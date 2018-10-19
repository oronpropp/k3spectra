/*
    Magma code related to the paper:
    [1] "Constructing explicit K3 spectra."
    Copyright (c) 2018 by Oron Y. Propp.
    You are welcome to use and/or modify this code under the terms of version 3
    of the GNU General Public License or any later version (but please cite the
    paper if you use this code in your research).

    This module implements algorithms detailed in [1] (originally owed to
    J. Stienstra and M. Artin) for computing formal group laws, p-series, and
    heights of formal Brauer groups of smooth quartics, double planes, and
    elliptic K3 surfaces. It also provides functions verifying the assertions
    made in [1, Section 9], where three height-3 K3 spectra are explicitly
    constructed. Specific references to the paper are given throughout in the
    comments.
*/

//////////////////////////////////////////////////
// General Functions for Stienstra's Algorithm
//////////////////////////////////////////////////

// Given a polynomial ring P, an element f of P, and a "coefficient counting"
// function C (which takes P, f, and a positive integer i, and returns an integer
// coerresponding to the coefficient of a certain monomial in a certain power of f;
// when f is a quartic equation in four variables, we will take C to be CQuartic(),
// and when f is a sextic equation in three variables, we will take C to be
// CDoublePlane()), this function computes a formal group law of the "formal Brauer
// group of f" with respect to C up to degree B (which is by default set to 10)
// using Stienstra's algorithm as in [1, Theorems 6.1 or 6.4] (note that f need not
// define a K3 surface for this function to run). If the parameter p is set to a
// prime, then this function also returns the p-series and height of the formal
// group law at the prime p (if the height is inconclusive from the computation up
// to degree B, then 0 is returned for the height). If the optional parameter ring
// is set to true, then the function also returns the power series ring in which
// the formal group law and p-series live.
StienstraFromEqn:=function(P,f,C:p:=0,B:=10,ring:=false)
    local A,K,R,l,log,exp,Q,S,e,fgl,pseries,T,Ap,hts,ht;
    assert (f in P) and (B gt 0);
    A:=BaseRing(P);
    assert (p eq 0 or IsPrime(p)) and not IsUnit(A!p);
    K:=FieldOfFractions(A);
    R:=PowerSeriesRing(K);
    l:=[K!C(P,f,i)/i:i in [1..B]];
    log:=elt<R|1,l>;
    exp:=Reverse(log);
    Q<x,y>:=PolynomialRing(K,2);
    Q:=quo<Q|MonomialsOfDegree(Q,B+1)>;
    S:=PolynomialRing(Q);
    e:=&+[Coefficient(exp,i)*S.1^i:i in [1..B]];
    fgl:=Evaluate(e,Evaluate(log,Q.1)+Evaluate(log,Q.2));
    if p eq 0 then if ring then return fgl,R; else return fgl; end if; end if;
    pseries:=Composition(exp,p*log);
    Ap:=quo<A|p>;
    hts:=[i:i in [1..Floor(Log(p,B))]|IsInvertible(Ap!Coefficient(pseries,p^i))];
    if IsEmpty(hts) then ht:=0; else ht:=hts[1]; end if;
    if ring then return fgl,pseries,ht,R; else return fgl,pseries,ht; end if;
end function;

// Given a polynomial ring P, an element f of P, a "coefficient counting" function
// C (as in StienstraFromEqn()), and a prime p, this function attempts to compute
// the height of the "formal Brauer group of f" at the prime p by successively
// computing the p-series up to degree p^0, p^1, ... , p^B using the same
// algorithm as in StienstraFromEqn() until a coefficient that is invertible modulo
// p is found (B is by default set to 3). Note that, for efficiency, this function
// only computes the p-power-degree terms of the formal group law that are needed
// for computing the height, rather than the entire formal group law as in
// StienstraFromEqn().
// If the parameter v is set to 0 (its default), then this function returns the
// height of the formal Brauer group (a positive integer, or 0 if the height is
// inconclusive); if v is set to 1, then it returns the coefficients v_i of the
// degree-p^i terms in the p-series as a list, where i ranges from 1 to B; and if
// v is set to 2, then it returns the v_i's as a list, with each v_i reduced modulo
// v_0, v_1, ..., v_{i-1} (this generally speeds up computations).
// If the optional parameter verbose is set to true, then this function returns the
// (incomplete) "formal group law" and "p-series" that it computes, and the power
// series ring in which the formal group law and p-series live, along with its
// usual output corresponding to the choice of v.
StienstraHeightFromEqn:=function(P,f,p,C:B:=3,v:=0,verbose:=false)
    local A,Ap,ht,l,V,K,R,b,ls,log,exp,Q,S,e,fgl,pseries,ret,w;
    A:=BaseRing(P);
    Ap:=quo<A|p>;
    assert (f in P) and IsPrime(p) and (B gt 0) and not IsUnit(A!p);
    ht:=0;
    l:=[];
    if v eq 2 then V:=[]; end if;
    K:=FieldOfFractions(A);
    R:=PowerSeriesRing(K);
    while ht le B do
	if v eq 1 and not ht eq B then ht:=ht+1; continue; end if;
	b:=K!C(P,f,p^ht);
        l:=Append(l,b/p^ht);
        ls:=[K!0:i in [1..p^ht]];
        for i in [0..ht] do ls[p^i]:=l[i+1]; end for;
        log:=elt<R|1,ls>;
        exp:=Reverse(log);
        Q:=PolynomialRing(K,2);
        Q:=quo<Q|MonomialsOfDegree(Q,p^ht+1)>;
        S:=PolynomialRing(Q);
        e:=&+[Coefficient(exp,i)*S.1^i:i in [1..p^ht]];
        fgl:=Evaluate(e,Evaluate(log,Q.1)+Evaluate(log,Q.2));
        pseries:=Composition(exp,p*log);
        if v eq 0 then
	    if IsUnit(Ap!Coefficient(pseries,p^ht)) then
	        ret:=ht;
                break;
	    elif ht eq B then
	        ret:=0;
                break;
            end if;
        end if;
        if v eq 1 and ht eq B then
	    ret:=[Coefficient(pseries,p^i):i in [0..B]];
            break;
        end if;
        if v eq 2 then
	    w:=A!Coefficient(pseries,p^ht);
            V:=Append(V,w);
            A:=quo<BaseRing(P)|V>;
            if ht eq B then ret:=V; break; end if;
        end if;
        ht:=ht+1;
    end while;
    if verbose then return ret,fgl,pseries,R; else return ret; end if;
end function;

// Given a homogeneous degree-d element f of a (multivariate) polynomial ring P,
// returns the coefficients of f as a list in Magma's default (lexicographic)
// monomial ordering.
EqnToCoeffs:=function(P,f,d)
    assert f eq HomogeneousComponent(f,d);
    return [MonomialCoefficient(f,m):m in MonomialsOfDegree(P,d)];
end function;

// Given a list c of coefficients lying in a ring A, of length ((d+n-1) choose d),
// returns a polynomial ring with n variables and coefficients in A, along with a
// homogeneous degree-d element of P with coefficients given by c (with respect to
// Magma's default monomial ordering).
CoeffsToEqn:=function(c,n,d:A:=Integers())
    local P,m,f;
    P:=PolynomialRing(A,n);
    m:=MonomialsOfDegree(P,d);
    assert #c eq #m and c subset A;
    f:=&+{c[i]*m[i]:i in [1..#m]};
    return P,f;
end function;

//////////////////////////////////////////////////
// Quartic Surfaces
//////////////////////////////////////////////////

// Given a homogeneous quartic equation f in four variables and a prime p, return
// true if and only if the quartic surface in P^3 is smooth over the finite field
// with p elements (i.e., defines a K3 surface over F_p).
IsSmoothQuartic:=function(f,p)
    local X;
    assert IsPrime(p) and f eq HomogeneousComponent(f,4);
    X:=Scheme(ProjectiveSpace(FiniteField(p),3),f);
    return IsNonsingular(X);
end function;

// The coefficient counting function used in Stienstra's algorithm for computing
// the formal Brauer group of a smooth quartic. Takes a polynomial ring P in four
// variables, an element f of P, and a positive integer i; returns the coefficient
// of (wxyz)^(i-1) in f^(i-1), where w,x,y,z are the variables of P.
CQuartic:=function(P,f,i);
    assert Rank(P) eq 4 and f in P and i ge 1;
    return MonomialCoefficient(f^(i-1),(P.1*P.2*P.3*P.4)^(i-1));
end function;

// Given a polynomial ring P in four variables and a homogeneous degree-4 element
// f of P, returns a formal group law of the formal Brauer group of the quartic
// surface that f defines, computed using Stienstra's algorithm as in [1, Theorem 6.1].
// The optional parameters p, B, and ring are as in StienstraFromEqn().
// For example, one might run this function on the Fermat quartic (see
// [1, Example 6.3]) by setting:
// > P<w,x,y,z>:=PolynomialRing(Integers(),4);
// > f:=w^4+x^4+y^4+z^4;
StienstraQuarticFromEqn:=function(P,f:p:=0,B:=10,ring:=false)
    return StienstraFromEqn(P,f,CQuartic:p:=p,B:=B,ring:=ring);
end function;

// Given c and A as in CoeffsToEqn() for n=d=4, this function converts c to an
// equation defining a quartic surface using CoeffstoEqn(), and then runs
// StienstraQuarticFromEqn() on this equation (where the parameters p, B, and ring are
// as before).
StienstraQuarticFromCoeffs:=function(c:A:=Integers(),p:=0,B:=10,ring:=false)
    local P,f; 
    P,f:=CoeffsToEqn(c,4,4:A:=A);
    return StienstraQuarticFromEqn(P,f:p:=p,B:=B,ring:=ring);
end function;

// Given P, f, and p as in StienstraQuarticFromEqn() (though here p is a required
// parameter), compute the height of the formal Brauer group of the quartic
// surface defined by f at the prime p using Stienstra's algorithm as in
// [1, Thm. 6.1]. The optional parameters B, v, and verbose are as in
// StienstraHeightFromEqn().
StienstraQuarticHeightFromEqn:=function(P,f,p:B:=3,v:=0,verbose:=false)
  return StienstraHeightFromEqn(P,f,p,CQuartic:B:=B,v:=v,verbose:=verbose);
end function;

// Given c and A as in CoeffsToEqn() for n=d=4, this function converts c to an
// equation defining a quartic surface using CoeffstoEqn(), and then runs
// StienstraQuarticHeightFromEqn() on this equation (where the parameters A, B, v,
// and verbose are as before).
StienstraQuarticHeightFromCoeffs:=function(c,p:A:=Integers(),B:=3,v:=0,verbose:=false)
    local P,f;
    P,f:=CoeffsToEqn(c,4,4:A:=A);
    return StienstraQuarticHeightFromEqn(P,f,p:B:=B,v:=v,verbose:=verbose);
end function;

// This function verifies the computations in [1, Example 9.1], where a height-3
// K3 spectrum Q arising from a family of quartic surfaces is explicitly constructed.
VerifyK3SpectrumQ:=function()
    R<a,b>:=PolynomialRing(Integers(),2);
    P<w,x,y,z>:=PolynomialRing(R,4);
    f:=w^4+w^2*x*z+w*x*y^2+w*z^3+x^4+y^4+a*x*z^3+b*x*y^2*z;
    return StienstraQuarticHeightFromEqn(P,f,3:v:=2);
end function;

//////////////////////////////////////////////////
// Sextic Double Planes
//////////////////////////////////////////////////

// Given a homogeneous sextic equation f in three variables and a prime p, return
// true if and only if the double plane it defines (i.e., w^2=f) in a weighted P^3
// is smooth over the finite field with p elements (i.e., defines a K3 surface over
// F_p).
IsSmoothDoublePlane:=function(f,p)
    local F,C,P,g,X;
    assert IsPrime(p) and f eq HomogeneousComponent(f,6);
    F:=FiniteField(p);
    C:=Scheme(ProjectiveSpace(F,2),f);
    P:=PolynomialRing(F,[1,1,1,3]);
    g:=P.4^2-Evaluate(f,[P.1,P.2,P.3]);
    X:=Scheme(ProjectiveSpace(P),g);
    return IsNonsingular(C) and IsNonsingular(X);
end function;

// The coefficient counting function used in Stienstra's algorithm for computing
// the formal Brauer group of a (sextic) double plane. Takes a polynomial ring P
// in three variables, an element f of P, and a positive integer i; returns 0 if
// i is even and the coefficient of (xyz)^(i-1) in f^((i-1)/2) if i is odd, where
// x,y,z are the variables of P.
CDoublePlane:=function(P,f,i);
    assert Rank(P) eq 3 and f in P and i ge 1;
    if IsEven(i) then
        return 0;
    else
        return MonomialCoefficient(f^ExactQuotient(i-1,2),(P.1*P.2*P.3)^(i-1));
    end if;
end function;

// Given a polynomial ring P in three variables and a homogeneous degree-6 element
// f of P, returns a formal group law of the formal Brauer group of the double plane
// that f defines (i.e., w^2=f), computed using Stienstra's algorithm as in
// [1, Thm. 6.4]. The optional parameters p, B, and ring are as in StienstraFromEqn().
// For example, one might run this function on the following double plane
// (see [1, Example 6.5]):
// > P<x,y,z>:=PolynomialRing(Integers(),3);
// > f:=x^6+y^6+z^6;
StienstraDoublePlaneFromEqn:=function(P,f:p:=0,B:=10,ring:=false)
    return StienstraFromEqn(P,f,CDoublePlane:p:=p,B:=B,ring:=ring);
end function;

// Given c and A as in CoeffsToEqn() for n=3 and d=6, this function converts c to an
// equation defining a double plane using CoeffstoEqn(), and then runs
// StienstraDoublePlaneFromEqn() on this equation (where the parameters p, B, and
// ring are as before).
StienstraDoublePlaneFromCoeffs:=function(c:A:=Integers(),p:=0,B:=10,ring:=false)
    local P,f; 
    P,f:=CoeffsToEqn(c,3,6:A:=A);
    return StienstraDoublePlaneFromEqn(P,f:p:=p,B:=B,ring:=ring);
end function;

// Given P, f, and p as in StienstraDoublePlaneFromEqn() (though here p is a required
// parameter), compute the height of the formal Brauer group of the double plane
// defined by f at the prime p using Stienstra's algorithm as in [1, Thm. 6.4]. The
// optional parameters B, v, and verbose are as in StienstraHeightFromEqn().
StienstraDoublePlaneHeightFromEqn:=function(P,f,p:B:=3,v:=0,verbose:=false)
  return StienstraHeightFromEqn(P,f,p,CDoublePlane:B:=B,v:=v,verbose:=verbose);
end function;

// Given c and A as in CoeffsToEqn() for n=3 and d=6, this function converts c to an
// equation defining a quartic surface using CoeffstoEqn(), and then runs
// StienstraDoublePlaneHeightFromEqn() on this equation (where the parameters A, B,
// v, and verbose are as before).
StienstraDoublePlaneHeightFromCoeffs:=function(c,p:A:=Integers(),B:=3,v:=0,
					       verbose:=false)
    local P,f;
    P,f:=CoeffsToEqn(c,3,6:A:=A);
    return StienstraDoublePlaneHeightFromEqn(P,f,p:B:=B,v:=v,verbose:=verbose);
end function;

// This function verifies the computations in [1, Example 9.3], where a height-3
// K3 spectrum D arising from a family of double planes is explicitly constructed.
VerifyK3SpectrumD:=function()
    local R,P,f;
    R<a,b>:=PolynomialRing(Integers(),2);
    P<x,y,z>:=PolynomialRing(R,3);
    f:=-x^6+x^2*y^4+x*y^5+y*z^5+z^6+a*x*y^2*z^3+b*x^2*y^2*z^2;
    return StienstraDoublePlaneHeightFromEqn(P,f,3:v:=2);
end function;

//////////////////////////////////////////////////
// Elliptic K3 Surfaces
//////////////////////////////////////////////////

// Given a coefficient ring R (which should be of the form A[t] or A(t) for some
// base ring A) and a list c=[a1,a2,a3,a4,a6] of five elements of R, this function
// returns coefficients for a minimal model of the elliptic K3 surface (over P^1)
// defined by the Weierstrass equation y^2+a1*x*y+a3*y=x^3+a2*x^2+a4*x+a6 over the
// ring obtained from R by replacing the base ring of R with its field of fractions,
// which is also returned.
MinimalModelCoeffs:=function(R,c)
    local S,K,cK,M;
    S:=ChangeRing(R,FieldOfFractions(BaseRing(R)));
    K:=FieldOfFractions(S);
    cK:=[K!a:a in c];
    M:=MinimalModel(EllipticCurve(cK));
    return [S!a:a in Coefficients(M)],S;
end function;

// Given R and c as for MinimalModelCoeffs(), return true if and only if the ai
// satisfy the conditions deg ai \le 2i for each i and deg ai(t) > i for some i.
// (If the ai satisfy these conditions and define a minimal model, then the minimal
// desingularization of the associated surface is an (elliptic) K3 surface, see
// [1, Section 2].)
CoeffsSatisfyK3Condition:=function(R,c)
    local C;
    C:=Insert(c,5,0);
    return &and[Degree(C[i]) le 2*i:i in [1..#C]] and
           &or[Degree(C[i]) gt i:i in [1..#C]];
end function;

// Given a quotient h of a univariate polynomial by a monomial,
// compute the "positive coboundary" B_+ as in Step (3) of [1, Theorem 7.1], i.e.,
// the sum of all monomials in h of degree greater than -1.
PosCobound:=function(h)
    local S;
    assert #Terms(Denominator(h)) eq 1;
    S:=[a/Denominator(h):a in Terms(Numerator(h))|
                         Degree(a)-Degree(Denominator(h)) gt -1];
    if S eq [] then return 0; else return &+S; end if;
end function;

// Given h as in PosCobound(), compute the "negative coboundary" B_- as in Step
// (3) of [1, Theorem 7.1], i.e., the sum of all monomials in h of degree less
// than -1.
NegCobound:=function(h)
    local S;
    assert #Terms(Denominator(h)) eq 1;
    S:=[a/Denominator(h):a in Terms(Numerator(h))|
                         Degree(a)-Degree(Denominator(h)) lt -1];
    if S eq [] then return 0; else return &+S; end if;
end function;

// Given h as in PosCobound(), returns the sum of all terms of h which are not in
// degree -1.
NotDegMinusOne:=function(h)
    local S;
    assert #Terms(Denominator(h)) eq 1;
    S:=[a/Denominator(h):a in Terms(Numerator(h))|
                         not Degree(a)-Degree(Denominator(h)) eq -1];
    if S eq [] then return 0; else return &+S; end if;
end function;

// Given a power series f whose coefficients are quotients h as in
// NotDegMinusOne(), returns true if and only if all coefficients of f are
// homogeneous of degree -1.
AllDegMinusOne:=function(f)
    return &and[NotDegMinusOne(Coefficients(f)[i]) eq 0:i in [1..#Monomials(f)]];
end function;

// Given a bivariate polynomial ring P, an element f of P, and a positive integer
// p, compute the p-series of f, i.e., the polynomial given by p applications
// f(x,f(x,f(x,...))), where x is the first variable of P.
PSeries:=function(P,f,p)
    assert Rank(P) eq 2 and f in P and p ge 1;
    if p eq 1 then return P.1;
    else return Evaluate(f,[P.1,$$(P,f,p-1)]); end if;
end function;

// Given a coefficient ring R (which should be of the form A[t] or A(t) for some
// base ring A) and a list c=[a1,a2,a3,a4,a6] of five elements of R, this function
// computes a formal group law of the formal Brauer group of the elliptic K3 surface
// (over P^1) defined by the Weierstrass equation y^2+a1*x*y+a3*y=x^3+a2*x^2+a4*x+a6,
// using Artin's algorithm as in [1, Theorem 7.1]. Note that c need not define a K3
// surface or be minimal for this function to run (though it should be for correct
// output). The optional parameters p, B, and ring are exactly as for
// StienstraFromEqn() (though specifying ring=true now returns a polynomial ring).
// For example, one might run this function on the Weierstrass model fo the Fermat
// quartic obtained in [1, Example 2.4] (see also [1, Example 7.3]) by setting:
// > R<t>:=PolynomialRing(Integers());
// > c:=[0,3*t^2,0,0,4*t^10+3*t^6+4*t^2];
ArtinEllipticFromCoeffs:=function(R,c:p:=0,B:=10,ring:=false)
    local A,Ap,K,cK,P,Q,g,f,pos,neg,b,fgl,pseries,hts,ht;
    assert c subset R and (p eq 0 or IsPrime(p)) and (B gt 0) and not IsUnit(R!p);
    A:=BaseRing(R);
    if A!p eq 0 then Ap:=A; else Ap:=quo<A|p>; end if;
    K:=FieldOfFractions(R);
    cK:=[K!a:a in c];
    P<x,y>:=PolynomialRing(K,2);
    Q:=quo<P|MonomialsOfDegree(P,B+1)>;
    g:=FormalGroupLaw(EllipticCurve(cK),B);
    f:=Evaluate(g,[Q.1/K.1,Q.2/K.1]);
    f:=Q!f;
    while not AllDegMinusOne(f) do
        pos:=&+[-PosCobound(Coefficients(f)[i])*Monomials(f)[i]:
		i in [1..#Monomials(f)]];
        neg:=&+[-NegCobound(Coefficients(f)[i])*Monomials(f)[i]:
		i in [1..#Monomials(f)]];
        b:=Evaluate(g,[pos,neg]);
        f:=Evaluate(g,[f,b]);
    end while;
    fgl:=K.1*f;
    if p eq 0 then if ring then return fgl,P; else return fgl; end if; end if;
    pseries:=PSeries(Q,fgl,p);
    hts:=[i:i in [1..Floor(Log(p,B))]|IsInvertible(Ap!Coefficient(pseries,P.1,p^i))];
    if IsEmpty(hts) then ht:=0; else ht:=hts[1]; end if;
    if ring then return fgl,pseries,ht,P; else return fgl,pseries,ht; end if;
end function;

// Given R, c, and p as for ArtinEllipticFromCoeffs(), this function attempts to
// compute the height of the elliptic K3 surface defined by c using the exact same
// method as in StienstraHeightFromEqn(). The optional parameters B, v, and verbose
// are just as in StienstraHeightFromEqn().
ArtinEllipticHeightFromCoeffs:=function(R,c,p:B:=3,v:=0,verbose:=false)
  local A,Ap,K,cK,ht,V,fgl,pseries,f,P,ret;
    assert c subset R and IsPrime(p) and (B gt 0) and not IsUnit(R!p);
    A:=BaseRing(R);
    if A!p eq 0 then Ap:=A; else Ap:=quo<A|p>; end if;
    ht:=1;
    if v eq 2 then V:=[]; end if;
    while ht le B do
	if v eq 1 and not ht eq B then ht:=ht+1; continue; end if;
        fgl,pseries,h,P:=ArtinEllipticFromCoeffs(R,c:p:=p,B:=p^ht,ring:=true);
        if v eq 0 then
            if IsInvertible(Ap!Coefficient(pseries,P.1,p^ht)) then
                ret:=ht;
                break;
            elif ht eq B then
                ret:=0;
                break;
            end if;
        end if;
        if v eq 1 and ht eq B then
            ret:=[Coefficient(pseries,P.1,p^i):i in [0..B]];
            break;
        end if;
        if v eq 2 then
   	    w:=A!Coefficient(pseries,P.1,p^ht);
            V:=Append(V,w);
            A:=quo<BaseRing(R)|V>;
            if ht eq B then ret:=V; break; end if;
        end if;
        ht:=ht+1;
    end while;
    if verbose then return ret,fgl,pseries,P; else return ret; end if;
end function;

// This function verifies the computations in [1, Example 9.4], where a height-3
// K3 spectrum E arising from a family of Elliptic K3 surfaces is explicitly
// constructed.
VerifyK3SpectrumE:=function()
    local R,A,c,A3,c3;
    R<a,b>:=PolynomialRing(Integers(3),2);
    A<t>:=PolynomialRing(R);
    c:=[a+b*t,1+t,t^2,1+t^4+t^8,t^7+t^8];
    A3<s>:=PolynomialRing(Integers(3));
    c3:=[0,1+s,s^2,1+s^4+s^8,s^7+s^8];
    return ArtinEllipticHeightFromCoeffs(A,c,3:B:=2,v:=1),
           ArtinEllipticHeightFromCoeffs(A3,c3,3:v:=1);
end function;
