#####
with(ListTools):
with(Groebner):





#####
Binomials := module()
description "Some functions for Binomial Ideals";
#Authors: Alexandru Iosif and Hamid Rahkooy
option package;
#with(ListTools):
#with(Groebner):
export isBinomial, isBinomialGroebner, coefficientsMatrix, monomialCoefficient;





#####Main Functions:

monomialCoefficient := proc(f::polynom,variablesf::list, m::monomial)
# This procedure takes a polynomial f and it returns the coefficient of the monomial m in with respect to the variables variablesf
local monomialsf, TermsList, termsf, coefficientsf, fd, kk, indexm, positionm;
if m = 1 then return (tcoeff(f,variablesf)); end if;
fd := collect(f,variablesf,'distributed');
TermsList := e->`if`(type(e,`+`), convert(e,list), [e]); #taken from Internet
termsf := TermsList(fd);
termsf := collect(termsf,variablesf);
coefficientsf := seq(coeffs(termsf[kk],variablesf),kk=1..(nops(termsf)));
monomialsf := termsf/~[coefficientsf];
positionm := member(m,monomialsf,'indexm');
if (positionm = true) then coeffs(termsf[indexm],variablesf); else 0; end if;
end proc;

coefficientsMatrix := proc(F::list,variablesF::list)
#Input: a list of polynomials
#Output: a matrix C of coefficients and a list m of monomials such that
local vectorF, Fd, TermsList, termsF, kkk, coefficientsF, monomialsF, kk, nrElemsTermsF, nrElemsF;
Fd := collect(F,variablesF,distributed);
TermsList := e->`if`(type(e,`+`), convert(e,list), [e]); #taken from Internet
nrElemsF := nops(F);
termsF := [seq(TermsList(Fd[kkk]),kkk=1..nrElemsF)];
termsF := op~(termsF);
termsF := collect(termsF,variablesF);
nrElemsTermsF := nops(termsF);
coefficientsF := seq(coeffs(termsF[kkk],variablesF),kkk=1..nrElemsTermsF);
monomialsF := termsF/~coefficientsF;convert(%,set);
monomialsF := convert(%,list);
coefficientsF :=
[seq(
[seq(
monomialCoefficient(F[kkk],variablesF,monomialsF[kk])
,kk=1..nops(monomialsF))]
,kkk=1..nops(F))];
return (Matrix(coefficientsF), convert(monomialsF,Vector));
end proc;

isBinomial := proc(F::list,variablesF::list)
description "tests binomiality";
# --Checks binomiality of an ideal (here binomial means no monomials are in the ideal)
local isB, kk,A,M,rowDimA,maxNrRowElementsA,minNrRowElementsA;
(A,M) := coefficientsMatrix (F,variablesF);
A := LinearAlgebra[ReducedRowEchelonForm](A);
rowDimA := LinearAlgebra[RowDimension](A);
if (rowDimA = 1) then maxNrRowElementsA := ArrayNumElems(Array(A),NonZero);
else
maxNrRowElementsA := max(seq(ArrayNumElems(Array(A[kk]),NonZero),kk=1..rowDimA));
minNrRowElementsA := min(seq(ArrayNumElems(Array(A[kk]),NonZero),kk=1..rowDimA));
end if;
if maxNrRowElementsA < 2 or minNrRowElementsA = 1 then return (false); end if;
if maxNrRowElementsA = 2 and minNrRowElementsA = 2 then return (true); end if;
isB := isBinomialGroebnerFree(F,variablesF)[1];
if isB then return isB; end if;
if (F = Homogenize(F,ttt,variablesF)) then return isB; end if;
if not isB then
print("Gröbner free method failed.");
end if;
return 0;
end proc;

isBinomialGroebner := proc(F::list,variablesF::list)
#test binomiality using a Groebner Basis
local B, numTermsB, maxNumTermsB, minNumTermsB;
B := Basis(F,tdeg(op(variablesF)));
numTermsB := nops~(B);
maxNumTermsB := max(numTermsB);
minNumTermsB := min(numTermsB);
if maxNumTermsB = 2 and minNumTermsB = 2 then true else false end if
end proc;





#####Local Functions:

local isBinomialGroebnerFree;
isBinomialGroebnerFree := proc(F::list,variablesF::list)
description "test for Binomiality with Conradi-Kahle algorithm";
#Detecting Binomiality using Groebner Free method.
#Implements Algorithm 3.3 in [CK15] and part of Recipe 4.5 in [CK15]
local needToDehom, FF, variablesFF, ttt, isB, bins;
needToDehom := false;
FF := F;
variablesFF := variablesF;
if not (FF = Homogenize(FF,ttt,variablesF)) then
# homogenize the generators of the ideal as in Recipe 4.5 in [CK15]
# The last variable is the homogenization variable
FF := Homogenize(FF,ttt,variablesF);
needToDehom := true;
variablesFF := [op(variablesF),ttt];
end if;
(isB, bins) := CKbasisRecursion (FF,variablesFF);
if not isB then return (false, {}); end if;
if needToDehom then
bins := subs(ttt = 1, bins);
end if;
return (true,bins);
end proc;

local minDegreeElements;
minDegreeElements := proc(F::list,variablesF::list)
local kkkk, degreesList,  minDegree, elementsMinDegree, indicesMinDegree;
degreesList := [seq(degree(F[kkkk],variablesF),kkkk=1..nops(F))];
minDegree := min(degreesList);
indicesMinDegree := SearchAll(minDegree, degreesList);
indicesMinDegree := [SearchAll(minDegree, degreesList)];
elementsMinDegree := [seq(F[kkkk], kkkk in indicesMinDegree)];
return elementsMinDegree;
end proc;

local CKbasisRecursion;
CKbasisRecursion := proc(F::list,variablesF::list)
# Taken and adapted to Maple from the Macaulay2 package Binomials, by Thomas Kahle
#Input: A set of standard-graded polynomials,
#Output: (Boolean, a matrix of binomials)
#Algorithm 3.3. in [CK15]
local FF, Fmin, A, M, setFF, setFmin, diffFFmin, maxNrRowElementsA, k, B, setAM, GB, minNrRowElementsA;
if nops (F) = 0 then return (true, Matrix(0)); end if;
B:={};
Fmin:={};
FF := F; # MakeUnique(F);
while (nops(FF) > 0) do
Fmin := minDegreeElements(FF,variablesF);
(A,M) := coefficientsMatrix (Fmin,variablesF);
A := LinearAlgebra[ReducedRowEchelonForm](A);
local rowDimA; rowDimA := LinearAlgebra[RowDimension](A);
if (rowDimA = 1) then maxNrRowElementsA := ArrayNumElems(Array(A),NonZero);
else
maxNrRowElementsA := max(seq(ArrayNumElems(Array(A[k]),NonZero),k=1..rowDimA));
minNrRowElementsA := min(seq(ArrayNumElems(Array(A[k]),NonZero),k=1..rowDimA));
end if;
if maxNrRowElementsA > 2 or minNrRowElementsA = 1 then return (false, {}); end if;
setAM := convert(op~([entries(LinearAlgebra[Multiply](A,M))]),set);
B := B union setAM;
B := remove(member, B, [0]);
setFF := convert(FF,set);
setFmin := convert(Fmin,set);
diffFFmin := setFF minus setFmin;
FF := (convert(FF,set)) minus (convert(Fmin,set));
GB := Basis(Fmin,tdeg(op(variablesF)));
convert([seq( NormalForm(FF[k],GB,tdeg(op(variablesF))), k=1..(nops(FF)) )],set); FF:= convert(%,list);
FF := remove(member, FF, [0]);
if nops(FF) = 0 then return (true, B); end if; ##this avoids the next step in case F is empty
#Check again if the reduction made things zero
if nops(FF) = 0 then return [true, B]; end if; ##this avoids the next step in case F is empty
end do;
# #    -- We should never reach this:
print ("You have found a bug in the binomials package.  Please report.");
return   (0,Matrix[0]);
end proc;





end module; # Binomials





#####Bibliography:
#[CK15] Conradi, Kahle. Detecting Binomiality, 2015.
