module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutEModel
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.M12.Statements

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.EvenSporadicStandard.Fin76b CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.SmallOddCore.Native CFSG.GH74.M12 AutETable

@[expose] def pB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

@[expose] def sP : Equiv.Perm (Fin 12) := pB * bfF * bfF * pB

@[expose] def u1P : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [1, 2] * List.formPerm [5, 10] * List.formPerm [6, 9]

@[expose] def tbl14 (σ : Equiv.Perm (Fin 12)) : Table :=
  (Array.range 14).map fun i =>
    if h : i < 12 then ((σ ⟨i, h⟩ : Fin 12).val.toUInt32) else i.toUInt32

@[expose] def tauT : Table :=
  (Array.range 14).map fun i =>
    if i = 12 then (13 : UInt32) else if i = 13 then 12 else i.toUInt32

@[expose] def yGens : Array Table := #[tauT, tbl14 bfE, tbl14 bfN, tbl14 bfF, tbl14 sP]

@[expose] def tGens : Array Table := #[tauT, tbl14 bfE, tbl14 bfN, tbl14 bfF]

@[expose] def cT : Table := tbl14 bfJ

@[expose] def sT : Table := tbl14 sP

@[expose] def u1T : Table := tbl14 u1P

@[expose] def yE : Array Table × Array ℕ × Array ℕ := mulClosureS 14 14 yGens 2000

@[expose] def yEl : Array Table := yE.1

@[expose] def tE : Array Table × Array ℕ × Array ℕ := mulClosureS 14 14 tGens 1000

@[expose] def tEl : Array Table := tE.1

@[expose] def yMul (a b : ℕ) : ℕ := tblMulIdx 14 yEl a b

@[expose] def yM : Array (Array ℕ) := tab2 384 yMul

@[expose] def yGW : List ℕ × Array (Option (List ℕ)) := mkGens 384 yM

@[expose] def yGn : List ℕ := yGW.1

@[expose] def yW : Array (List ℕ) := yGW.2.map fun o => o.getD []

@[expose] def ixOf (T : Table) : ℕ :=
  ((List.range yEl.size).find? fun k => tblEq 14 yEl[k]! T).getD 0

@[expose] def ie : ℕ := ixOf tauT

@[expose] def ic : ℕ := ixOf cT

@[expose] def isx : ℕ := ixOf sT

@[expose] def iu : ℕ := ixOf (compT 14 tauT u1T)

@[expose] def epow (a : ℕ) : ℕ := if a % 2 == 0 then 0 else ie

@[expose] def cpow (a : ℕ) : ℕ := if a % 2 == 0 then 0 else ic

@[expose] def spow (b : ℕ) : ℕ :=
  if b % 3 == 0 then 0 else if b % 3 == 1 then isx else mt yM isx isx

@[expose] def epsI (k : ℕ) : ℕ := if ((yEl[k]!)[12]!).toNat == 13 then 1 else 0

@[expose] def lamI (k : ℕ) : ℕ :=
  let t := yEl[k]!
  (((List.range 4).flatMap fun i => (List.range 4).filter fun j => i < j && (t[j]!).toNat <
    (t[i]!).toNat).length) % 2

@[expose] def centralArr (α : ℕ) : Array ℕ :=
  (Array.range 384).map fun k => mt yM k (cpow (epsI k + α * lamI k))

@[expose] def tIdx : List ℕ := tEl.toList.map ixOf

@[expose] def badA (A : Array ℕ) : Bool :=
  let ta := tIdx.filter fun t => mt yM t iu == mt yM iu t
  let tb := tIdx.filter fun t => mt yM t (ix A iu) == mt yM iu t
  ta.length + tb.length == 128 &&
    ta.all (fun t => mt yM (mt yM t t) (mt yM t t) == 0) &&
    tb.all (fun t => mt yM (mt yM t (ix A t)) (mt yM t (ix A t)) == 0)

@[expose] def constrOK (A : Array ℕ) : Bool :=
  ix A ie == mt yM ie ic && ix A ic == ic && ix A isx == isx &&
    (List.range 384).all fun k => ix A (ix A k) == k

@[expose] def classOK (A : Array ℕ) : Bool :=
  !constrOK A || A == centralArr 0 || A == centralArr 1 || badA A

@[expose] def fIdx : Bool :=
  tblEq 14 yEl[ie]! tauT && tblEq 14 yEl[ic]! cT && tblEq 14 yEl[isx]! sT &&
    tblEq 14 yEl[iu]! (compT 14 tauT u1T)

@[expose] def fPerm : Bool := permOK 14 tauT && permOK 14 cT && permOK 14 sT && permOK 14 u1T

@[expose] def fOrd : Bool :=
  mt yM ie ie == 0 && mt yM ic ic == 0 && mt yM (mt yM isx isx) isx == 0

@[expose] def fCentral : Bool :=
  (List.range 384).all fun k => mt yM k ie == mt yM ie k && mt yM k ic == mt yM ic k

@[expose] def fT : Bool :=
  tIdx.length == 128 && tEl.toList.all (fun T => tblEq 14 yEl[ixOf T]! T) &&
    (tIdx.filter fun k => mt yM k k == 0).length == 56 &&
    tblEq 14 yEl[ixOf u1T]! u1T && tIdx.contains (ixOf u1T)

@[expose] def fCs : Bool :=
  (List.range 384).all fun k => mt yM k isx != mt yM isx k ||
    (List.range 2).any fun a => (List.range 2).any fun b => (List.range 3).any fun r =>
      mt yM (mt yM (epow a) (cpow b)) (spow r) == k

@[expose] def fInv : Bool :=
  (List.range 384).any fun k => mt yM k isx == mt yM (mt yM isx isx) k

@[expose] def fSyl : Bool :=
  (List.range 384).all fun k => !(mt yM (mt yM k k) k == 0 && k != 0) ||
    (List.range 384).any fun h =>
      mt yM h k == mt yM isx h || mt yM h k == mt yM (mt yM isx isx) h

@[expose] def factsOK : Bool := fIdx && fPerm && fOrd && fCentral && fT && fCs && fInv && fSyl

@[expose] def normOK : Bool :=
  (autArrs 384 yM yGn yW).all fun A =>
    !(ix A ie == mt yM ie ic && ix A ic == ic) ||
      (List.range 384).all fun w =>
        !(ix A w == w && (List.range 384).all fun k =>
            mt yM (ix A (ix A k)) w == mt yM w k) ||
          (List.range 384).any fun h =>
            mt yM h (ix A isx) == mt yM isx h && mt yM (mt yM h (ix A h)) w == 0

@[expose] def ptOK : Bool :=
  (autArrs 384 yM yGn yW).all fun A => !constrOK A || tIdx.all fun t => tIdx.contains (ix A t)

@[expose] def fT8 : Bool := tIdx.any fun t => mt yM (mt yM t t) (mt yM t t) != 0

@[expose] def yoshCheck : Bool :=
  enumOK 14 14 yGens yE 384 && tblClosedOK 14 yEl && enumOK 14 14 tGens tE 128 &&
    gensOk 384 yM yGn yW && factsOK && normOK && (autArrs 384 yM yGn yW).all classOK &&
    ptOK && fT8

end CFSG.EvenSporadicStandard.M12Std.Yosh
