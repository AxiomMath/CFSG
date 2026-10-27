module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import Certificates.Data.CFSGNative.MonsterB.CosetEnum

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7

@[expose] def bitsOf (A : ℕ) : List ℕ := (List.range 12).filter fun j => A.testBit j

@[expose] def prodP (f : ℕ → Model.Pauli) (l : List ℕ) : Model.Pauli :=
  l.foldl (fun P j => Model.Pauli.mul P (f j)) (false, 0, 0)

@[expose] def basisT (j : ℕ) : Model.Pauli := (false, 2 ^ j, 0)

@[expose] def basisD (j : ℕ) : Model.Pauli := (false, 0, 2 ^ j)

@[expose] def decompOK (_ : Unit := ()) : Bool :=
  (List.range 4096).all (fun A => prodP basisT (bitsOf A) == (false, A, 0)) &&
    (List.range 4096).all fun D => prodP basisD (bitsOf D) == (false, 0, D)

@[expose] def tblT (imgT : Array Model.Pauli) : Array Model.Pauli :=
  (Array.range 4096).map fun A => prodP (fun j => imgT[j]!) (bitsOf A)

@[expose] def tblD (imgD : Array Model.Pauli) : Array Model.Pauli :=
  (Array.range 4096).map fun D => prodP (fun j => imgD[j]!) (bitsOf D)

@[expose] def validB (p : Model.Pauli) : Bool := decide (p.2.1 < 4096) && decide (p.2.2 < 4096)

@[expose] def ebarPairs (w : List Native.Gen) (imgT imgD : Array Model.Pauli) :
    List (List Native.Gen × List Native.Gen) :=
  ((List.range 12).map fun j => (Native.Gen.rho (basisT j) :: w, w ++ [Native.Gen.rho imgT[j]!])) ++
    (List.range 12).map fun j => (Native.Gen.rho (basisD j) :: w, w ++ [Native.Gen.rho imgD[j]!])

@[expose] def ebarFixTest (tA tB : Array Model.Pauli) (n : ℕ) : Bool :=
  let p := Rep4371.Native.Pauli.mul tA[n % 2 ^ 12]! tB[n / 2 ^ 12 % 2 ^ 12]!
  (p.2.1 == n % 2 ^ 12) && (p.2.2 == n / 2 ^ 12 % 2 ^ 12) && !p.1

@[expose] def ebarFixCount (tA tB : Array Model.Pauli) : ℕ :=
  Rep4371.Native.CosetEnum.countBelow (ebarFixTest tA tB) (2 ^ 24) 0

@[expose] def ebarCheck (w : List Native.Gen) (imgT imgD : Array Model.Pauli) (bound : ℕ) : Bool :=
  decide (imgT.size = 12) && decide (imgD.size = 12) && imgT.all validB && imgD.all validB &&
    decompOK () && agreeAll (ebarPairs w imgT imgD) &&
    decide (ebarFixCount (tblT imgT) (tblD imgD) ≤ bound)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
