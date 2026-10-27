module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PThData
public import CFSG.Certificates.Kernel.Co1BMulSound
public import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound

public section

namespace CFSG.KC.Ops2

open CFSG.SectionRank.Native CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

variable {M V : Type} (O : Ops M V) (X : M)

theorem pow_one' : O.pow X 1 = X := by
  rw [Ops.pow]
  simp

theorem pow_two' : O.pow X 2 = O.mul X X := by
  rw [Ops.pow]
  simp [pow_one']

theorem pow_three' : O.pow X 3 = O.mul X (O.mul X X) := by
  rw [Ops.pow]
  simp [pow_one']

theorem pow_four' : O.pow X 4 = O.mul (O.mul X X) (O.mul X X) := by
  rw [Ops.pow]
  simp [pow_two']

theorem pow_eight' :
    O.pow X 8 = O.mul (O.mul (O.mul X X) (O.mul X X)) (O.mul (O.mul X X) (O.mul X X)) := by
  rw [Ops.pow]
  simp [pow_four']

theorem init12 [Inhabited M] (A B : M) : O.initRegs A B 12 =
    #[A, B, O.one, O.one, O.one, O.one, O.one, O.one, O.one, O.one, O.one, O.one] := by
  apply Array.ext
  · simp [Ops.initRegs]
  · intro i h1 _
    have hi : i < 12 := by simpa [Ops.initRegs] using h1
    simp only [Ops.initRegs, Array.getElem_ofFn]
    interval_cases i <;> rfl

theorem run11 [Inhabited M] (A B : M) :
    (O.run thOrd8Data.prog (O.initRegs A B thOrd8Data.nregs))[11]! =
      O.pow (O.mul (O.mul (O.mul (O.mul (O.mul (O.mul (O.mul A B) (O.mul A B)) (O.mul A B))
        (O.mul A (O.pow B 2))) (O.mul A B)) (O.mul A (O.pow B 2))) (O.mul A (O.pow B 2))) 3 := by
  change (O.run thOrd8Data.prog (O.initRegs A B 12))[11]! = _
  rw [init12]
  simp [Ops.run, Ops.step, thOrd8Data]

theorem unpackR_eqP (d X : Nat) : unpackR d X = CFSG.KS.SporSch.PF2.unpackP d X := by
  unfold unpackR CFSG.KS.SporSch.PF2.unpackP
  congr 1
  funext i
  rw [CFSG.KC.F2W.rowF_eq]

theorem mul_unpack (d A B : Nat) :
    (ops2 d).mul (unpackR d A) (unpackR d B) = unpackR d (mulF d A B) :=
  CFSG.KC.F2W.mulRows_unpackR d A B

theorem one_unpack (d : Nat) : (ops2 d).one = unpackR d (idF d) := by
  rw [unpackR_eqP, CFSG.KS.SporSch.PF2.idF_unpack]
  rfl

theorem eq_unpack {d A B : Nat} (h : Nat.beq A B = true) :
    (ops2 d).eq (unpackR d A) (unpackR d B) = true := by
  rw [Nat.eq_of_beq_eq_true h]
  exact beq_self_eq_true _

theorem vne_unpack (d k P : Nat) :
    (ops2 d).vne ((ops2 d).vmul ((ops2 d).unit k) (unpackR d P)) ((ops2 d).unit k) =
      (List.range d).any fun j => (vmF d P (1 <<< k)).testBit j != (1 <<< k : Nat).testBit j := by
  change ((List.range d).any fun j =>
    (vecMulN d (unpackR d P) (1 <<< k)).testBit j != (1 <<< k : Nat).testBit j) = _
  rw [CFSG.KC.F2W.vecMulN_unpackR]

end CFSG.KC.Ops2

end
