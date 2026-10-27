module

public import Certificates.Data.Kernel.M1F2
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersThData
import all CFSG.Certificates.Kernel.LocalCompCubSound
import CFSG.Certificates.Kernel.Co1BMulSound
public import Certificates.Data.CFSGNative.SectionRank.F2

public section

namespace CFSG.KC.M1F2

open CFSG.EvenSmallLie.CatalogOrders CFSG.SectionRank.Native CFSG.KC.Co1F2 CFSG.KC.F2W
  CFSG.KC.LocalComp.Cub CFSG.Sporadic.SmallF2.Native

private theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

private theorem andB_true {a b : Bool} (h : CFSG.KLie.CT.andB a b = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [CFSG.KLie.CT.andB]

private theorem unpackR_powF {d X e nb : Nat} (he : e < 2 ^ nb) :
    unpackR d (powF d X e nb) = (ops2 d).pow (unpackR d X) e := by
  have hw := ops2_pow_wf d (unpackR d X) e (by simp [unpackR]) (fun i hi => unpackR_lt hi)
  refine rowsMatrix_inj (d := d) ?_ hw.1 (fun i hi => unpackR_lt hi) hw.2 ?_
  · simp [unpackR]
  · rw [rowsMatrix_powF he, rowsMatrix_ops2_pow]

private theorem vmF_one {d : Nat} (hd : 0 < d) (M : Nat) : vmF d M 1 = rowF d M 0 := by
  rw [vmF_rec]
  have key : ∀ n, 0 < n → Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => if (1 : Nat).testBit k then rowF d M k ^^^ acc else acc) n = rowF d M 0 := by
    intro n hn
    induction n with
    | zero => exact absurd hn (Nat.lt_irrefl 0)
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        simp
      · have hb : (1 : Nat).testBit n = false := by
          have e1 : (1 : Nat) = 2 ^ 0 := rfl
          rw [e1, Nat.testBit_two_pow]
          simp only [decide_eq_false_iff_not]
          omega
        change (if (1 : Nat).testBit n = true then rowF d M n ^^^ _ else _) = _
        rw [hb]
        simp only [Bool.false_eq_true, ite_false]
        exact ih h0
  exact key d hd

theorem prodOrder_sound {d q nb A B : Nat} {csA csB : List Char} (hd : 0 < d) (hq : q < 2 ^ nb)
    (hA : m1Bind csA d A = true) (hB : m1Bind csB d B = true) (hk : orderK d A B q nb = true) :
    prodOrderOK (ops2 d) (String.ofList csA) (String.ofList csB) q 0 = true := by
  unfold orderK at hk
  rw [strictB_eq'] at hk
  obtain ⟨h1, h2⟩ := andB_true hk
  unfold prodOrderOK
  change ((ops2 d).eq ((ops2 d).pow (mulRows d (rowsOfPayload d (String.ofList csA))
      (rowsOfPayload d (String.ofList csB))) q) (ops2 d).one &&
    (ops2 d).vne ((ops2 d).vmul ((ops2 d).unit 0) (mulRows d (rowsOfPayload d (String.ofList csA))
      (rowsOfPayload d (String.ofList csB)))) ((ops2 d).unit 0)) = true
  rw [bind_sound hA, bind_sound hB, mulRows_unpackR, ← unpackR_powF hq, ops2_one_eq,
    ops2_eq_unpackR h1, Bool.true_and]
  refine vne_of_Zmove hd ?_
  have e1 : CFSG.KLie.CT.pw2 0 = 1 := rfl
  rw [e1, vmF_one hd]
  revert h2
  cases Nat.beq (rowF d (mulF d A B) 0) 1 <;> simp [CFSG.KLie.CT.notB]

end CFSG.KC.M1F2

end
