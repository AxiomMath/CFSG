module

public import Certificates.Data.Kernel.Spor.MulHC
public import Certificates.Data.Kernel.Spor.MulHQ
public import CFSG.Certificates.Kernel.Spor.PEnumRSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KS.MulH

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PEnum CFSG.KS.Raw.Orb

theorem clRK_find {n w k K cnt : Nat} {GI GJ T PL POS SRT SRI CL : Nat → Nat}
    (hb : ∀ i < cnt, CFSG.KS.PEnumR.penumPtR n w (mask w) GI k cnt T PL POS SRT SRI i = true)
    {c : Nat} (hc : c < cnt * K)
    (h : clRK k K cnt T POS (prodQK n w (mask w) K T (bothK k GI GJ)) CL c = true) :
    findPtK cnt T (prodQK n w (mask w) K T (bothK k GI GJ)) CL c = true := by
  unfold clRK at h
  rw [strictB_eq, bIf_eq] at h
  by_cases hj : Nat.blt (Nat.mod c K) k = true
  · rw [if_pos hj] at h
    have hjk : c % K < k := Nat.blt_eq.mp hj
    have hi : c / K < cnt := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hc)
    obtain ⟨hq, hT⟩ := (CFSG.KS.PEnumR.penumPtR_spec (hb _ hi)).2 _ hjk
    have hpos : r32 CL c = r32 POS (c / K * k + c % K) := Nat.eq_of_beq_eq_true h
    have eQ : prodQK n w (mask w) K T (bothK k GI GJ) c =
        pcomp n w (mask w) (T (c / K)) (GI (c % K)) := by
      unfold prodQK bothK
      change pcomp n w (mask w) (T (c / K)) (Bool.rec (motive := fun _ => Nat)
        (GJ (Nat.sub (c % K) k)) (GI (c % K)) (Nat.blt (c % K) k)) = _
      have hj' : Nat.blt (c % K) k = true := hj
      rw [hj']
    unfold findPtK
    rw [strictB_eq, bAnd_eq, Bool.and_eq_true, hpos, eQ, hT]
    exact ⟨Nat.blt_eq.mpr hq, Nat.beq_refl _⟩
  · rw [if_neg hj] at h
    exact h

end CFSG.KS.MulH

end
