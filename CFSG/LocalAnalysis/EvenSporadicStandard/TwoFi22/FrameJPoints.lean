module

public import CFSG.Sporadic.Fi23.Centralizer
public import Certificates.Certificate24670

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.FrameJ

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native
open CFSG.EvenSporadicStandard.Wong77.Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem fjPts_lt (i : Fin 23) : fjIdx.getD i.val 0 < 31671 := by
  revert i
  decide +kernel

section


theorem fjPt_mem (i : Fin 23) : fjPt i ∈ D23 :=
  (isConj_d_iff _).2 ⟨⟨fjIdx.getD i.val 0, fjPts_lt i⟩, rfl⟩

theorem fjPt_zero : fjPt 0 = d := conjPt_zero

theorem fjPt_ne {i j : Fin 23} (hij : i ≠ j) : fjPt i ≠ fjPt j := by
  have hnd : ∀ i j : Fin 23, fjIdx.getD i.val 0 = fjIdx.getD j.val 0 → i = j := by
    decide +kernel
  intro h
  have hi := fjPts_lt i
  have hj := fjPts_lt j
  rw [← orb_size] at hi hj
  exact hij (hnd i j (conjPt_inj hi hj h))

theorem fjPt_sq (i : Fin 23) : fjPt i * fjPt i = 1 := by
  rw [← pow_two, ← orderOf_of_isConj (fjPt_mem i), pow_orderOf_eq_one]

theorem fjPt_ne_one (i : Fin 23) : fjPt i ≠ 1 := by
  intro h
  have := orderOf_of_isConj (fjPt_mem i)
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem fjPt_inv (i : Fin 23) : (fjPt i)⁻¹ = fjPt i := inv_eq_of_mul_eq_one_right (fjPt_sq i)

theorem fjPt_mul_ne_one {i j : Fin 23} (hij : i ≠ j) : fjPt i * fjPt j ≠ 1 := by
  intro h
  rw [mul_eq_one_iff_eq_inv, fjPt_inv] at h
  exact fjPt_ne hij h

end

section


theorem fjPt_comm (i j : Fin 23) : fjPt i * fjPt j = fjPt j * fjPt i :=
  Certificates.certificate24670.1 i j

theorem fjPt_mul_ne {i j k : Fin 23} (hij : i ≠ j) (hik : k ≠ i) (hjk : k ≠ j) :
    fjPt i * fjPt j ≠ fjPt k :=
  Certificates.certificate24670.2.1 i j k hij hik hjk

theorem fjPt_mul_mul_ne_one {i j k : Fin 23} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    fjPt i * fjPt j * fjPt k ≠ 1 := by
  intro h
  rw [mul_eq_one_iff_eq_inv, fjPt_inv] at h
  exact fjPt_mul_ne hij hik.symm hjk.symm h

theorem fjPt_rel (r : Fin 12) : ((rowList (golayMask r)).map fjPt).prod = 1 :=
  Certificates.certificate24670.2.2 r

end

end CFSG.EvenSporadicStandard.TwoFi22.FrameJ
