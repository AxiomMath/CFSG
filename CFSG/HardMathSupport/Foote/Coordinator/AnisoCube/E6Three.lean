module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Skeleton
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.Open CFSG.LieType.SeitzGeneration

theorem dvd_sq_add_add_one_of_orderOf_eq_three {p q : ℕ} (hp : p.Prime)
    (h : orderOf ((q : ℕ) : ZMod p) = 3) : p ∣ q ^ 2 + q + 1 ∧ p ≠ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hx3 : ((q : ℕ) : ZMod p) ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  have hx1 : ((q : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at h
    exact absurd h (by norm_num)
  refine ⟨?_, ?_⟩
  · have hfac : (((q : ℕ) : ZMod p) - 1) * (((q : ℕ) : ZMod p) ^ 2 + ((q : ℕ) : ZMod p) + 1) = 0 := by
      linear_combination hx3
    have hq : ((q : ℕ) : ZMod p) ^ 2 + ((q : ℕ) : ZMod p) + 1 = 0 :=
      (mul_eq_zero.1 hfac).resolve_left (sub_ne_zero.2 hx1)
    refine (ZMod.natCast_eq_zero_iff (q ^ 2 + q + 1) p).1 ?_
    push_cast
    exact hq
  · rintro rfl
    have hF : ((q : ℕ) : ZMod 3) ^ 3 = (q : ZMod 3) := ZMod.pow_card _
    exact hx1 (hF.symm.trans hx3)

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube
