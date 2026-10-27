module

public import CFSG.FeitThompson.Representations.ProductCharactersFullBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G] {W W1 W2 : Subgroup G}

namespace IsCyclicTIPair

open scoped Classical in
theorem cfInner_prodCharAlpha (h : IsCyclicTIPair W W1 W2) [Fintype ↥W]
    {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hk : k ≠ principalIrr ↥W1)
    (hj : j ≠ principalIrr ↥W2) (hl : l ≠ principalIrr ↥W2) :
    cfInner (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
        (h.prodCharAlpha (k : ↥W1 → ℂ) (l : ↥W2 → ℂ)) =
      (1 + if i = k then 1 else 0) * (1 + if j = l then 1 else 0) := by
  have e1 : ((principalIrr ↥W1 : Irr ↥W1) : ↥W1 → ℂ) = 1 := coe_principalIrr _
  have e2 : ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) = 1 := coe_principalIrr _
  have hone : (1 : ↥W → ℂ) = h.prodChar ((principalIrr ↥W1 : Irr ↥W1) : ↥W1 → ℂ)
      ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) := by rw [e1, e2, h.prodChar_one_one]
  simp only [prodCharAlpha_eq, hone, ← e1, ← e2, cfInner_sub_left, cfInner_sub_right,
    cfInner_add_left, cfInner_add_right, h.cfInner_prodChar, Prod.mk.injEq]
  simp only [hi, hj, Ne.symm hk, Ne.symm hl, and_false, false_and, if_false]
  by_cases h1 : i = k
  · by_cases h2 : j = l
    · simp only [h1, h2, and_self, if_true]
      norm_num
    · simp [h1, h2]
  · by_cases h2 : j = l
    · simp [h1, h2]
    · simp [h1, h2]

open scoped Classical in
theorem cfInner_prodCharAlpha_one (h : IsCyclicTIPair W W1 W2) [Fintype ↥W]
    {i : Irr ↥W1} {j : Irr ↥W2}
    (hi : i ≠ principalIrr ↥W1) (hj : j ≠ principalIrr ↥W2) :
    cfInner (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) (1 : ↥W → ℂ) = 1 := by
  have e1 : ((principalIrr ↥W1 : Irr ↥W1) : ↥W1 → ℂ) = 1 := coe_principalIrr _
  have e2 : ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) = 1 := coe_principalIrr _
  have hone : (1 : ↥W → ℂ) = h.prodChar ((principalIrr ↥W1 : Irr ↥W1) : ↥W1 → ℂ)
      ((principalIrr ↥W2 : Irr ↥W2) : ↥W2 → ℂ) := by rw [e1, e2, h.prodChar_one_one]
  simp only [prodCharAlpha_eq, hone, ← e1, ← e2, cfInner_sub_left, cfInner_add_left,
    h.cfInner_prodChar, Prod.mk.injEq]
  simp [hi, hj]

theorem cfInner_self_prodCharAlpha (h : IsCyclicTIPair W W1 W2) [Fintype ↥W]
    {i : Irr ↥W1} {j : Irr ↥W2} (hi : i ≠ principalIrr ↥W1) (hj : j ≠ principalIrr ↥W2) :
    cfInner (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ))
      (h.prodCharAlpha (i : ↥W1 → ℂ) (j : ↥W2 → ℂ)) = 4 := by
  classical
  rw [h.cfInner_prodCharAlpha hi hi hj hj]
  norm_num

end IsCyclicTIPair

end CFSG.FeitThompson
