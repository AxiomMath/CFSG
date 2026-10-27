module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs

public section

namespace CFSG.HardMathSupport.Lang.Proving

private lemma sixth_sub_one (q : ℕ) : q ^ 6 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
  rcases Nat.eq_zero_or_pos (q ^ 3) with h | h
  · have hq : q = 0 := pow_eq_zero_iff (by norm_num) |>.mp h
    subst hq
    simp
  · have h6 : q ^ 6 = q ^ 3 * q ^ 3 := by ring
    rw [h6]
    have hx : 1 ≤ q ^ 3 := h
    obtain ⟨a, ha⟩ : ∃ a, q ^ 3 = a + 1 := ⟨q ^ 3 - 1, by omega⟩
    rw [ha]
    simp only [Nat.add_sub_cancel]
    rw [show (a + 1) * (a + 1) - 1 = a * (a + 2) by
      rw [Nat.sub_eq_of_eq_add]; ring]

theorem pgl3_order_dvd_G2 (q : ℕ) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∣
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .G2 0 q := by
  show q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) ∣ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
  refine ⟨q ^ 3 * (q ^ 3 + 1), ?_⟩
  rw [sixth_sub_one q]
  ring

theorem pgu3_order_dvd_G2 (q : ℕ) :
    q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ∣
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .G2 0 q := by
  show q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) ∣ q ^ 6 * (q ^ 6 - 1) * (q ^ 2 - 1)
  refine ⟨q ^ 3 * (q ^ 3 - 1), ?_⟩
  rw [sixth_sub_one q]
  ring

end CFSG.HardMathSupport.Lang.Proving
