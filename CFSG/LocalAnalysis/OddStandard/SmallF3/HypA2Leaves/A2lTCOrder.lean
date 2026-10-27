module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafLieOrderBig
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG CFSG.ComponentClassification.CatLeaf

theorem a2l_lieModel_two_card (hO : LieOrderFormulasInput) {X : Type} [Group X]
    {t : Open.StatedLieTag} {n f : ℕ} (hadm : Open.StatedLieAdmissible t n 2 f)
    (hX : Blueprint.LieModel X t n 2 f)
    (hc : Nat.card X = 360 ∨ Nat.card X = 6048 ∨ Nat.card X = 25920) :
    Nat.card X = 25920 ∧ t = .PSU ∧ n = 4 ∧ f = 1 := by
  obtain ⟨hb, hord⟩ := lie_bounds hO hadm hX (v := 6)
    (by rcases hc with h | h | h <;> rw [h] <;> decide)
  generalize Nat.card X = c at hc hord ⊢
  rcases lie_casework_le (by norm_num) hadm hb with
    ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, hn1, hn2, hf1, hf2⟩ | ⟨ht, rfl, rfl⟩ | ⟨ht, rfl, hf1, hf2⟩
  · rcases ht with rfl | rfl <;> simp only [lieSylowExponent] at hb <;>
      interval_cases n <;> interval_cases f <;> norm_num at hb <;>
      rcases hc with rfl | rfl | rfl <;>
      first | exact absurd hord (by decide) | exact ⟨rfl, rfl, rfl, rfl⟩
  · rcases ht with rfl | rfl
    · simp only [lieSylowExponent] at hb
      interval_cases n <;> interval_cases f <;> norm_num at hb <;>
        rcases hc with rfl | rfl | rfl <;>
        first | exact absurd hord (by decide) | exact ⟨rfl, rfl, rfl, rfl⟩
    · exact absurd rfl hadm.2.2.2
  · rcases ht with rfl | rfl <;> rcases hc with rfl | rfl | rfl <;>
      first | exact absurd hord (by decide) | exact ⟨rfl, rfl, rfl, rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ht
    cases t <;> simp only [ne_eq, not_true_eq_false] at h1 h2 h3 h4 h5 h6 <;>
      simp only [lieSylowExponent] at hb <;> interval_cases f <;> norm_num at hb <;>
      rcases hc with rfl | rfl | rfl <;> simp only [lieOrderNumerator, lieOrderDivisor] at hord <;>
      first | exact absurd hord (by decide) | exact ⟨rfl, rfl, rfl, rfl⟩

end CFSG.OddStandard.SmallF3.HypA2Leaves
