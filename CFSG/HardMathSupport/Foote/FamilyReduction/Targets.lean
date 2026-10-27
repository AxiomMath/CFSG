module

public import CFSG.HardMathSupport.Foote.FamilyReduction.RowAlt
public import CFSG.HardMathSupport.Foote.FamilyReduction.RowOdd
public import CFSG.HardMathSupport.Foote.FamilyReduction.RowEven
public import CFSG.HardMathSupport.Foote.FamilyReduction.Glue

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG CFSG.HardMathSupport.Foote.Coordinator CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)


theorem lieModel_of_classical {Q : Type} [Group Q] {t : StatedLieTag} {n p f : ℕ}
    (hm : StatedClassicalModel Q t n p f) : LieModel Q t n p f := by
  refine Or.inl ⟨?_, hm⟩
  have h2 := hm.2
  cases t <;> first | exact h2.elim | simp [CFSG.Blueprint.classicalTags]

theorem altTarget : AltTarget := fun n hn =>
  end415K_of_not_compIn5 fun _ hc => not_comp5_alternating hn (MulEquiv.refl _) hc.toComp5

theorem lieModel_of_suzuki {Q : Type} [Group Q] {p f : ℕ} (hm : SuzukiModel Q p f) :
    StatedLieAdmissible .twistedB2 0 p f ∧ LieModel Q .twistedB2 0 p f := by
  have hm' := hm
  obtain ⟨hℓ, a, ha, K, _, _, hf, -, -⟩ := hm'
  refine ⟨⟨?_, ?_, rfl, hℓ, ⟨a, hf⟩, ?_⟩, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hm⟩))⟩
  · rw [hℓ]
    exact Nat.prime_two
  · omega
  · omega


theorem not_compIn5_of_lieModel_ne_five {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ∃ x y : Q, x * y ≠ y * x) {t : StatedLieTag} {n p f : ℕ} (hp : p ≠ 5)
    (hadm : StatedLieAdmissible t n p f) (hm : LieModel Q t n p f) : ¬ CompIn5 Q := by
  by_cases h2 : p = 2
  · subst h2
    exact not_comp5_evenLie hna hadm hm
  · exact fun hc => not_comp5_oddLie hadm.1 h2 hp hadm hm hc.toComp5

theorem classicalOffFiveTarget : ClassicalOffFiveTarget := by
  intro Q _ t n p f hp hm
  exact end415K_of_not_compIn5 fun hna =>
    not_compIn5_of_lieModel_ne_five hna hp hm.1 (lieModel_of_classical hm)

theorem excOffFiveTarget : ExcOffFiveTarget := by
  intro Q _ t p f hp ht hm
  exact end415K_of_not_compIn5 fun hna =>
    not_compIn5_of_lieModel_ne_five hna hp hm.1 (Or.inr (Or.inl ⟨rfl, ht, hm⟩))

theorem reeTitsSuzukiTarget : ReeTitsSuzukiTarget := by
  refine ⟨?_, ?_⟩
  · intro Q _ t p f ht hm
    have hp5 : p ≠ 5 := by
      have h1 := hm.1
      simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact fun h => by have := h1.2.2; simp_all [StatedLieAdmissible]
      · exact fun h => by have := h1.2.2; simp_all [StatedLieAdmissible]
      · exact fun h => by have := h1.2.2; simp_all [StatedLieAdmissible]
    exact end415K_of_not_compIn5 fun hna =>
      not_compIn5_of_lieModel_ne_five hna hp5 hm.1 (Or.inr (Or.inr (Or.inl ⟨rfl, ht, hm⟩)))
  · intro Q _ p f hm
    obtain ⟨hadm, hlie⟩ := lieModel_of_suzuki hm
    have hp5 : p ≠ 5 := by
      have := hadm.2.2.2.1
      omega
    exact end415K_of_not_compIn5 fun hna => not_compIn5_of_lieModel_ne_five hna hp5 hadm hlie

end CFSG.HardMathSupport.Foote.FamilyReduction
