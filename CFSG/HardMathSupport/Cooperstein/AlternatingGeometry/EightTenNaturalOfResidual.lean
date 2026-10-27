module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNaturalOfResidual
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSevenOutcomes

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open

theorem eightTen_natural_of_residual (hnat : GF2NaturalLSL)
    (hres : EightTenResidualOutcomes) :
    ∀ (G : Type) [Group G] [Finite G] (X S L : Subgroup G), CFSG.Open.IsKGroup ↥X →
      Asc81bHyp X S → IsWeakSBlock X S L → S ≤ Subgroup.normalizer (L : Set G) →
      ∀ m : ℕ, (m = 7 ∨ 8 < m) →
      Nonempty (↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃*
        alternatingGroup (Fin m)) → NaturalSectionLSL S L m → EightTenOutcomes X S L := by
  intro G _ _ X S L hX hA hL hSL m hm he hN
  rcases hm with rfl | hm8
  · exact eightTen_outcomes_of_natural_seven hX hA hL hN
  · obtain ⟨e⟩ := he
    rcases eightTen_outcomes_or_residual' hnat hX hA hL hm8 e hN with h | h
    · exact h
    · exact hres G X S L hX hA hL m hm8 e hN h

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
