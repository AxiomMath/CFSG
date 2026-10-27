module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayerShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL6Wreath

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

@[expose] def ThSylowWreathPair : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G) (S A B Aa D : Subgroup G)
    (z b : G), ThCyc G L R t → ThLocalIn L S A B z → ThLocalIn2 B A Aa b → SylowFacts L S B Aa →
    DHyp A Aa t D → (∀ d ∈ D, d ^ 4 = 1) → (∀ d ∈ D, b * d * b⁻¹ = d⁻¹) →
    ∀ P : Subgroup G, IsPGroup 2 P → S ⊔ Bp A t ≤ P →
      ∀ y ∈ P, (∀ a ∈ A, y * a * y⁻¹ = a) →
        y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G) → y ∉ S ⊔ Bp A t →
      ∃ X : Subgroup G, Nat.card X = Nat.card S ∧
        (∀ a ∈ X, ∀ c ∈ X, a * (t * c * t⁻¹) = (t * c * t⁻¹) * a) ∧
        ∀ a ∈ X, t * a * t⁻¹ ∈ X → a = 1

theorem thSecondLayerB_of_sylowWreathPair (h : ThSylowWreathPair) : ThSecondLayerB := by
  intro G _ _ L R t S A B Aa D z b H W W2 F hD h4 hb P hP hSP y hyP hyA hyN hyT
  obtain ⟨X, hX, hcomm, hinter⟩ :=
    h G L R t S A B Aa D z b H W W2 F hD h4 hb P hP hSP y hyP hyA hyN hyT
  exact H.false_of_wreath W.isThSylow hX hcomm hinter

end CFSG.EvenSporadicStandard.ThStd
