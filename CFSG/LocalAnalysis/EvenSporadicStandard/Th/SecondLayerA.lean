module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndNB

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

@[expose] def ThSecondLayerA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L R : Subgroup G) (t : G) (S A B Aa : Subgroup G) (z b : G),
    ThCyc G L R t → ThLocalIn L S A B z → ThLocalIn2 B A Aa b → SylowFacts L S B Aa →
    ∀ P : Subgroup G, IsPGroup 2 P → S ⊔ Bp A t ≤ P →
      ∀ c ∈ P, (∀ a ∈ A, c * a * c⁻¹ = a) →
        c ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G) → c ∉ S ⊔ Bp A t → False

theorem thSecondLayer_of_A (h : ThSecondLayerA) : ThSecondLayer := by
  intro G _ _ L R t S A B Aa z b H W W2 F P hP hSP hPN
  obtain ⟨D, hDC, hDab, hAaD, hDsup, hDdisj, hDcard, hDnorm, hBpC⟩ := H.exists_D W W2
  have hD : SylowEnd.DHyp A Aa t D := ⟨hDC, hDab, hAaD, hDsup, hDdisj, hDcard, hDnorm, hBpC⟩
  obtain ⟨c, hcP, hcA, hcN, hcT⟩ := H.exists_centralizing_mem_normalizer_Tprime W W2 hD
    F.abelian_le F.center_quotient hP hSP hPN
  exact h G L R t S A B Aa z b H W W2 F P hP hSP c hcP hcA hcN hcT

end CFSG.EvenSporadicStandard.ThStd
