module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagGlue

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross (E6DiagIsotropic TwistedE6DiagIsotropic)


@[expose] def E6HeisFrameNormalizesR : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K ≠ 3 → 4 ≤ Nat.card K →
    ∀ E : Subgroup (MulAut (adjointGroup Tag.E6 K)), CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → E ≤ e6Inndiag K → E6HeisenbergFrame K E → E6NormalizesR K E

@[expose] def TwE6HeisFrameNormalizesR : Prop :=
  ∀ (ℓ f : ℕ), ℓ.Prime → ℓ ≠ 3 → 1 ≤ f → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = (ℓ ^ f) ^ 2 → ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)),
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → CFSG.IsElementaryAbelian 3 E →
      Nat.card E = 3 ^ 2 → TwE6HeisenbergFrame K σ (ℓ ^ f) E → TwE6NormalizesR K σ E

theorem e6HeisenbergParabolic_of_frame (h : E6HeisFrameNormalizesR) : E6HeisenbergParabolic := by
  intro K _ _ hK3 K₁ _ hroot E hEab hcard hE hnin hiso
  have hK4 := four_le_card_of_not_innerAut K hK3 E hE hnin
  obtain ⟨F⟩ := exists_e6HeisenbergFrame hK3 hK4 K₁ hroot E hEab hcard hE hiso
  exact h K hK3 hK4 E hEab hcard hE F

theorem twE6HeisenbergParabolic_of_frame (h : TwE6HeisFrameNormalizesR) :
    TwE6HeisenbergParabolic := by
  intro K _ _ σ q hK3 hσ hK K₁ _ hroot E hE hEab hcard hnin hiso
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hK
    (by
      by_contra h
      have hq : q ≤ 1 := by omega
      have : Nat.card K ≤ 1 := by
        rw [hK]; nlinarith [Nat.zero_le q]
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      omega)
  obtain ⟨F⟩ := exists_twE6HeisenbergFrame (ringChar K) f hp hK3 hf hK σ hσ K₁ hroot E hEab
    hcard hE hiso
  exact h (ringChar K) f hp hK3 hf K hK σ hσ E hE hEab hcard F

end CFSG.LieType.SeitzGeneration.ExcWideThree
