module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Odd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Plus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.UnCore

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GH74.GLS.Stage2.Bender.Thm1

set_option linter.unusedSectionVars false


@[expose] def TriD4A2Minus : Prop :=
  ∀ (ℓ f : ℕ) (hℓ : ℓ.Prime), ℓ ≠ 3 → ℓ ≠ 2 → 1 ≤ f → (ℓ ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, D4MinusToral ℓ f hℓ K σ s →
      NoL2Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

theorem triD4A2NoL2_of_minus (hMinus : TriD4A2Minus) : TriD4A2NoL2 := by
  intro ℓ f hℓ h3 h2 hf K _ _ hK σ hσ s hs
  rcases hs with ⟨hq, d, hd, hd3, hd1, hsd⟩ | ⟨hq, hs⟩
  · have hℓ5 : 5 ≤ ℓ := by
      have := hℓ.two_le
      have hne4 : ℓ ≠ 4 := fun h => by
        rw [h] at hℓ
        exact absurd hℓ (by decide)
      omega
    have hq5 : 5 ≤ ℓ ^ f :=
      le_trans hℓ5 (Nat.le_self_pow (by omega) ℓ)
    exact TriD4A2.noL2Layer_a2_plus hℓ (a2Std_of_class hℓ h2 hf hq hK hσ hd hd3 hd1)
      hq5 hsd
  · exact hMinus ℓ f hℓ h3 h2 hf hq K hK σ hσ s hs

theorem triD4A2Minus_holds : TriD4A2Minus := by
  intro ℓ f hℓ _ h2 hf hq K _ _ hK σ hσ s hs
  exact TriD4A2.noL2Layer_a2_minus hℓ h2 hf hq hK σ hσ s hs

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false


theorem triD4A2NoL2_holds : TriD4Aux.TriD4A2NoL2 :=
  TriD4Aux.triD4A2NoL2_of_minus TriD4Aux.triD4A2Minus_holds

end CFSG.HardMathSupport.Dickson.Sec6.I923
