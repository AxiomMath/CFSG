module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoMinusCore
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2TwoMinusFold

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem trialityA2CoreFreeTwoMinus_of_a2Core
    (hA2 : ∀ f : ℕ, 1 ≤ f → (2 ^ f) % 3 = 2 → ∀ (K₄ : Type) [Field K₄] [Finite K₄],
      Nat.card K₄ = ((2 ^ f) ^ 4) ^ 3 → ∀ σ₄ : K₄ ≃+* K₄, (∀ c, σ₄ c = c ^ ((2 ^ f) ^ 4)) →
      ∀ b : K₄ˣ, b ^ 3 = 1 → b ≠ 1 → A2Core σ₄ b ((2 ^ f) ^ 4)) :
    TrialityA2CoreFreeTwoMinus := by
  intro f hf K _ _ hK σ hσ hq s hs
  obtain ⟨K₄, hF, hfin, hCh, hK₄, σ₄, ε, hσ₄, hε, b, hb3, hb1, s₄, hs₄, ψ₄, hinj, hint, hfix⟩ :=
    un_frame Nat.prime_two hf hq K hK σ hσ s hs
  obtain ⟨hNo, hZ, hU⟩ :=
    unTau_props_two hf hq σ₄ ε hε b (hA2 f hf hq K₄ hK₄ σ₄ hσ₄ b hb3 hb1) s₄ hs₄
  obtain ⟨hA, hZ', hU'⟩ := fixSub_props_of_frame
    (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)
    (MulAut.conj s₄ * fieldActor (t := TwistTag.D4) σ₄ σ₄) (unTau σ₄ ε) ψ₄ hinj hint hfix hNo hZ
    hU
  exact ⟨hA, trialityFaithfulTwo_holds f hf K hK σ hσ _ hZ' hU'
    fun he => absurd he (not_even_of_pow_mod_three hq)⟩

theorem trialityA2CoreFreeTwoMinus_holds : TrialityA2CoreFreeTwoMinus :=
  trialityA2CoreFreeTwoMinus_of_a2Core fun _ hf hq _ _ _ hK₄ _ hσ₄ _ hb3 hb1 =>
    a2Core_of_frame_two hf hq hK₄ hσ₄ hb3 hb1

end CFSG.HardMathSupport.Timmesfeld.CrossChar
