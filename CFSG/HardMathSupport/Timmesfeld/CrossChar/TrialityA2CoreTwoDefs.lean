module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityA2Core

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

section Defs


@[expose] def TrialityA2CoreFreeTwoToral : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) → (2 ^ f) % 3 = 1 →
    ∀ (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (d : Kˣ),
      Units.map σ.toRingHom.toMonoidHom d = d → d ^ 3 = 1 → d ≠ 1 →
      (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1] →
      CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

@[expose] def TrialityA2CoreFreeTwoMinus : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (2 ^ f)) → (2 ^ f) % 3 = 2 →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      CFSG.GH74.GLS.Stage2.Bender.Thm1.D4MinusToral 2 f Nat.prime_two K σ s →
      CoreFreeAt 3 (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

theorem trialityA2CoreFreeTwo_of_parts (h1 : TrialityA2CoreFreeTwoToral)
    (h2 : TrialityA2CoreFreeTwoMinus) : TrialityA2CoreFreeTwo := by
  intro f hf K _ _ hK σ hσ s hs
  rcases hs with ⟨hq, d, hd, hd3, hd1, hsd⟩ | ⟨hq, hsm⟩
  · exact h1 f hf K hK σ hσ hq s d hd hd3 hd1 hsd
  · exact h2 f hf K hK σ hσ hq s hsm

end Defs

end CFSG.HardMathSupport.Timmesfeld.CrossChar
