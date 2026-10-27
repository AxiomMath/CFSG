module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.A2Plus
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.OutTriAux.Odd

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Dickson.Sec6.I923

set_option linter.unusedSectionVars false


@[expose] def TriD4A2Minus34 : Prop :=
  ∀ (ℓ f : ℕ) (hℓ : ℓ.Prime), 5 ≤ ℓ → 1 ≤ f → (ℓ ^ f) % 3 = 2 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (ℓ ^ f) ^ 3 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom, D4MinusToral ℓ f hℓ K σ s →
      NoL34Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ)

theorem triD4A2NoL34_of_minus (hMinus : TriD4A2Minus34) : TriD4A2NoL34 := by
  intro ℓ f hℓ hℓ5 hf K _ _ hK σ hσ s hs
  rcases hs with ⟨hq, d, hd, hd3, hd1, hsd⟩ | ⟨hq, hs⟩
  · have hℓ2 : ℓ ≠ 2 := by omega
    have hq5 : 5 ≤ ℓ ^ f := le_trans hℓ5 (Nat.le_self_pow (by omega) ℓ)
    exact OutTri.noL34Layer_a2_plus (a2Std_of_class hℓ hℓ2 hf hq hK hσ hd hd3 hd1) hq5 hsd
  · exact hMinus ℓ f hℓ hℓ5 hf hq K hK σ hσ s hs

end CFSG.HardMathSupport.Dickson.Sec6
