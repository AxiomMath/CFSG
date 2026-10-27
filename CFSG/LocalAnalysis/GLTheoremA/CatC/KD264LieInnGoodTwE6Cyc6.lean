module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangAlg
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTwE6Class
import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyRhoHexGamma

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false

theorem perfectCentralizerPlanes_twistedE6_six {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hpK : ¬ p ∣ ℓ ^ f)
    (he : orderOf (((ℓ ^ f : ℕ)) : ZMod p) = 6) (hq3 : 3 ≤ ℓ ^ f) :
    PerfectCentralizerPlanes p (twistedE6RootGroup K σ) := by
  classical
  obtain ⟨Fr, hFr, g0, hg0C, hg0, S, hSD, hsyl, ⟨ε⟩⟩ :=
    springer_exists_langSetup_twistedE6_six frobeniusOnRoots_proved hℓ hf K hK σ hσ hp hp7 hpK he
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  haveI : Finite K := Nat.finite_of_card_ne_zero hK0
  have hq : S.D.q = ℓ ^ f := by rw [hSD]; rfl
  have hΦ' : S.D.Φ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr := by rw [hSD]; rfl
  have hAlg : S.IsAlgebraic := S.isAlgebraic_of_algebraic K 2 (by rw [hK, hq])
  have hcl : S.IsTwE6SixClass := ⟨Fr, fun c => by rw [hq]; exact hFr c, hΦ', by rw [hSD]; rfl⟩
  have hPS : BigAnyPBig S :=
    S.bigAnyPBig_of_twE6SixClass hcl hp7
      (S.hexGroupInGamma_of_hexStep_E6 (S.hexStep_of_twE6SixClass hcl) hAlg (by omega))
  exact PerfectCentralizerPlanes.of_mulEquiv ε.symm
    (perfectCentralizerPlanes_of_sylow_le_torus S hsyl fun D₁ hD₁E hD₁c =>
      bigComponentSet_nonempty_of_bigAnyPBig S hPS hD₁E hD₁c)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
