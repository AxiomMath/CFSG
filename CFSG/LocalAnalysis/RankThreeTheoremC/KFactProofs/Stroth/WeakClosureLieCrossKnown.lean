module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossPsl2
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossThree
import CFSG.LieType.BorelTits.Suzuki
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem wcOn_cross_suzuki {K : Type} [Group K] [Finite K]
    {ℓ f p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h : SuzukiModel K ℓ f) : WCOn p K := by
  obtain ⟨-, a, ha, F, _, _, hfa, hcard, ⟨e⟩⟩ := h
  have hF : Nat.card F = 2 ^ (2 * a + 1) := by rw [hcard, hfa]
  let e' : K ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  exact WCOn.of_isCyclic_sylow
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
      a ha hF e' p hp2)

@[expose] def CrossCharKnown (t : StatedLieTag) (n ℓ f p : ℕ) : Prop :=
  t = .twistedB2 ∨ (t = .PSL ∧ n = 2) ∨
    (p = 3 ∧ n = 3 ∧ ((t = .PSL ∧ (ℓ ^ f % 9 = 4 ∨ ℓ ^ f % 9 = 7)) ∨
      (t = .PSU ∧ (ℓ ^ f % 9 = 2 ∨ ℓ ^ f % 9 = 5))))

theorem wcOn_of_crossCharKnown {K : Type} [Group K] [Finite K]
    {t : StatedLieTag} {n ℓ f p : ℕ} (hmodel : LieModel K t n ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hk : CrossCharKnown t n ℓ f p) : WCOn p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases hk with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl, ⟨rfl, hq⟩ | ⟨rfl, hq⟩⟩
  · rcases hmodel with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact wcOn_cross_suzuki hp2 hS
  · exact wcOn_cross_psl_two hp2 hpℓ (hmodel.statedClassicalModel (by decide))
  · exact wcOn_cross_psl_three (hmodel.statedClassicalModel (by decide)) hq
  · exact wcOn_cross_psu_three (hmodel.statedClassicalModel (by decide)) hq

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
