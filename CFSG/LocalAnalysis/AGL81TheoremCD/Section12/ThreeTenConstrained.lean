module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
public import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem isPConstrained_of_pLayerIn_eq_bot {p : ℕ} (hp : p.Prime) (H : Subgroup G)
    (hL : pLayerIn p H = ⊥) : CFSG.ABGLocalTools.IsPConstrained p ↥H := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlayer : CFSG.layer (StarGroup p H) = ⊥ := (pLayerIn_eq_bot_iff hp H).mp hL
  refine (CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_iff_hasPrimeConstraint
    (p := p) (H := ↥H)).2 ?_
  refine ⟨CFSG.pCore p (StarGroup p H), CFSG.pCore_normal, CFSG.pCore_isPGroup, ?_⟩
  exact centralizer_pCore_le_of_layer_eq_bot hp H hlayer

theorem mem_sigma_prime_odd_ne_p {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) {d : ℕ}
    (hd : d ∈ sigmaSet G M) : d.Prime ∧ d ≠ 2 ∧ d ≠ p :=
  ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1,
    CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_odd d hd.1,
    fun hdp => h.p_not_mem_sigma (hdp ▸ hd)⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
