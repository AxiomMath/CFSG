module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ADefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieConfig
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1ConfigU3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1OneSmall3Data.exists_sylow (hd : D1OneSmall3Data p P M H R Rbar K) :
    ∃ T₁ : Sylow p K, (T₁ : Subgroup K).map K.subtype =
        (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K ∧
      IsSimpleGroup K ∧ (∃ a b : K, a * b ≠ b * a) ∧ IsCatalogGroup K ∧
      ¬ IsCyclic (T₁ : Subgroup K) ∧ GLBCore p 1 (T₁ : Subgroup K) ≠ ⊤ ∧
      (GLBCore p 1 (T₁ : Subgroup K)).map K.subtype ≤ d1X0 p M H := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hsimple, hnonab⟩ := hd.toCore.isSimpleGroup
  let e : K ≃* K ⧸ Subgroup.center K :=
    ((QuotientGroup.quotientMulEquivOfEq hd.center).trans QuotientGroup.quotientBot).symm
  have hcat : IsCatalogGroup K :=
    IsCatalogGroup.of_mulEquiv e (hd.cfg.catalog.isCatalogGroup_center_quotient hd.comp)
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (ComponentClassification.Components.mathlib_subnormal_of_chain hd.comp.2.1
      Subgroup.IsSubnormal.top)
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  obtain ⟨hN, hKX₀⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzR hzK hzp hzc
  have hTnc : ¬ IsCyclic (T : Subgroup K) := fun hc => hd.noncyclic (by
    rw [← hT]
    exact isCyclic_of_surjective _ (K.subtype.subgroupMap_surjective (T : Subgroup K)))
  exact ⟨T, hT, hsimple, hnonab, hcat, hTnc, hd.cfg.red.glbCore_ne_top_of_rankOne hN hKX₀ hT,
    glbCore_map_le_of_normalizer_le hp hT hN⟩

theorem D1OneSmall3Data.toPhaseThree (hUP : KFactUPrimeSmall)
    (hd : D1OneSmall3Data p P M H R Rbar K) (hL : ¬ (p = 3 ∧ IsLinThreeFour K))
    (hF : ¬ (p = 5 ∧ IsFi22 K)) : D1PhaseThree p P M H R := by
  obtain ⟨T, -, hs, hn, hc, hTnc, hΓ, -⟩ := hd.exists_sylow
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hd.z
  exact hd.cfg.toU.toPhaseThree (hd.cfg.red.uPrimeHyp_of_rankOne hd.comp hd.noncyclic hzR hzK hzp
    hzc (hUP K hs hn hc p hd.cfg.red.prime hd.cfg.red.ne_two T hTnc hΓ hd.small hL hF))

end CFSG.LocalAnalysis.RankThreeTheoremC
