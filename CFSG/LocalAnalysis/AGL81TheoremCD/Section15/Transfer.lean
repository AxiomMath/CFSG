module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDNonsolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.NoXBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.GNSettingM

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {G : Type} [Group G] [Finite G]

theorem transfer_residual_hyps_gen (hS : StandingGen G) {q : ℕ} {Q : Sylow q G}
    {M : Subgroup G} (hq : IsWitnessPrime q Q) (hwq : IsWitnessGen q Q M) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hJe : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G))
    (hns : ¬ Group.IsSolvable ↥(CFSG.Quasithin.autOn M (uCore M T)))
    (hN : ¬ normalizer (T : Set G) ≤ M) :
    (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank q (normalizer (C : Set G)) ≤ 1) ∧
    (∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ T → ∃ n ∈ normalizer (T : Set G),
      CFSG.Open.pRank q
        (M ⊓ normalizer ((Y.map (MulAut.conj n).toMonoidHom : Subgroup G) : Set G)) ≤ 1) ∧
    2 ≤ CFSG.Open.pRank q (thompsonCore M T) ∧
    2 ≤ CFSG.Open.pRank q (CFSG.Quasithin.thompsonJ M) ∧
    rankThreeGamma 1 q (Q : Subgroup G) ≤ M := by
  have hC : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank q (normalizer (C : Set G)) ≤ 1 := by
    intro C hC1 hCT hchar
    by_contra h
    exact hN (hwq.normalizer_le_of_characteristic_global hS hq hT hC1 hCT hchar (by omega))
  refine ⟨hC, ?_, ?_, ?_, ?_⟩
  · intro Y hY1 hYT
    by_contra hcon
    push Not at hcon
    exact hN (hwq.normalizer_le_of_forall_conj_two_le_pRank hq.prime hT hY1 hYT
      fun n hn => by have := hcon n hn; omega)
  · by_contra h
    exact hN (hwq.normalizer_le_of_pRank_thompsonCore_le_one hS hq hT (by omega))
  · by_contra h
    exact hN (hwq.normalizer_le_of_pRank_thompsonJ_le_one hS hq hT (by omega))
  · exact hwq.gamma_one_le_of_residual hS hq hT hJe hC (Or.inr hns)

theorem gnSetting_of_noXBlockFor (hS : StandingGen G)
    (hX : CFSG.AGLEmbeddingD2.NoXBlockFor G) {M T : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) :
    GNSetting ↥M (T.subgroupOf M) := by
  haveI := hS.simple
  have hMtop : M ≠ ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top hS.nonab M hM.1
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.gnSetting_of_subgroup hS.kProper hMtop
    (hS.charTwo M hM.1) (CFSG.ABGLocalTools.isSylowOf_iff.mp hT)
    (fun Y hYM hYs hY => hX M Y hM hYM hYs hY)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
