module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDNonsolvable
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem transfer_residual_hyps (hS : Standing G) {q : ℕ} (hq : q ∈ rankThreeSigmaA G)
    {Q : Sylow q G} {M : Subgroup G} (hwq : IsWitness q Q M) {T : Subgroup G}
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
    exact hN (hwq.normalizer_le_of_forall_conj_two_le_pRank hq hT hY1 hYT
      fun n hn => by have := hcon n hn; omega)
  · by_contra h
    exact hN (hwq.normalizer_le_of_pRank_thompsonCore_le_one hS hq hT (by omega))
  · by_contra h
    exact hN (hwq.normalizer_le_of_pRank_thompsonJ_le_one hS hq hT (by omega))
  · exact hwq.gamma_one_le_of_residual hS hq hT hJe hC (Or.inr hns)

end CFSG.LocalAnalysis.RankThreeUC.S15
