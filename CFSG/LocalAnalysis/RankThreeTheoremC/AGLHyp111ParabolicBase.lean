module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111FactorAtBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp
public import CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6CentralizingBase
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericFrobenius

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem relIndex_sup_of_le_normalizer {N K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (K ⊔ N) = N.relIndex K := by
  set A := K ⊔ N
  have hNA : N ≤ A := le_sup_right
  have hKA : K ≤ A := le_sup_left
  set N' := N.subgroupOf A
  set K' := K.subgroupOf A
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr
    (sup_le hK Subgroup.le_normalizer)
  have htop : K' ⊔ N' = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKA,
      Subgroup.map_subgroupOf_eq_of_le hNA, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show N'.index = _
  rw [← Subgroup.relIndex_top_right, ← htop, Subgroup.relIndex_sup_right,
    Subgroup.relIndex_subgroupOf hKA]

theorem false_of_sylow_base_of_factorAtB {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
    (h : D1PhaseThree p P M H R) (hCGT : AschbacherLocalCGTBlock) (hD2 : NoXBlockFor G)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKX : ¬ K ≤ d1X0 p M H)
    (hOM : (primeComplementCore (G := H) p).map H.subtype ≤ M)
    (hHfac : ∀ x ∈ H, ∃ m ∈ H ⊓ M, ∃ k : H,
      QuotientGroup.mk' (primeComplementCore (G := H) p) k ∈ K ∧ x = m * k)
    {B : Subgroup G} (hfacB : AGLCompetitorFactorAt p M H K B) (hXM : d1PlusCore p H K ≤ M)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hLn : (L.subgroupOf M).Normal)
    (hBp : IsPGroup p B) (hBH : B ≤ H) (hBM : B ≤ M)
    (hb3 : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ H → B ≤ Subgroup.normalizer (S : Set G) →
      S ≤ d1PlusCore p H K)
    (hsyl : ∀ RB : Subgroup G, CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo B RB →
      pCoreOf 2 M ≤ RB → RB ≤ H → RB ≤ M → ¬ 2 ∣ (L ⊓ RB).relIndex L) : False := by
  have hM : IsTwoLocal M := h.maxTwoLocal_M.1
  have hOH : pCoreOf 2 M ≤ pCoreOf 2 H := h.toD1Escape.twoCore_M_le h.twoCore_inf
  have hHM : pCoreOf 2 H ≤ M := h.toD1Escape.twoCore_le
  have hBS : B ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hBH.trans (localGroup_le_normalizer_pCoreOf 2 H)
  obtain ⟨RB, hSRB, hRB⟩ := TwoRest3A6.exists_isMaxInvariantTwoIn_ge
    (hb3 _ (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)
      (RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H) hBS)
    (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H) hBS
  have hRBX : RB ≤ d1PlusCore p H K := hRB.1
  have hRB1 : RB ≠ ⊥ := fun h1 =>
    pCoreOf_two_ne_bot h.maxTwoLocal_H.1 (le_bot_iff.mp (h1 ▸ hSRB))
  have habs := absorbsAt_of_factorAt hM h.maxTwoLocal_H hOH hHM hOM hHfac hfacB
  obtain ⟨hCGS, hRBmax⟩ := star_of_absorbsAt_of_le_normalizer h.prime h.ne_two hBp hBH hKX habs
    hb3 hRB hRB1 hRB.2.2.1
  have hRBM : RB ≤ M := hRBX.trans hXM
  have hRBH : RB ≤ H := hRBX.trans (Subgroup.map_subtype_le _)
  have hMn : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.le).mp hLn
  have hRBL : RB ≤ Subgroup.normalizer (L : Set G) := hRBM.trans hMn
  have hORB : pCoreOf 2 M ≤ RB :=
    TwoRest3A6.le_of_isMaxInvariantTwo hRBmax
      (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M)
      (hRBM.trans (localGroup_le_normalizer_pCoreOf 2 M))
      (hBM.trans (localGroup_le_normalizer_pCoreOf 2 M))
  have hsylRB : ¬ 2 ∣ ((L ⊓ RB).subgroupOf L).index := hsyl RB hRBmax hORB hRBH hRBM
  have hloc : ∀ C : Subgroup G, C ≤ RB → C ≠ ⊥ → (C.subgroupOf RB).Characteristic →
      Subgroup.normalizer (C : Set G) ≤ H := fun C hC hC1 hCc =>
    le_trans (by
      unfold CFSG.Quasithin.CGS
      exact le_iSup_of_le C <| le_iSup_of_le hC <| le_iSup_of_le hC1 <|
        le_iSup (fun _ : (C.subgroupOf RB).Characteristic => Subgroup.normalizer (C : Set G)) hCc)
      hCGS
  have hLH : L ≤ H := le_of_normal_block_of_local h.glob hCGT hD2 h.maxTwoLocal_M h.not_le hL.le
    hLn hRBM hRBmax.1 hORB hRBL hsylRB hloc
  exact hL.not_le_normalizer (hLH.trans (localGroup_le_normalizer_pCoreOf 2 H))

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
