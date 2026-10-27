module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenEightPairJShapeOrders
import CFSG.Adapters.LieModelSimple
import CFSG.Adapters.LinearCatalogStated
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRankOne
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.RankOneOut.Groups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenEight

open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.Open
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

section Main

theorem kFactThreeFourPairJShape_of (hB : LieOrderBridgeHyp) (hC : LieCharPartHyp)
    (hHe : IsSimpleGroup TauCeti.SporadicName.He.Group ∧
      Nat.card TauCeti.SporadicName.He.Group = 4030387200) :
    KFactThreeFourPairJShape := by
  intro p iK iJ hpair Y _ _ hY
  rcases hpair with
    ⟨-, q, hqp, hqe, dK, ⟨dJ, hv⟩, -, hdJ, -, rfl⟩ |
    ⟨-, q, hqp, hqe, dK, ⟨dJ, hv⟩, -, hdJ, -, rfl⟩ |
    ⟨-, q, hqp, hqe, dK, ⟨dJ, hv⟩, -, hdJ, -, rfl⟩ |
    ⟨-, q, hqp, hqe, dK, ⟨dJ, hv⟩, -, hdJ, -, rfl⟩ |
    ⟨-, h₁, h₂, -, rfl⟩ |
    ⟨-, q, hqp, hqe, ⟨dJ, hv⟩, hdJ, -, rfl⟩ |
    ⟨-, q, hqp, hqe, ⟨dJ, hv⟩, hdJ, -, rfl⟩ |
    ⟨-, -, rfl⟩
  all_goals obtain ⟨e⟩ := hY
  ·
    change dJ = .twistedA 3 q at hdJ
    subst hdJ
    have hqc : q.card = 2 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    have hcard : Nat.card Y = 25920 := by
      rw [hB ⟨.twistedA 3 q, hv⟩ Y ⟨e⟩]
      simp only [lieOrderFormula, hqc]
      norm_num [orderTwistedA, Finset.prod_Icc_succ_top]
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
    have hs : IsSimpleGroup Y := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    rw [hqp, hqe] at hm
    exact pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs
      (fun _ _ _ _ _ _ _ => u42Facts_of_model_psu_four_two hm)
  ·
    change dJ = .twistedA 2 q at hdJ
    subst hdJ
    have hqc : q.card = 8 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    have hcard : Nat.card Y = 5515776 := by
      rw [hB ⟨.twistedA 2 q, hv⟩ Y ⟨e⟩]
      simp only [lieOrderFormula, hqc]
      norm_num [orderTwistedA, Finset.prod_Icc_succ_top]
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    have hs : IsSimpleGroup Y := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    rw [hqp, hqe] at hm
    refine pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs ?_
    intro _ T J hT hNJ hJ hJtop
    obtain ⟨T', rfl⟩ := CFSG.AGLEmbedding.BlockCyc.exists_sylow_of_isSylowTwoOf_top hT
    exact absurd (CFSG.AGLEmbedding.LieOut.borelMaximal_of_model_psu_three hm T' J hNJ hJtop) hJ
  ·
    change dJ = .A 1 q at hdJ
    subst hdJ
    have hqc : q.card = 8 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    have hcard : Nat.card Y = 504 := by
      rw [hB ⟨.A 1 q, hv⟩ Y ⟨e⟩]
      simp only [lieOrderFormula, hqc]
      norm_num [orderA, Finset.prod_Icc_succ_top]
    have hm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
    have hs : IsSimpleGroup Y := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    rw [hqp, hqe] at hm
    refine pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs ?_
    intro _ T J hT hNJ hJ hJtop
    obtain ⟨T', rfl⟩ := CFSG.AGLEmbedding.BlockCyc.exists_sylow_of_isSylowTwoOf_top hT
    exact absurd (CFSG.AGLEmbedding.LieOut.borelMaximal_of_model_psl_two hm T' J hNJ hJtop) hJ
  ·
    change dJ = .A 2 q at hdJ
    subst hdJ
    have hqc : q.card = 3 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    have hcard : Nat.card Y = 5616 := by
      rw [hB ⟨.A 2 q, hv⟩ Y ⟨e⟩]
      simp only [lieOrderFormula, hqc]
      norm_num [orderA, Finset.prod_Icc_succ_top]
    have hs : IsSimpleGroup Y := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)
    exact pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs
      (fun hcl => absurd hcl (pairJ_not_isClassicalTwoOrG2_of_card hB hC hcard (by norm_num)))
  ·
    let e' : Y ≃* alternatingGroup (Fin 5) := e
    have hcard : Nat.card Y = 60 := by
      rw [Nat.card_congr e'.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hs : IsSimpleGroup Y := e'.isSimpleGroup
    exact pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs
      (fun _ T J hT hNJ hJ hJtop =>
        (CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.RankOneOut.false_of_alternating_five_parabolic
          e' T J hT hNJ hJ hJtop).elim)
  ·
    change dJ = .twistedA 2 q at hdJ
    subst hdJ
    have hqc : q.card = 5 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    have hcard : Nat.card Y = 126000 := by
      rw [hB ⟨.twistedA 2 q, hv⟩ Y ⟨e⟩]
      simp only [lieOrderFormula, hqc]
      norm_num [orderTwistedA, Finset.prod_Icc_succ_top]
    have hs : IsSimpleGroup Y := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e)
    exact pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs
      (fun hcl => absurd hcl (pairJ_not_isClassicalTwoOrG2_of_card hB hC hcard (by norm_num)))
  ·
    change dJ = .A 2 q at hdJ
    subst hdJ
    have hqc : q.card = 7 := by rw [TauCeti.PrimePower.card_def, hqp, hqe]; norm_num
    have hcard : Nat.card Y = 1876896 := by
      rw [hB ⟨.A 2 q, hv⟩ Y ⟨e⟩]
      simp only [lieOrderFormula, hqc]
      norm_num [orderA, Finset.prod_Icc_succ_top]
    have hs : IsSimpleGroup Y := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel
      (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e)
    exact pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs
      (fun hcl => absurd hcl (pairJ_not_isClassicalTwoOrG2_of_card hB hC hcard (by norm_num)))
  ·
    have hs : IsSimpleGroup Y := (MulEquiv.isSimpleGroup_congr e).2 hHe.1
    have hcard : Nat.card Y = 4030387200 := (Nat.card_congr e.toEquiv).trans hHe.2
    exact pairJ_clauses hB (by unfold IsPairJOrder; omega) hcard hs
      (fun hcl => absurd hcl (pairJ_not_isClassicalTwoOrG2_of_card hB hC hcard (by norm_num)))

end Main

end CFSG.LocalAnalysis.RankThreeTheoremC.TenEight
