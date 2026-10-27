module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.One
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Solv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69Full.Reindex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem b_6_9_of_compK (hComp : B69.AsB69ComponentK) : CFSG.ASVolI.B_6_9 := by
  intro V _ _ hV H T M hmp hK hO2 hFF
  have hP4 : AsB15Part4 := B15P4.asB15Part4
  have key : ∃ 𝓗 : Finset (Subgroup (MulAut V)), B69.StructConcl H T M 𝓗 ∧
      (∀ g ∈ H, ∀ K ∈ 𝓗, B6.conjSub g K ∈ 𝓗) ∧ ∀ K ∈ 𝓗, B69.CanonBlock H T M K := by
    by_cases hsolv : Group.IsSolvable ↥H
    · obtain ⟨𝓗, hsc, hperm, hnat⟩ := B69.structConclP_of_solvable hV hmp hO2 hFF hsolv
      refine ⟨𝓗, hsc, hperm, fun K hK' => ?_⟩
      obtain ⟨e, he, hbin, hM⟩ := hnat K hK'
      exact B69.canonBlock_of_nat (hsc.1 K hK') he hbin hM
    · have hB : B69.BlkCtx H T M := B69.blkCtxK_of_inputs hP4 hComp (B69.asB69GenByMinK_of hP4 hComp)
        hV hK hmp hO2 hFF hsolv
      refine ⟨B69.blkFamily H, B69.structConcl_of_blkCtx hB hmp hFF, ?_, ?_⟩
      · intro g hg K hK'
        obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hK'
        exact B69.mem_blkFamily.2 ⟨B6.conjSub g L, B113.isComponentOf_conj hL hg,
          (B69.conjSub_blk hg)⟩
      · intro K hK'
        obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hK'
        exact B69.canonBlock_blk hB hK hmp hFF hsolv hL
  obtain ⟨𝓗, hsc, hperm, hcanon⟩ := key
  obtain ⟨s, Hs, -, hmem, hprod, hsum, hcomm, ⟨hperm1, hperm2⟩, h4⟩ :=
    B69.canonFamily_of hsc hperm hmp.isSylow.1
  exact ⟨B69.qOf_eq_one_K hP4 hComp hV hK hmp hO2 hFF, s, Hs, hprod, hsum, hcomm,
    ⟨hperm1, hperm2⟩, h4, fun i => hcanon (Hs i) ((hmem _).2 ⟨i, rfl⟩)⟩

end CFSG.Quasithin
