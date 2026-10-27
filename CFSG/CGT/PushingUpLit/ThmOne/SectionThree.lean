module

public import CFSG.CGT.PushingUpLit.ThmOne.ThreeTenMain
public import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneOmega
public import CFSG.CGT.PushingUpLit.ThmOne.StepF

public section

namespace CFSG.CGT.PushingUpLit.ThmOne

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.Assembly (KProper InCatalog)

theorem sectionThree_holds (hE : CGT6.AschbacherEmbeddingK) : SectionThreeContent := by
  intro G _ _ hK hchar htop X hX hmax
  obtain ⟨hXcl, M, hM, hXM, hsub⟩ := hX
  have hMc := isCharacteristicP_of_isPLocal hchar hM.1
  have h31 := threeOne hE hK hchar htop hXcl hmax hM hXM hsub
  refine ⟨hXcl, fun R hR =>
    ⟨isSubnormal_normalizer_of_threeOne hXcl.1 hMc hXM hsub h31 hR, Or.inr ?_⟩⟩
  have hR' := (isSylowOf_centralizerModCore_inf_iff_of_threeOne hXcl.1 h31).mpr hR
  refine ⟨(le_normalizer_of_isSylowOf_inf hXM hR').trans (normalizer_le_normalizer_jIn R), ?_⟩
  by_contra hns
  have hR1 : R ≠ ⊥ := fun h => blockU_ne_bot_of_short hXcl.1 (le_bot_iff.mp (h ▸
    (blockU_le_inf_centralizer_of_isSylowOf hXcl.1 hXM hR').trans inf_le_left))
  obtain ⟨H, hJH, hH⟩ := exists_isMaximalTwoLocal_ge
    (isPLocal_normalizer_of_isPGroup (isPGroup_jIn hR.2.1) (jIn_ne_bot hR.2.1 hR1))
  exact false_of_threeSix (aschbacherEmbeddingAmbK'_holds hE) hXcl hMc hXM hsub h31 hR' hH
    (isCharacteristicP_of_isPLocal hchar hH.1)
    (CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup hK H
      fun h => htop (h ▸ hH.1))
    hJH (fun h => hns (CFSG.GroupTheory.isSubnormal_subgroupOf_of_le hJH h)) hmax

theorem aschbacherTheoremOneK_holds (hE : CGT6.AschbacherEmbeddingK) : AschbacherTheoremOneK :=
  aschbacherTheoremOneK_of_embeddingK hE (sectionThree_holds hE)

end CFSG.CGT.PushingUpLit.ThmOne
