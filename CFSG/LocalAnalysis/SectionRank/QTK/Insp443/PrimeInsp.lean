module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PrimeDefs
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBMain

public section

namespace CFSG.SectionRank.QTK

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443

theorem insp443'_of'
    (hI : Insp443List') : Insp443' := by
  intro G _ _ T M L B Tp VB K hS hU hO hKB hNK hq hKM hVK hLK hcen
  have hNt : normalizer (B : Set G) ≠ ⊤ := by
    intro hN
    have hBn : B.Normal := normalizer_eq_top_iff.mp hN
    rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hS.hyp.simple B hBn with h | h
    · exact hS.hyp.B_ne_bot h
    · obtain ⟨a, b, hab⟩ := hS.hyp.nonabelian
      have hc := hS.hyp.B_comm.is_comm.comm ⟨a, h ▸ mem_top a⟩ ⟨b, h ▸ mem_top b⟩
      exact hab (congrArg Subtype.val hc)
  have hKt : K ≠ ⊤ := fun h => hNt (top_le_iff.mp (h ▸ hKB))
  exact hI G T M L B Tp VB K hS hU hO hKB hNK hq hKM hVK hLK hcen
    (CoverB.qtkSimpleList_of_cover hS.hyp.qtke.2.2 hq
      (isKGroupCat_of_kProper hS.hyp.qtke.1 hKt))

end CFSG.SectionRank.QTK
