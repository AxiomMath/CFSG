module

public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem cStarStarIn_le_cStarIn {G T : Subgroup Γ} (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    cStarStarIn G T ≤ cStarIn G T := by
  have hJb : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hchar : ((thompsonJ T).subgroupOf (baum T)).Characteristic := by
    have heq : thompsonJ (baum T) = thompsonJ T := B6.thompsonJ_eq_of_le hJb inf_le_left
    have := CFSG.QuasithinUnique.Setup.characteristic_thompsonJ (baum T)
    rwa [heq] at this
  refine sup_le_sup_left ?_ _
  exact le_iSup_of_le (thompsonJ T) (le_iSup_of_le hJb
    (le_iSup_of_le (CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hT2 hT1)
      (le_iSup_of_le hchar le_rfl)))

end CFSG.CGT.PushingUpLit.BHS7
