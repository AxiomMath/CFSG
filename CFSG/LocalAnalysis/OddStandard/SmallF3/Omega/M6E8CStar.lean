module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6ShapesDef
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4ChainMain
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L65
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem m6e8_inCStar_of_u43 [Finite G] (hsh : Asc82Shapes) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {A : Subgroup G} (hAC : InC A) (hAF : InFStar A)
    (hA : IsOmega6Minus A) : InCStar A := by
  have hAq : IsQuasisimple ↥A := sec65_quasisimple hAF
  refine inCStar_of_ctrQ_maximal hS.a2 hAC hAF fun B hBC hBF hdvd => ?_
  have hq' := sec65_quasisimple hBF
  rw [ctrQ_of_u43 hAq hA] at hdvd ⊢
  rcases sec65_shape hsh hS hBC hBF with h | h | h | h | h | h
  · rw [ctrQ_of_l29 hq' h] at hdvd
    omega
  · rw [ctrQ_of_l281 hq' h] at hdvd
    omega
  · rcases h with h | h
    · rw [ctrQ_of_l33 hq' h] at hdvd
      omega
    · rw [ctrQ_of_u33 hq' h] at hdvd
      omega
  · rw [ctrQ_of_psp4 hq' h] at hdvd
    omega
  · rw [ctrQ_of_l43 hq' h] at hdvd
    omega
  · exact ctrQ_of_u43 hq' h

end CFSG.OddStandard.SmallF3.Omega
