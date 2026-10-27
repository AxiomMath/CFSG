module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH3b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888End4a

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

theorem isPlaneData_of_hyp [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) :
    IsPlaneData (planeV hS.quad α) (planeW hS.quad α) (planeRho hS.quad α) := by
  haveI : Finite X := Finite.of_surjective α hS.surj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact planeW_le hS.quad α
  · exact card_V_of_planes (planeV_comm hS.quad α hS.ker) (planeW_le hS.quad α)
      (card_planeW hS) (planeV_decomp hS.quad α) (planeRho_mem hS.quad α)
      (planeRho_inv hS.quad α) (planeRho_triv hS.quad α) (planeRho_fpf hS.quad α hS.ker)
  · exact card_planeW hS
  · exact planeV_decomp hS.quad α
  · exact planeRho_mem hS.quad α
  · exact planeRho_order hS
  · exact planeRho_comm hS.quad α
  · exact planeRho_inv hS.quad α
  · exact planeRho_triv hS.quad α
  · exact planeRho_fpf hS.quad α hS.ker
  · exact planeW_trans hS hP

theorem xdata_of_hyp [Finite H] [Finite X] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) (S : Sylow 2 X) (hST : (S : Subgroup X) = T.map α) :
    XData S (planeV hS.quad α) (planeW hS.quad α) (planeRho hS.quad α) := by
  refine ⟨isPlaneData_of_hyp hS hP, planeV_comm hS.quad α hS.ker,
    planeV_sq hS.quad α hS.ker, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hST]
    exact planeV_le_map hP α
  · intro s hs
    rw [hST] at hs
    exact planeV_normS hS hP s hs
  · intro a ha g hg
    rw [hST] at hg
    exact planeV_closed hS hP a ha g hg
  · intro s hs hcomm
    rw [hST] at hs
    exact planeV_centS hS hP s hs hcomm
  · exact planeW_perm hS hP

end CFSG.OddStandard.SmallF3.Omega
