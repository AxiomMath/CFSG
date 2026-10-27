module

public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionAssemblyDefs
import CFSG.LocalAnalysis.ComponentClassification.M12CoverRigid
import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernel
import CFSG.LocalAnalysis.ComponentClassification.J2CoverRigid
import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernel

public section

namespace CFSG.ComponentClassification.StandardRecognition

open CFSG.Assembly

theorem m12J2DoubleCoverExclusion :
    M12J2DoubleCoverExclusion :=
  m12J2DoubleCoverExclusion_of_local
    (m12J2LocalKernel_of M12Cover.ctss_m12_central_double_cover_local_kernel_frontier
      J2Cover.ctss_j2_central_double_cover_local_kernel_frontier)
    (m12J2LocalInvolutionData_of_data M12Cover.internalSylowData_M12 J2Cover.internalSylowData_J2
      M12Cover.ctss_m12_central_double_cover_external_data_from_fusion_and_section
      J2Cover.ctss_j2_central_double_cover_external_involution_data_frontier)

theorem center_eq_bot_of_m12_or_j2 (hMJ : M12J2DoubleCoverExclusion)
    (hMJBound : M12J2CentralTwoGroupOrderBound) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : Assembly.KProper Assembly.InCatalog G) {L : Subgroup G}
    (hL : Assembly.ComponentType.IsStandardSubgroup L)
    (hcore : ∀ x : G, orderOf x = 2 → Assembly.oddCore (Subgroup.centralizer ({x} : Set G)) = ⊥)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (Subgroup.centralizer (L : Set G))))
    (h2 : IsPGroup 2 (Subgroup.center L))
    (hQ : Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .M12 ∨
      Blueprint.NativeSporadic.IsSporadic (L ⧸ Subgroup.center L) .J2) :
    Subgroup.center L = ⊥ := by
  by_contra hne
  have hle := hMJBound L hL.1 h2 hQ
  have hpos : 0 < Nat.card (Subgroup.center L) := Nat.card_pos
  have hne1 : Nat.card (Subgroup.center L) ≠ 1 := fun h => hne (Subgroup.card_eq_one.mp h)
  exact hMJ G hnonab hK L hL hcore S hS (by omega) hQ

end CFSG.ComponentClassification.StandardRecognition
