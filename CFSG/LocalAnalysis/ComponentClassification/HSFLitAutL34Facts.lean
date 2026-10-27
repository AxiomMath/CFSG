module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Make
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsCov
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5InputsRank
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs58
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Real3

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.UnbalancedLayer Subgroup

theorem l34AutRankFact :
    L34AutRankFact := by
  intro G _ _ K E hK hL hE hEe
  obtain ⟨ρ⟩ := exists_real hK hL
  exact ρ.rank hE hEe

theorem l34UnitaryAutFact :
    L34UnitaryAutFact := by
  intro G _ _ K R x hK hL hx hR2 hR
  obtain ⟨ρ, hρ⟩ := exists_real_unitary hK hL hx
  exact ρ.unitary hx.1 hρ hR2 hR

theorem l34AutRankOneNormalFact :
    L34AutRankOneNormalFact := by
  intro G _ _ L S D hL hT hS hDS hSD hDC hD
  obtain ⟨ρ⟩ := exists_real hL hT
  exact ρ.card_le_two hS hDS hSD hDC hD

theorem l34AutSylowCenterFact_of
    (hEC : L34ElementaryCenterSylowFact) : L34AutSylowCenterFact := by
  intro G _ _ K S hK hL hS hZ
  obtain ⟨ρ⟩ := exists_real hK hL
  have hP : IsSylowTwoIn (S ⊓ K) K := GrS4.isSylowTwoIn_inf hS
  have hZ' : ∀ z ∈ S ⊓ K ⊓ zStarIn K, z * z = 1 := fun z hz =>
    hZ z (mem_inf.2 ⟨(mem_inf.1 (mem_inf.1 hz).1).1, (mem_inf.1 hz).2⟩)
  obtain ⟨-, hcard, -⟩ := hEC G K (S ⊓ K) hK hL hP hZ'
  exact ⟨fun y hy S₁ hS₁ hc hcomm => ρ.mem_center_sup hS hcard hy hS₁ hc hcomm,
    fun E hCE hES hSE hEe h8 => ρ.center_le hS hCE hES hSE hEe h8⟩

theorem l34AutSylowCenterFact :
    L34AutSylowCenterFact :=
  l34AutSylowCenterFact_of elementaryCenterSylow

end CFSG.ComponentClassification.HSFLit.AutL34
