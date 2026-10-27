module

public import CFSG.ClassicalInvolution.Q3.Q3T7EndF3
public import CFSG.GH74.Uniqueness.Section165GapFinal
public import CFSG.StronglyEmbedded.UniqueCosetZD

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.StronglyEmbedded.UniqueCoset CFSG.GH74.Uniqueness

theorem false_of_uniqueCoset_of_weakMember3_F {G : Type} [Group G] [Finite G] {F : Subgroup G}
    [F.Normal] (hFs : IsSimpleGroup ↥F) (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x)
    (hFc : Subgroup.centralizer (F : Set G) = ⊥) {H : Subgroup G} {z : G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {K : Subgroup G} (hK : Q3.IsClassicalMember3 K z) : False := by
  obtain ⟨hLF, hLB, -⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz hFs hFnab hFc
    (L := Subgroup.closure (conjugatesOf z)) rfl
    (S_ZD_unconditional G (conjugatesOf z) H (isInvariantInvolutionSet hz)
      (isProductDisconnected hH hz h1 h2))
  have hzF : z ∈ F := by
    rw [← hLF]
    exact Subgroup.subset_closure mem_conjugatesOf_self
  obtain ⟨n, i, e, hT⟩ := Bender.isBenderGroup_iff_exists_benderType.mp hLB
  exact false_of_weakMember_of_benderType hFc
    (hT.of_mulEquiv (MulEquiv.subgroupCongr hLF)) hzF hK

end CFSG.ClassicalInvolution.Q3.Q3T8
