module

public import CFSG.ClassicalInvolution.Q3.Q3T8Bend
public import CFSG.GH74.Uniqueness.Section165GapFinal
public import CFSG.StronglyEmbedded.UniqueCosetZD

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

open CFSG.StronglyEmbedded.UniqueCoset CFSG.GH74.Uniqueness

theorem false_of_uniqueCoset_of_weakMember3 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} {z : G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {K : Subgroup G} (hK : Q3.IsClassicalMember3 K z) : False := by
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  obtain ⟨hLF, hLB, -⟩ := closure_conjugatesOf_eq_and_isBenderGroup hz hTs hTnab hTc
    (L := Subgroup.closure (conjugatesOf z)) rfl
    (S_ZD_unconditional G (conjugatesOf z) H (isInvariantInvolutionSet hz)
      (isProductDisconnected hH hz h1 h2))
  have hBG : CFSG.BenderSuzuki.IsBenderGroup G := by
    obtain ⟨n, i, e, hT⟩ := CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mp hLB
    refine CFSG.GH74.Uniqueness.Bender.isBenderGroup_iff_exists_benderType.mpr
      ⟨n, i, e, hT.of_mulEquiv ((MulEquiv.subgroupCongr hLF).trans Subgroup.topEquiv)⟩
  exact false_of_isBenderGroup_weakMember hBG hK

end CFSG.ClassicalInvolution.Q3.Q3T8
