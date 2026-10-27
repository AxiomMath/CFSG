module

public import CFSG.StronglyEmbedded.UniqueCosetEnd
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.StronglyEmbedded.UniqueCoset

theorem not_isSolvable_of_isClassical2A7 {G : Type} [Group G] {K : Subgroup G} {z : G}
    (hK : Hat2A7.IsClassical2A7 ⊤ K z) : ¬ Group.IsSolvable ↥K := fun hsolv => by
  have hs : Group.IsSolvable (↥K ⧸ classicalInvolutionOddCore ↥K) :=
    Group.isSolvable_of_surjective
      (f := QuotientGroup.mk' (classicalInvolutionOddCore ↥K)) (QuotientGroup.mk'_surjective _)
  exact not_isSolvable_of_open_isQuasisimple hK.witness.1 hs


theorem false_of_uniqueCoset_of_nonsolvable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} {z : G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {K : Subgroup G} (hKc : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKs : ¬ Group.IsSolvable ↥K) : False := by
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
  exact false_of_uniqueCoset_of_not_isSolvable hH hz h1 h2 hTs hTnab hTc hKc hKs

theorem false_of_uniqueCoset_a7 {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} {z : G} (hH : H ≠ ⊤)
    (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {K : Subgroup G} (hK : Hat2A7.IsClassical2A7 ⊤ K z) : False :=
  false_of_uniqueCoset_of_nonsolvable hnab hH hz h1 h2 hK.le_centralizer
    (not_isSolvable_of_isClassical2A7 hK)

end CFSG.ClassicalInvolution.Hat2A7S
