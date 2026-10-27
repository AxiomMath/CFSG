module

public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.GroupTheory

open CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isSylowOf_of_fusion_trivial_center {z : G} {M Y : Subgroup G}
    (hY : IsSylowOf p Y (Subgroup.centralizer ({z} : Set G) ⊓ M))
    (hzY : z ∈ Y ⊓ Subgroup.centralizer (Y : Set G))
    (hfus : ∀ g : G, g * z * g⁻¹ ∈ Y ⊓ Subgroup.centralizer (Y : Set G) → g * z * g⁻¹ = z) :
    IsSylowOf p Y M := by
  refine isSylowOf_of_normalizer_inf_le hY ?_
  intro n hn
  obtain ⟨hnN, -⟩ := Subgroup.mem_inf.mp hn
  have hnz : n * z * n⁻¹ ∈ Y ⊓ Subgroup.centralizer (Y : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hnN z).mp
      (Subgroup.mem_inf.mp hzY).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ Y := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hnN) y).mp hy
      simpa using h1
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzY).2 _ hy'
    calc y * (n * z * n⁻¹) = n * ((n⁻¹ * y * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * y * n)) * n⁻¹ := by rw [hc]
      _ = (n * z * n⁻¹) * y := by group
  have hnz' := hfus n hnz
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [hnz']

end CFSG.GroupTheory
