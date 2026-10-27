module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisTools

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem centralizer_conj (g v : G) :
    centralizer ({g⁻¹ * v * g} : Set G) =
      (centralizer ({v} : Set G)).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, mem_centralizer_singleton_iff.mpr ?_, by
      change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x; group⟩
    have h := mem_centralizer_singleton_iff.mp hx
    calc g * x * g⁻¹ * v = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by rw [h]
      _ = v * (g * x * g⁻¹) := by group
  · rintro ⟨y, hy, rfl⟩
    have h := mem_centralizer_singleton_iff.mp hy
    rw [mem_centralizer_singleton_iff]
    change g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * v * g) = g⁻¹ * v * g * (g⁻¹ * y * g⁻¹⁻¹)
    calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * v * g) = g⁻¹ * (y * v) * g := by group
      _ = g⁻¹ * (v * y) * g := by rw [h]
      _ = g⁻¹ * v * g * (g⁻¹ * y * g⁻¹⁻¹) := by group

namespace GHSylow

variable (D : GHSylow G)

theorem S_le_centralizer_z : (D.S : Subgroup G) ≤ centralizer ({D.z} : Set G) := fun c hc => by
  rw [mem_centralizer_singleton_iff]
  have h := D.conj_z_S hc
  calc c * D.z = c * (c⁻¹ * D.z * c) := by rw [h]
    _ = D.z * c := by group

theorem isSylowOf_S_centralizer_z [Finite G] :
    IsSylowOf 2 (D.S : Subgroup G) (centralizer ({D.z} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_top D.S).of_le D.S_le_centralizer_z le_top

abbrev Ct : Subgroup G := (D.S : Subgroup G) ⊓ centralizer ({D.t} : Set G)

theorem Zset_subset_Ct {w : G} (hw : w ∈ D.Zset) : w ∈ D.Ct := by
  have hzt : D.z * D.t = D.t * D.z := D.z_comm_t
  rcases hw with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact mem_inf.mpr ⟨D.z_mem_S, mem_centralizer_singleton_iff.mpr hzt⟩
  · exact mem_inf.mpr ⟨D.t_mem_S, mem_centralizer_singleton_iff.mpr rfl⟩
  · refine mem_inf.mpr ⟨mul_mem D.t_mem_S D.z_mem_S, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [mul_assoc, ← hzt, ← mul_assoc]

theorem comm_of_mem_Zset {w : G} (hw : w ∈ D.Zset) {p : G} (hp : p ∈ D.Ct) :
    p * w = w * p := by
  obtain ⟨hpS, hpt⟩ := mem_inf.mp hp
  have hpt' : p * D.t = D.t * p := mem_centralizer_singleton_iff.mp hpt
  have hpz : p * D.z = D.z * p := mem_centralizer_singleton_iff.mp (D.S_le_centralizer_z hpS)
  rcases hw with rfl | rfl | rfl | rfl
  · simp
  · exact hpz
  · exact hpt'
  · rw [← mul_assoc, hpt', mul_assoc, hpz, mul_assoc]

theorem mem_Zset_iff (w : G) :
    w ∈ D.Zset ↔ w ∈ D.Ct ∧ ∀ p ∈ D.Ct, p * w = w * p := by
  constructor
  · intro hw
    exact ⟨D.Zset_subset_Ct hw, fun p hp => D.comm_of_mem_Zset hw hp⟩
  · rintro ⟨hwC, hcomm⟩
    obtain ⟨hwS, hwt⟩ := mem_inf.mp hwC
    obtain ⟨s, rfl⟩ := D.exists_toG hwS
    have hs : s * SE.invRep 1 = SE.invRep 1 * s := by
      have h := mem_centralizer_singleton_iff.mp hwt
      rw [← map_mul, ← map_mul] at h
      exact D.toG_injective h
    have hc : ∀ g : SE, g * SE.invRep 1 = SE.invRep 1 * g → g * s = s * g := by
      intro g hg
      have hgC : D.toG g ∈ D.Ct := mem_inf.mpr ⟨D.toG_mem g, mem_centralizer_singleton_iff.mpr
        (by rw [← map_mul, ← map_mul, hg])⟩
      have h := hcomm _ hgC
      rw [← map_mul, ← map_mul] at h
      exact D.toG_injective h
    rcases SE.center_centralizer_invRep1 s hs hc with rfl | rfl | rfl | rfl
    · rw [map_one]; exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · rw [map_mul]; exact Or.inr (Or.inr (Or.inr rfl))

end GHSylow

end CFSG.ComponentClassification.GHarris
