module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6B0b
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {A C0 V : Subgroup G} {a₁ b₁ a₂ b₂ z t u : G}

private lemma mem_normalizer_of_conj {H : Subgroup G} {x : G}
    (h1 : ∀ c ∈ H, x * c * x⁻¹ ∈ H) (h2 : ∀ c ∈ H, x⁻¹ * c * x ∈ H) :
    x ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro c
  refine ⟨h1 c, fun hc => ?_⟩
  have h := h2 (x * c * x⁻¹) hc
  rwa [show x⁻¹ * (x * c * x⁻¹) * x = c by group] at h

theorem y6_X_le_NAV (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    normalizer ((A ⊔ C0 : Subgroup G) : Set G) ⊓ normalizer (V : Set G) ≤
      normalizer ((A ⊔ V : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxN1, hxNV⟩ := hx
  have key : ∀ y : G, y ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) →
      y ∈ normalizer (V : Set G) → ∀ c ∈ A ⊔ V, y * c * y⁻¹ ∈ A ⊔ V := by
    intro y hy1 hyV c hc
    have hcC1 : c ∈ A ⊔ C0 := (sup_le_sup_left (y6_V_le_C0 h) A) hc
    have hc' : y * c * y⁻¹ ∈ A ⊔ C0 := (Subgroup.mem_set_normalizer_iff.mp hy1 c).mp hcC1
    refine (y6_cent_C1_V h (y * c * y⁻¹) hc').mp ?_
    intro v hv
    have hv' : y⁻¹ * v * y ∈ V := (Subgroup.mem_set_normalizer_iff''.mp hyV v).mp hv
    have hcv : c * (y⁻¹ * v * y) = (y⁻¹ * v * y) * c :=
      (y6_cent_C1_V h c hcC1).mpr hc (y⁻¹ * v * y) hv'
    calc (y * c * y⁻¹) * v = y * (c * (y⁻¹ * v * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * v * y) * c) * y⁻¹ := by rw [hcv]
      _ = v * (y * c * y⁻¹) := by group
  refine mem_normalizer_of_conj (key x hxN1 hxNV) ?_
  simpa using (key x⁻¹ (Subgroup.inv_mem _ hxN1) (Subgroup.inv_mem _ hxNV))

theorem y6_NAV_le_NV (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    normalizer ((A ⊔ V : Subgroup G) : Set G) ≤ normalizer (V : Set G) := by
  intro x hx
  have key : ∀ y : G, y ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) →
      ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    intro y hy v hv
    have hyv : y * v * y⁻¹ ∈ A ⊔ V :=
      (Subgroup.mem_set_normalizer_iff.mp hy v).mp (Subgroup.mem_sup_right hv)
    refine y6_cen_AV h (y * v * y⁻¹) hyv ?_
    intro w hw
    have hw' : y⁻¹ * w * y ∈ A ⊔ V := (Subgroup.mem_set_normalizer_iff''.mp hy w).mp hw
    have hw'C1 : y⁻¹ * w * y ∈ A ⊔ C0 := (sup_le_sup_left (y6_V_le_C0 h) A) hw'
    have hcomm : v * (y⁻¹ * w * y) = (y⁻¹ * w * y) * v :=
      ((y6_cent_C1_V h (y⁻¹ * w * y) hw'C1).mpr hw' v hv).symm
    calc (y * v * y⁻¹) * w = y * (v * (y⁻¹ * w * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * w * y) * v) * y⁻¹ := by rw [hcomm]
      _ = w * (y * v * y⁻¹) := by group
  refine mem_normalizer_of_conj (key x hx) ?_
  simpa using (key x⁻¹ (Subgroup.inv_mem _ hx))

theorem y6_C1_le_Kp (h : Y6Cfg A C0 V a₁ b₁ a₂ b₂ z t u) :
    A ⊔ C0 ≤ CFSG.GH74.GLS.centralizerSection (A ⊔ V) V := by
  intro c hc
  have hcNV : c ∈ normalizer (V : Set G) := y6_C1_le_N_V h hc
  have hcN1 : c ∈ normalizer ((A ⊔ C0 : Subgroup G) : Set G) := Subgroup.le_normalizer hc
  have hcNAV : c ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) :=
    y6_X_le_NAV h (Subgroup.mem_inf.mpr ⟨hcN1, hcNV⟩)
  refine ⟨hcNAV, hcNV, fun k hk => ?_⟩
  have hkC1 : k ∈ A ⊔ C0 := (sup_le_sup_left (y6_V_le_C0 h) A) hk
  exact (Subgroup.zpowers_le.mpr (y6_z_mem_V h)) (y6_comm_C1 h k hkC1 c hc)

end CFSG.OddStandard.HigherRank.YamadaG23
