module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888Pair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem Sec5HCtx.pair₁₂ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : Sec5Pair K₁ K₂ z :=
  Sec5Pair.of_kctx c.toSec5KCtx

theorem Sec5HCtx.pair₃₄ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Sec5Pair (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) z :=
  ⟨c.comm₃₄, c.iso₃, c.iso₄, c.z_mem_K₃, c.z_mem_K₄, c.z_mul_self, c.z_ne_one⟩

theorem Sec5HCtx.K_le (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    K₁ ⊔ K₂ ≤ L ⊓ centralizer ({z} : Set G) :=
  sup_le c.pocket₁.2.1 c.pocket₂.2.1

theorem Sec5HCtx.z_mem_L (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∈ L :=
  (Subgroup.mem_inf.mp (c.pocket₁.2.1 c.z_mem_K₁)).1

theorem Sec5HCtx.t_comm_z (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t * z = z * t :=
  (Subgroup.mem_centralizer_singleton_iff.mp (c.L_le_centralizer c.z_mem_L)).symm

theorem Sec5HCtx.t_mem_A (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ∈ A := by
  rw [c.A_eq]
  exact Subgroup.mem_sup_right c.B_split.1

theorem Sec5HCtx.P_le_cent (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h ≤ centralizer ({z} : Set G) :=
  sup_le c.K₃_le_centralizer c.K₄_le_centralizer

theorem Sec5HCtx.mem_normalizer_of_cent (h36 : Asc82Lemma36)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {g : G} (hgt : g ∈ centralizer ({t} : Set G))
    (hgz : g ∈ centralizer ({z} : Set G)) :
    g ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  have hL : g ∈ normalizer (L : Set G) := sec4_mem_normalizer h36 c.toSec3SettingLB g hgt
  have hC : g ∈ normalizer ((centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hgz
  have hinf : g ∈ normalizer ((L ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    sec5b513_mem_normalizer_inf hL hC
  have htwo : g ∈ normalizer ((twoRes (L ⊓ centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
    sec5b513_mem_normalizer_twoRes hinf
  rwa [← c.prod] at htwo

theorem Sec5HCtx.sq_mem_normalizer (h36 : Asc82Lemma36)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    h * h ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
  c.mem_normalizer_of_cent h36 c.h_sq (mul_mem c.h_z c.h_z)

theorem Sec5HCtx.K_odd_mem (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {g : G}
    (hg : g ∈ L ⊓ centralizer ({z} : Set G)) (hodd : Odd (orderOf g)) : g ∈ K₁ ⊔ K₂ := by
  rw [c.prod]
  exact Subgroup.subset_closure ⟨hg, hodd⟩

theorem Sec5HCtx.A_inf_K_cent_P (h36 : Asc82Lemma36) (hMA : Asc82Fact513AModel)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {y p : G} (hyA : y ∈ A) (hyK : y ∈ K₁ ⊔ K₂)
    (hp : p ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) : y * p = p * y := by
  have hsq : h * h ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := c.sq_mem_normalizer h36
  have hy'A : h * y * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp c.h_mem y).mp hyA
  have hy'P : h * y * h⁻¹ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := by
    rw [← sec5b_conjugate_sup]
    refine sec5b_mem_conjugate_iff.mpr ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hsq y).mp hyK
    rwa [show h * (h * y * h⁻¹) * h⁻¹ = h * h * y * (h * h)⁻¹ from by group]
  have hy'C := hMA G t L S z r B A K₁ K₂ h c (Subgroup.mem_inf.mpr ⟨hy'A, hy'P⟩)
  have hp' : h * p * h⁻¹ ∈ K₁ ⊔ K₂ := by
    rw [← sec5b_conjugate_sup] at hp
    exact sec5b_mem_conjugate_iff.mp hp
  have h1 := Subgroup.mem_centralizer_iff.mp hy'C (h * p * h⁻¹) hp'
  have h2 : h * (p * y) * h⁻¹ = h * (y * p) * h⁻¹ := by
    calc h * (p * y) * h⁻¹ = h * p * h⁻¹ * (h * y * h⁻¹) := by group
      _ = h * y * h⁻¹ * (h * p * h⁻¹) := h1
      _ = h * (y * p) * h⁻¹ := by group
  exact (mul_left_cancel (mul_right_cancel h2)).symm

end CFSG.OddStandard.SmallF3.Omega
