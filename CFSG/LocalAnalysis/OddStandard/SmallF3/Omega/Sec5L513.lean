module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Prod
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B513Norm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5InputsB3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem sec5b513_orderOf_conj {x u : G} (hu : u * u = 1) (hu1 : u ≠ 1) :
    orderOf (x⁻¹ * u * x) = 2 := by
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  rw [← hu2]
  exact (SemiconjBy.orderOf_eq x⁻¹ (by
    show x⁻¹ * u = (x⁻¹ * u * x) * x⁻¹
    group)).symm

private theorem sec5b513_deltaT (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {x : G} (hx : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    x⁻¹ * t * x ∈ DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) := by
  have hxC : x ∈ centralizer ({z} : Set G) :=
    (sup_le c.K₃_le_centralizer c.K₄_le_centralizer) hx
  have ht : t ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := c.t_mem_sup₃₄
  refine ⟨sec5b513_orderOf_conj c.t_mul_self c.t_ne_one, ?_, ?_⟩
  · intro hconj
    have hzx : z * x = x * z := Subgroup.mem_centralizer_iff.mp hxC z rfl
    have hxzx : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [← hzx]
        _ = z := by rw [mul_assoc, mul_inv_cancel, mul_one]
    have htz : t = z := by
      calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
        _ = x * z * x⁻¹ := by rw [hconj]
        _ = z := hxzx
    exact c.t_ne_z h37 htz
  · exact mul_mem (mul_mem (inv_mem hx) ht) hx

private theorem sec5b513_comm_mem_normalizer (h37 : Asc82Lemma37) (f : Asc82Fact513Comm)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {y : G} (hy : y ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h)
    (hcomm : (y⁻¹ * t * y) * t = t * (y⁻¹ * t * y)) :
    y ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
  (sec5b513_conjugate_eq_iff).mp (f G t L S z r B A K₁ K₂ h c y hy (sec5b513_deltaT h37 c hy)
    hcomm)

private theorem sec5b513_P_le_N (h37 : Asc82Lemma37) (f : Asc82Fact513Comm)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {g : G} (hg : g ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    g ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  obtain ⟨y₁, hy₁, y₂, hy₂, hcomm₁, hcomm₂, hg_eq⟩ :=
    sec5b513_gen (Classical.choice c.iso₃) (Classical.choice c.iso₄) c.comm₃₄
      c.z_mem_K₃ c.z_mem_K₄ c.z_mul_self c.z_ne_one c.t_mem_sup₃₄ c.t_mul_self c.t_ne_one
      (c.t_ne_z h37) hg
  rw [hg_eq]
  exact mul_mem (sec5b513_comm_mem_normalizer h37 f c hy₁ hcomm₁)
    (sec5b513_comm_mem_normalizer h37 f c hy₂ hcomm₂)

private theorem sec5b513_mem_normalizer_of_centralizers (h36 : Asc82Lemma36)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {g : G} (hgt : g ∈ centralizer ({t} : Set G)) (hgz : g ∈ centralizer ({z} : Set G)) :
    g ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  have hL : g ∈ normalizer (L : Set G) := sec4_mem_normalizer h36 c.toSec3SettingLB g hgt
  have hC : g ∈ normalizer ((centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer hgz
  have hinf : g ∈ normalizer ((L ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    sec5b513_mem_normalizer_inf hL hC
  have htwo : g ∈ normalizer ((twoRes (L ⊓ centralizer ({z} : Set G)) : Subgroup G) : Set G) :=
    sec5b513_mem_normalizer_twoRes hinf
  rwa [← c.prod] at htwo

theorem asc82Lemma513_of (h36 : Asc82Lemma36) (h37 : Asc82Lemma37) (f : Asc82Fact513Comm) :
    Asc82Lemma513 := by
  intro G _ _ t L S z r B A K₁ K₂ h c x hxz hxd
  have ht'2 : (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1 := by
    rw [← pow_two, ← hxd.1, pow_orderOf_eq_one]
  have ht'1 : x⁻¹ * t * x ≠ 1 := by
    intro h1
    have h2 : orderOf (x⁻¹ * t * x) = 2 := hxd.1
    rw [h1, orderOf_one] at h2
    omega
  obtain ⟨y, hy, hyeq⟩ :=
    sec5b513_trans (Classical.choice c.iso₃) (Classical.choice c.iso₄) c.comm₃₄
      c.z_mem_K₃ c.z_mem_K₄ c.z_mul_self c.z_ne_one c.t_mem_sup₃₄ c.t_mul_self c.t_ne_one
      (c.t_ne_z h37) hxd.2.2 ht'2 ht'1 hxd.2.1
  have hyz : y ∈ centralizer ({z} : Set G) :=
    (sup_le c.K₃_le_centralizer c.K₄_le_centralizer) hy
  have hyN : y ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
    sec5b513_P_le_N h37 f c hy
  have hc0t : x * y⁻¹ ∈ centralizer ({t} : Set G) := by
    have hconj : (x * y⁻¹)⁻¹ * t * (x * y⁻¹) = t := by
      rw [show (x * y⁻¹)⁻¹ * t * (x * y⁻¹) = y * (x⁻¹ * t * x) * y⁻¹ from by group, ← hyeq]
      group
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * y⁻¹ * t = (x * y⁻¹) * ((x * y⁻¹)⁻¹ * t * (x * y⁻¹)) := by rw [hconj]
      _ = t * (x * y⁻¹) := by group
  have hc0z : x * y⁻¹ ∈ centralizer ({z} : Set G) := mul_mem hxz (inv_mem hyz)
  have hc0N : x * y⁻¹ ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) :=
    sec5b513_mem_normalizer_of_centralizers h36 c hc0t hc0z
  have hxN : x ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    have hxy : x * y⁻¹ * y = x := by group
    rw [← hxy]
    exact mul_mem hc0N hyN
  refine ⟨?_, ?_⟩
  · rw [← sec5b513_conjugate_inf_centralizer L hxz, sec5b513_twoRes_conjugate, ← c.prod,
      (sec5b513_conjugate_eq_iff).mpr hxN]
  · exact (sec5b513_conjugate_eq_iff).mpr hxN

end CFSG.OddStandard.SmallF3.Omega
