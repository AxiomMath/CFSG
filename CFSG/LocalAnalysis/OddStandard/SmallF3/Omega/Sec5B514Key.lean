module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B514Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5BCentProd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem sec5b_K514_twoRes_le (H : Subgroup G) : twoRes H ≤ H := by
  rw [twoRes]
  exact (Subgroup.closure_le H).mpr fun _ hx => hx.1

private theorem sec5b_K514_orderOf_conj {x u : G} (hu : u * u = 1) (hu1 : u ≠ 1) :
    orderOf (x⁻¹ * u * x) = 2 := by
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu) hu1
  rw [← hu2]
  exact (SemiconjBy.orderOf_eq x⁻¹ (by
    show x⁻¹ * u = (x⁻¹ * u * x) * x⁻¹
    group)).symm

private theorem sec5b_K514_deltaT (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {x : G} (hx : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    x⁻¹ * t * x ∈ DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) := by
  have hxC : x ∈ centralizer ({z} : Set G) :=
    (sup_le c.K₃_le_centralizer c.K₄_le_centralizer) hx
  have ht : t ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := c.t_mem_sup₃₄
  refine ⟨sec5b_K514_orderOf_conj c.t_mul_self c.t_ne_one, ?_, ?_⟩
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

private theorem sec5b_K514_513' (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {x : G}
    (hxC : x ∈ centralizer ({z} : Set G))
    (hxd : x⁻¹ * t * x ∈ DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h)) :
    twoRes (CFSG.conjugate L x ⊓ centralizer ({z} : Set G)) = K₁ ⊔ K₂ ∧
      CFSG.conjugate (K₁ ⊔ K₂) x = K₁ ⊔ K₂ :=
  h513 G t L S z r B A K₁ K₂ h c x hxC hxd

private theorem sec5b_K514_513 (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {x : G} (hx : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    twoRes (CFSG.conjugate L x ⊓ centralizer ({z} : Set G)) = K₁ ⊔ K₂ ∧
      CFSG.conjugate (K₁ ⊔ K₂) x = K₁ ⊔ K₂ :=
  sec5b_K514_513' h513 c ((sup_le c.K₃_le_centralizer c.K₄_le_centralizer) hx)
    (sec5b_K514_deltaT h37 c hx)

private theorem sec5b_K514_centralizes_class (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {x : G} (hx : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h)
    {a : G} (ha : a ∈ K₁ ⊔ K₂) :
    a * (x⁻¹ * t * x) = (x⁻¹ * t * x) * a := by
  have hR : twoRes (CFSG.conjugate L x ⊓ centralizer ({z} : Set G)) = K₁ ⊔ K₂ :=
    (sec5b_K514_513 h37 h513 c hx).1
  have ha' : a ∈ twoRes (CFSG.conjugate L x ⊓ centralizer ({z} : Set G)) := by
    rw [hR]; exact ha
  have haL : a ∈ CFSG.conjugate L x :=
    ((sec5b_K514_twoRes_le _).trans inf_le_left) ha'
  have hmemL : x * a * x⁻¹ ∈ L := sec5b_mem_conjugate_iff.mp haL
  have hcomm : t * (x * a * x⁻¹) = (x * a * x⁻¹) * t :=
    Subgroup.mem_centralizer_iff.mp (c.L_le_centralizer hmemL) t rfl
  have h1 : x⁻¹ * (t * (x * a * x⁻¹)) * x = x⁻¹ * ((x * a * x⁻¹) * t) * x := by
    rw [hcomm]
  rw [show x⁻¹ * (t * (x * a * x⁻¹)) * x = x⁻¹ * t * x * a from by group,
      show x⁻¹ * ((x * a * x⁻¹) * t) * x = a * x⁻¹ * t * x from by group] at h1
  rw [show a * (x⁻¹ * t * x) = a * x⁻¹ * t * x from by group]
  exact h1.symm

private theorem sec5b_K514_mem_conj (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {x : G} (hx : x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h)
    {a : G} (ha : a ∈ K₁ ⊔ K₂) :
    x * a * x⁻¹ ∈ K₁ ⊔ K₂ ∧ x⁻¹ * a * x ∈ K₁ ⊔ K₂ := by
  have hR : CFSG.conjugate (K₁ ⊔ K₂) x = K₁ ⊔ K₂ := (sec5b_K514_513 h37 h513 c hx).2
  exact ⟨sec5b_mem_of_conjugate_eq hR ha, sec5b_mem_of_conjugate_eq' hR ha⟩

private theorem sec5b_K514_mem_A34 (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {a : G} (ha : a ∈ K₁ ⊔ K₂)
    {b : G} (hb : b ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    a * b * a⁻¹ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := by
  have hb' : b ∈ CFSG.conjugate (K₁ ⊔ K₂) h := by
    rw [sec5b_conjugate_sup]; exact hb
  have hbA12 : h * b * h⁻¹ ∈ K₁ ⊔ K₂ := sec5b_mem_conjugate_iff.mp hb'
  have hhhC : h * h ∈ centralizer ({z} : Set G) := mul_mem c.h_z c.h_z
  have hhh_t : (h * h)⁻¹ * t * (h * h) ∈
      DeltaT5 z (CFSG.conjugate K₁ h) (CFSG.conjugate K₂ h) := by
    have heq : (h * h)⁻¹ * t * (h * h) = t := by
      have htcomm : t * (h * h) = (h * h) * t :=
        Subgroup.mem_centralizer_iff.mp c.h_sq t rfl
      calc (h * h)⁻¹ * t * (h * h) = (h * h)⁻¹ * (t * (h * h)) := by group
        _ = (h * h)⁻¹ * ((h * h) * t) := by rw [htcomm]
        _ = t := by group
    rw [heq]
    exact ⟨orderOf_eq_prime (by rw [pow_two]; exact c.t_mul_self) c.t_ne_one,
      c.t_ne_z h37, c.t_mem_sup₃₄⟩
  have hR2 : CFSG.conjugate (K₁ ⊔ K₂) (h * h) = K₁ ⊔ K₂ :=
    (sec5b_K514_513' h513 c hhhC hhh_t).2
  have hhha : (h * h) * a * (h * h)⁻¹ ∈ K₁ ⊔ K₂ :=
    sec5b_mem_of_conjugate_eq hR2 ha
  have hha : h * a * h⁻¹ ∈ CFSG.conjugate (K₁ ⊔ K₂) h :=
    sec5b_mem_conjugate_iff.mpr (by
      rw [show h * (h * a * h⁻¹) * h⁻¹ = (h * h) * a * (h * h)⁻¹ from by group]
      exact hhha)
  rw [sec5b_conjugate_sup] at hha
  have hwA12 : (h * a * h⁻¹) * (h * b * h⁻¹) * (h * a * h⁻¹)⁻¹ ∈ K₁ ⊔ K₂ :=
    (sec5b_K514_mem_conj h37 h513 c hha hbA12).1
  rw [← sec5b_conjugate_sup]
  exact sec5b_mem_conjugate_iff.mpr (by
    rw [show h * (a * b * a⁻¹) * h⁻¹ =
        (h * a * h⁻¹) * (h * b * h⁻¹) * (h * a * h⁻¹)⁻¹ from by group]
    exact hwA12)

private theorem sec5b_K514_inf_zpowers (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {y : G} (hy12 : y ∈ K₁ ⊔ K₂)
    (hy34 : y ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    y ∈ zpowers z := by
  have hyc : ∀ x ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h,
      y * (x⁻¹ * t * x) = (x⁻¹ * t * x) * y :=
    fun x hx => sec5b_K514_centralizes_class h37 h513 c hx hy12
  have h := sec5b_centProd_cent (K₃ := CFSG.conjugate K₁ h) (K₄ := CFSG.conjugate K₂ h)
    (Classical.choice c.iso₃) (Classical.choice c.iso₄) c.comm₃₄ c.z_mem_K₃ c.z_mem_K₄
    c.z_mul_self c.z_ne_one c.t_mem_sup₃₄ c.t_mul_self c.t_ne_one (c.t_ne_z h37)
    hy34 hyc
  rcases h with h1 | hz
  · rw [h1]; exact one_mem _
  · rw [hz]; exact Subgroup.mem_zpowers z

private theorem sec5b_K514_commutator_zpowers (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {a : G} (ha : a ∈ K₁ ⊔ K₂)
    {b : G} (hb : b ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    a * b * a⁻¹ * b⁻¹ ∈ zpowers z := by
  have hb_inv : b⁻¹ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := inv_mem hb
  have h1 : b * a⁻¹ * b⁻¹ ∈ K₁ ⊔ K₂ :=
    (sec5b_K514_mem_conj h37 h513 c hb (inv_mem ha)).1
  have h2 : a * b * a⁻¹ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h :=
    sec5b_K514_mem_A34 h37 h513 c ha hb
  have hA12 : a * b * a⁻¹ * b⁻¹ ∈ K₁ ⊔ K₂ := by
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) from by group]
    exact mul_mem ha h1
  have hA34 : a * b * a⁻¹ * b⁻¹ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h :=
    mul_mem h2 hb_inv
  exact sec5b_K514_inf_zpowers h37 h513 c hA12 hA34

private theorem sec5b_K514_centralizer (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h)
    {b : G} (hb : b ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h) :
    K₁ ⊔ K₂ ≤ centralizer ({b} : Set G) := by
  have hprod : K₁ ⊔ K₂ = twoRes (L ⊓ centralizer ({z} : Set G)) := c.prod
  rw [hprod]
  unfold twoRes
  apply (Subgroup.closure_le (centralizer ({b} : Set G))).mpr
  intro g hg
  rcases hg with ⟨hgL, hgodd⟩
  have hgA12 : g ∈ K₁ ⊔ K₂ := by
    rw [hprod]
    exact Subgroup.subset_closure ⟨hgL, hgodd⟩
  have hcommz : g * z = z * g :=
    (Subgroup.mem_centralizer_iff.mp hgL.2 z rfl).symm
  have hc := sec5b_K514_commutator_zpowers h37 h513 c hgA12 hb
  have hgb := sec5b_commute_of_odd c.z_mul_self hgodd hcommz hc
  exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hgb.symm)

theorem sec5b_514_key (h37 : Asc82Lemma37) (h513 : Asc82Lemma513)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ⁅K₁ ⊔ K₂, CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h⁆ = ⊥ := by
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact Subgroup.mem_centralizer_iff.mp (sec5b_K514_centralizer h37 h513 c hb ha) b rfl

end CFSG.OddStandard.SmallF3.Omega
