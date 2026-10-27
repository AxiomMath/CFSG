module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Facts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec5b_mem_conjugate_iff {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rwa [h]
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

theorem sec5b_conjugate_sup (H H' : Subgroup G) (g : G) :
    CFSG.conjugate (H ⊔ H') g = CFSG.conjugate H g ⊔ CFSG.conjugate H' g := by
  unfold CFSG.conjugate
  exact Subgroup.map_sup _ _ _

theorem sec5b_mem_of_conjugate_eq {H : Subgroup G} {x : G} (hx : CFSG.conjugate H x = H)
    {a : G} (ha : a ∈ H) : x * a * x⁻¹ ∈ H :=
  sec5b_mem_conjugate_iff.mp (hx.symm ▸ ha)

theorem sec5b_mem_of_conjugate_eq' {H : Subgroup G} {x : G} (hx : CFSG.conjugate H x = H)
    {a : G} (ha : a ∈ H) : x⁻¹ * a * x ∈ H := by
  rw [← hx]
  refine sec5b_mem_conjugate_iff.mpr ?_
  have h : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
  rw [h]
  exact ha

private lemma sec5b_comm_pow_aux {g b : G}
    (hgc : Commute g (g * b * g⁻¹ * b⁻¹)) (n : ℕ) :
    g ^ n * b * (g ^ n)⁻¹ * b⁻¹ = (g * b * g⁻¹ * b⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : g ^ (n + 1) * b * (g ^ (n + 1))⁻¹ * b⁻¹
        = g * (g ^ n * b * (g ^ n)⁻¹ * b⁻¹) * g⁻¹ * (g * b * g⁻¹ * b⁻¹) := by
      rw [pow_succ']
      group
    rw [h1, ih]
    have h2 : g * (g * b * g⁻¹ * b⁻¹) ^ n * g⁻¹ = (g * b * g⁻¹ * b⁻¹) ^ n := by
      have hcomm := (hgc.pow_right n).eq
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [h2, ← pow_succ]

theorem sec5b_commute_of_odd {z g b : G} (hz : z * z = 1) (hg : Odd (orderOf g))
    (hgz : g * z = z * g) (hc : g * b * g⁻¹ * b⁻¹ ∈ zpowers z) : g * b = b * g := by
  have hcg : Commute g (g * b * g⁻¹ * b⁻¹) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hk]
    exact (show Commute g z from hgz).zpow_right k
  have hc2 : (g * b * g⁻¹ * b⁻¹) * (g * b * g⁻¹ * b⁻¹) = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hk]
    have hz2 : z ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, zpow_add, zpow_one, hz]
    calc z ^ k * z ^ k = z ^ (k + k) := (zpow_add z k k).symm
      _ = z ^ (2 * k) := by rw [show k + k = 2 * k by ring]
      _ = (z ^ (2 : ℤ)) ^ k := zpow_mul z 2 k
      _ = 1 := by rw [hz2, one_zpow]
  have h1 : (g * b * g⁻¹ * b⁻¹) ^ (orderOf g) = 1 := by
    rw [← sec5b_comm_pow_aux hcg (orderOf g), pow_orderOf_eq_one]
    group
  obtain ⟨m, hm⟩ := hg
  have hc1 : g * b * g⁻¹ * b⁻¹ = 1 := by
    have h2 : (g * b * g⁻¹ * b⁻¹) ^ (2 * m + 1) = 1 := by rwa [hm] at h1
    rw [pow_succ, pow_mul, pow_two, hc2, one_pow, one_mul] at h2
    exact h2
  have hgb : g * b = b * g := by
    have h3 : g * b * g⁻¹ = b := by
      have := congrArg (· * b) hc1
      simpa [mul_assoc] using this
    have := congrArg (· * g) h3
    simpa [mul_assoc] using this
  exact hgb

section Ctx

variable [Finite G] {t : G} {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G} {h : G}

theorem Sec5HCtx.z_mem_K₁ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∈ K₁ :=
  c.pocket₁.1

theorem Sec5HCtx.z_mem_K₂ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∈ K₂ :=
  c.pocket₂.1

theorem Sec5HCtx.z_mul_self (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z * z = 1 := by
  have h : orderOf z = 2 := c.pocket.1
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem Sec5HCtx.z_ne_one (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ≠ 1 := by
  intro hz1
  have h : orderOf z = 2 := c.pocket.1
  rw [hz1, orderOf_one] at h
  omega

theorem Sec5HCtx.t_mul_self (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t * t = 1 := by
  have h : orderOf t = 2 := c.involution
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem Sec5HCtx.t_ne_one (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ≠ 1 := by
  intro ht1
  have h : orderOf t = 2 := c.involution
  rw [ht1, orderOf_one] at h
  omega

theorem Sec5HCtx.t_ne_z (h37 : Asc82Lemma37) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ≠ z := by
  intro htz
  exact sec5_t_not_conj_z h37 c.toSec5Ctx 1 (by rw [htz]; simp)

theorem Sec5HCtx.L_le_centralizer (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    L ≤ centralizer ({t} : Set G) :=
  c.component.1

theorem Sec5HCtx.comm₁₂ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
  intro a ha b hb
  have hmem : ⁅a, b⁆ ∈ ⁅K₁, K₂⁆ := Subgroup.commutator_mem_commutator ha hb
  rw [c.comm, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem Sec5HCtx.z_mem_K₃ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    z ∈ CFSG.conjugate K₁ h := by
  rw [sec5b_mem_conjugate_iff]
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  have hz' : h * z * h⁻¹ = z := by rw [hhz]; group
  rw [hz']
  exact c.z_mem_K₁

theorem Sec5HCtx.z_mem_K₄ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    z ∈ CFSG.conjugate K₂ h := by
  rw [sec5b_mem_conjugate_iff]
  have hhz : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp c.h_z
  have hz' : h * z * h⁻¹ = z := by rw [hhz]; group
  rw [hz']
  exact c.z_mem_K₂

theorem Sec5HCtx.K₃_le_centralizer (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    CFSG.conjugate K₁ h ≤ centralizer ({z} : Set G) := by
  intro x hx
  have hxK : h * x * h⁻¹ ∈ K₁ := sec5b_mem_conjugate_iff.mp hx
  have hxKc : h * x * h⁻¹ ∈ centralizer ({z} : Set G) :=
    (le_trans c.pocket₁.2.1 inf_le_right) hxK
  have hconj : h⁻¹ * (h * x * h⁻¹) * h ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem (inv_mem c.h_z) hxKc) c.h_z
  rwa [show h⁻¹ * (h * x * h⁻¹) * h = x from by group] at hconj

theorem Sec5HCtx.K₄_le_centralizer (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    CFSG.conjugate K₂ h ≤ centralizer ({z} : Set G) := by
  intro x hx
  have hxK : h * x * h⁻¹ ∈ K₂ := sec5b_mem_conjugate_iff.mp hx
  have hxKc : h * x * h⁻¹ ∈ centralizer ({z} : Set G) :=
    (le_trans c.pocket₂.2.1 inf_le_right) hxK
  have hconj : h⁻¹ * (h * x * h⁻¹) * h ∈ centralizer ({z} : Set G) :=
    mul_mem (mul_mem (inv_mem c.h_z) hxKc) c.h_z
  rwa [show h⁻¹ * (h * x * h⁻¹) * h = x from by group] at hconj

theorem Sec5HCtx.comm₃₄ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    ∀ a ∈ CFSG.conjugate K₁ h, ∀ b ∈ CFSG.conjugate K₂ h, a * b = b * a := by
  intro a ha b hb
  have ha' : h * a * h⁻¹ ∈ K₁ := sec5b_mem_conjugate_iff.mp ha
  have hb' : h * b * h⁻¹ ∈ K₂ := sec5b_mem_conjugate_iff.mp hb
  have hcomm := c.comm₁₂ (h * a * h⁻¹) ha' (h * b * h⁻¹) hb'
  have hall : h * (a * b) * h⁻¹ = h * (b * a) * h⁻¹ := by
    calc h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
      _ = (h * b * h⁻¹) * (h * a * h⁻¹) := hcomm
      _ = h * (b * a) * h⁻¹ := by group
  have : a * b = b * a := by
    have hconj := congrArg (fun t => h⁻¹ * t * h) hall
    simpa [mul_assoc] using hconj
  exact this

theorem Sec5HCtx.iso₃ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Nonempty (↥(CFSG.conjugate K₁ h) ≃* SL23) := by
  obtain ⟨e⟩ := c.iso₁
  exact ⟨(Subgroup.equivMapOfInjective K₁ (MulAut.conj h⁻¹).toMonoidHom
    (MulAut.conj h⁻¹).injective).symm.trans e⟩

theorem Sec5HCtx.iso₄ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    Nonempty (↥(CFSG.conjugate K₂ h) ≃* SL23) := by
  obtain ⟨e⟩ := c.iso₂
  exact ⟨(Subgroup.equivMapOfInjective K₂ (MulAut.conj h⁻¹).toMonoidHom
    (MulAut.conj h⁻¹).injective).symm.trans e⟩

theorem Sec5HCtx.t_mem_sup₃₄ (c : Sec5HCtx G t L S z r B A K₁ K₂ h) :
    t ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h := by
  have hsq : (h * h) * t = t * (h * h) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.h_sq
  have ht : h * t * h⁻¹ = h⁻¹ * t * h := by
    calc h * t * h⁻¹ = h⁻¹ * ((h * h) * t * (h * h)⁻¹) * h := by group
      _ = h⁻¹ * t * h := by rw [hsq]; group
  rw [← sec5b_conjugate_sup K₁ K₂ h]
  exact sec5b_mem_conjugate_iff.mpr (ht.symm ▸ c.h_t)

end Ctx

end CFSG.OddStandard.SmallF3.Omega
