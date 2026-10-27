module

public import CFSG.GH74.QTGen4.U42.PairExt
public import CFSG.GH74.QTGen4.U42.U0Core

public section

namespace CFSG.GH74.QTGen4.U42

open Subgroup

variable {G : Type*} [Group G] {H U : Subgroup G}

@[expose] def conjOn (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (h : ↥H) : ↥U ≃* ↥U where
  toFun u := ⟨(h : G) * u * (h : G)⁻¹, hU h h.2 u u.2⟩
  invFun u := ⟨(h : G)⁻¹ * u * (h : G), by
    have := hU (h : G)⁻¹ (H.inv_mem h.2) u u.2
    rwa [inv_inv] at this⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

theorem conjOn_mul (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (h k : ↥H) :
    conjOn hU (h * k) = (conjOn hU k).trans (conjOn hU h) :=
  MulEquiv.ext fun u => Subtype.ext (by simp [conjOn, mul_assoc])

@[expose] def nu (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (e : ↥U ≃* U0) (h : ↥H) :
    MulAut U0 :=
  (e.symm.trans (conjOn hU h)).trans e

theorem nu_mul (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (e : ↥U ≃* U0) (h k : ↥H) :
    nu hU e (h * k) = nu hU e h * nu hU e k := by
  apply MulEquiv.ext
  intro x
  simp [nu, conjOn_mul, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

@[expose] def nuHom (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (e : ↥U ≃* U0) :
    ↥H →* MulAut U0 :=
  MonoidHom.mk' (nu hU e) (nu_mul hU e)

theorem nu_eq_one_iff (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (e : ↥U ≃* U0) (h : ↥H) :
    nu hU e h = 1 ↔ ∀ u ∈ U, (h : G) * u = u * (h : G) := by
  constructor
  · intro h1 u hu
    have key : ∀ v : ↥U, conjOn hU h v = v := by
      intro v
      have hv := congrArg (fun f : MulAut U0 => f (e v)) h1
      simp only [nu, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at hv
      exact e.injective hv
    have := congrArg Subtype.val (key ⟨u, hu⟩)
    simp only [conjOn, MulEquiv.coe_mk, Equiv.coe_fn_mk] at this
    exact mul_inv_eq_iff_eq_mul.mp this
  · intro hc
    apply MulEquiv.ext
    intro x
    have hk : conjOn hU h (e.symm x) = e.symm x := by
      apply Subtype.ext
      have hc' := hc (e.symm x) (e.symm x).2
      simp only [conjOn, MulEquiv.coe_mk, Equiv.coe_fn_mk]
      rw [hc', mul_assoc, mul_inv_cancel, mul_one]
    simp only [nu, MulEquiv.trans_apply, hk, MulEquiv.apply_symm_apply, MulAut.one_apply]

theorem mem_center_transfer {A C : Type*} [Group A] [Group C] (f : A ≃* C) (y : A) :
    y ∈ Subgroup.center A ↔ f y ∈ Subgroup.center C := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro hy g
    obtain ⟨a, rfl⟩ := f.surjective g
    simpa [map_mul] using congrArg f (hy a)
  · intro hy g
    apply f.injective
    simpa [map_mul] using hy (f g)

theorem mem_zpowers_transfer (e : ↥U ≃* U0) (y : ↥U) :
    e y ∈ Subgroup.zpowers zc ↔ y ∈ Subgroup.zpowers (e.symm zc) := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, e.injective (by rw [map_zpow, MulEquiv.apply_symm_apply, hk])⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, map_zpow, MulEquiv.apply_symm_apply]⟩

theorem mem_center_U_iff (e : ↥U ≃* U0) (y : ↥U) :
    y ∈ Subgroup.center ↥U ↔ y ∈ Subgroup.zpowers (e.symm zc) := by
  rw [mem_center_transfer e y, center_U0, mem_zpowers_transfer]

variable {B T : Subgroup G}

@[expose] def zH (h : PairCore H B T U) (e : ↥U ≃* U0) : ↥H :=
  ⟨((e.symm zc : ↥U) : G), (h.U_le_T.trans (h.T_le_B.trans h.B_le_H)) (e.symm zc).2⟩

theorem nu_eq_one_iff_mem_zpowers (h : PairCore H B T U)
    (hU : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) (e : ↥U ≃* U0) (x : ↥H) :
    nu hU e x = 1 ↔ x ∈ Subgroup.zpowers (zH h e) := by
  have hcoe : ∀ k : ℤ, (((zH h e) ^ k : ↥H) : G) = ((((e.symm zc) ^ k : ↥U)) : G) := by
    intro k
    simp only [SubgroupClass.coe_zpow, zH]
  constructor
  · intro h1
    have hc : ∀ u ∈ U, (x : G) * u = u * (x : G) := (nu_eq_one_iff hU e x).mp h1
    have hxU : (x : G) ∈ U := h.centralizes (x : G) x.2 hc
    have hy : (⟨(x : G), hxU⟩ : ↥U) ∈ Subgroup.center ↥U := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (hc g.1 g.2).symm
    obtain ⟨k, hk⟩ := (mem_center_U_iff e _).mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    rw [hcoe k]
    exact congrArg Subtype.val hk
  · rintro ⟨k, rfl⟩
    rw [nu_eq_one_iff hU e]
    intro u hu
    have hw : ((e.symm zc) ^ k : ↥U) ∈ Subgroup.center ↥U :=
      (mem_center_U_iff e _).mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩)
    have hw' := congrArg Subtype.val (Subgroup.mem_center_iff.mp hw ⟨u, hu⟩)
    rw [hcoe k]
    exact hw'.symm

end CFSG.GH74.QTGen4.U42

end
