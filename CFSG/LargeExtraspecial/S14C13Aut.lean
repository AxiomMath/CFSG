module

public import CFSG.LargeExtraspecial.S14NQNine

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.LargeExtraspecial.S4

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem apply_mem_Vt_of_mem_Ct (haQ : g * S.z * g⁻¹ ∈ S.QG) {t x : S.O} (hx : x ∈ Ct S t)
    {v : S.Qt} (hv : v ∈ Vt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Vt S g t := by
  obtain ⟨k, hk⟩ : ∃ k : S.M, S.ρ k = x := (Subgroup.mem_inf.mp hx).1
  have hkt : S.ρ k * t = t * S.ρ k := by
    rw [hk]
    exact mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2
  have := apply_mem_Vt haQ hkt hv
  rwa [hk] at this

variable (S g) in
@[expose] noncomputable def resC (haQ : g * S.z * g⁻¹ ∈ S.QG) (t : S.O) :
    Ct S t →* (Vt S g t ≃ₗ[ZMod 2] Vt S g t) :=
  restrictHom (S.O.subtype.comp (Ct S t).subtype) (Vt S g t)
    (fun x _ hu => apply_mem_Vt_of_mem_Ct haQ x.2 hu)

theorem coe_resC_apply (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (x : Ct S t) (v : Vt S g t) :
    ((resC S g haQ t x v : Vt S g t) : S.Qt) = ((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
  rfl

theorem resC_mul_resV (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (y : Ct S t) (r : Rbar S g t) :
    resC S g haQ t y * resV haQ t r * (resC S g haQ t y)⁻¹ =
      resV haQ t ⟨y * r * (y : S.O)⁻¹, conj_mem_Rbar_of_mem_Ct y.2 r.2⟩ := by
  ext v
  rw [← map_inv]
  rfl

theorem map_conj_resC_RmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (y : Ct S t) :
    (RmodN S g t).map (MulAut.conj (resC S g haQ t y)).toMonoidHom = RmodN S g t := by
  have hle : ∀ y : Ct S t,
      (RmodN S g t).map (MulAut.conj (resC S g haQ t y)).toMonoidHom ≤ RmodN S g t := by
    intro y
    rintro _ ⟨e, he, rfl⟩
    rw [← range_resV haQ t] at he ⊢
    obtain ⟨r, rfl⟩ := he
    exact ⟨_, (resC_mul_resV haQ y r).symm⟩
  refine le_antisymm (hle y) fun e he => ⟨resC S g haQ t y⁻¹ * e * (resC S g haQ t y⁻¹)⁻¹,
    hle y⁻¹ ⟨e, he, rfl⟩, ?_⟩
  simp [map_inv, mul_assoc]

@[expose] noncomputable def autC (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (y : Ct S t) :
    RmodN S g t ≃* RmodN S g t :=
  Bridge.equivOfMapEq (MulAut.conj (resC S g haQ t y)) (map_conj_resC_RmodN haQ y)

theorem coe_autC (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (y : Ct S t) (e : RmodN S g t) :
    (autC haQ y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
      resC S g haQ t y * e * (resC S g haQ t y)⁻¹ :=
  rfl

theorem conj_resC_mem_LmodN (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {y : Ct S t}
    (hyL : (y : S.O) ∈ normalizer (S.Lbar g : Set S.O)) {e : Vt S g t ≃ₗ[ZMod 2] Vt S g t}
    (he : e ∈ LmodN S g t) :
    resC S g haQ t y * e * (resC S g haQ t y)⁻¹ ∈ LmodN S g t := by
  obtain ⟨x, hx, hex⟩ := mem_LmodN.mp he
  refine mem_LmodN.mpr ⟨y * x * (y : S.O)⁻¹, (mem_normalizer_iff.mp hyL x).mp hx, fun v => ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← map_inv, coe_resC_apply, hex,
    coe_resC_apply]
  rfl

theorem autC_mem_LmodN_iff (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} {y : Ct S t}
    (hyL : (y : S.O) ∈ normalizer (S.Lbar g : Set S.O)) (e : RmodN S g t) :
    (autC haQ y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ LmodN S g t ↔
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ LmodN S g t := by
  rw [coe_autC]
  refine ⟨fun h => ?_, conj_resC_mem_LmodN haQ hyL⟩
  have hyL' : ((y⁻¹ : Ct S t) : S.O) ∈ normalizer (S.Lbar g : Set S.O) := inv_mem hyL
  have := conj_resC_mem_LmodN haQ hyL' h
  rwa [map_inv, inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc,
    inv_mul_cancel, mul_one] at this

theorem comm_mem_Nbar_of_autC_eq (haQ : g * S.z * g⁻¹ ∈ S.QG) {t : S.O} (y : Ct S t)
    (r₀ : Rbar S g t)
    (h : ∀ e : RmodN S g t, (autC haQ y e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) =
      resV haQ t r₀ * e * (resV haQ t r₀)⁻¹) :
    ∀ r ∈ Rbar S g t, ((r₀ : S.O)⁻¹ * y) * r * ((r₀ : S.O)⁻¹ * y)⁻¹ * r⁻¹ ∈ Nbar S g t := by
  intro r hr
  set w : Rbar S g t := r₀⁻¹ * ⟨y * r * (y : S.O)⁻¹, conj_mem_Rbar_of_mem_Ct y.2 hr⟩ * r₀ *
    ⟨r, hr⟩⁻¹
  have hw : (w : S.O) = ((r₀ : S.O)⁻¹ * y) * r * ((r₀ : S.O)⁻¹ * y)⁻¹ * r⁻¹ := by
    simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [← hw, ← resV_eq_one_iff haQ]
  have he : resV haQ t ⟨r, hr⟩ ∈ RmodN S g t := by rw [← range_resV haQ t]; exact ⟨_, rfl⟩
  have h1 := h ⟨_, he⟩
  rw [coe_autC, resC_mul_resV] at h1
  simp only [w, map_mul, map_inv, h1]
  group

end CFSG.LargeExtraspecial.S14
