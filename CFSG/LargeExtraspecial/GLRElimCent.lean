module

public import CFSG.LargeExtraspecial.GLRFormBeta
public import CFSG.LargeExtraspecial.GLRFormModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G} (C : Config S)

namespace Config

variable {C} {σ : G} (hσM : σ ∈ S.M) (hσX : σ ∉ C.X) (hσ2 : σ * σ = 1 ∨ σ * σ = S.z)
include hσM hσX

theorem ρ_not_mem_Xbar : S.ρ ⟨σ, hσM⟩ ∉ C.Xbar := fun h => hσX (C.mem_X_iff.mpr ⟨hσM, h⟩)

omit [Finite G] hσM hσX in
include hσ2 in
theorem sq_conj {h : G} (hh : h ∈ S.M) : σ * σ * h * (σ * σ)⁻¹ = h := by
  rcases hσ2 with h2 | h2 <;> rw [h2]
  · group
  · rw [S.z_comm hh |>.symm, mul_inv_cancel_right]

include hσ2 in
theorem conj_mul_conj_eq_iff {h : G} (hh : h ∈ C.A) :
    σ * (h * (σ * h * σ⁻¹)) * σ⁻¹ = h * (σ * h * σ⁻¹) ↔
      C.formOf (S.ρ ⟨σ, hσM⟩) ⟨S.cl h, hh.2⟩ ⟨S.cl h, hh.2⟩ = 0 := by
  have hhM := S.QG_le_M (C.A_le_QG hh)
  have h' : σ * h * σ⁻¹ ∈ C.B := C.conj_mem_B_of_not_mem_X hσM hσX hh
  have e : σ * (h * (σ * h * σ⁻¹)) * σ⁻¹ = (σ * h * σ⁻¹) * h := by
    have := sq_conj hσ2 hhM
    calc σ * (h * (σ * h * σ⁻¹)) * σ⁻¹ = (σ * h * σ⁻¹) * (σ * σ * h * (σ * σ)⁻¹) := by group
      _ = _ := by rw [this]
  rw [e, formOf_apply]
  change _ ↔ polar S.q (S.cl h) ((S.ρ ⟨σ, hσM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl h)) = 0
  rw [← cl_conj hσM (C.A_le_QG hh), S.polar_cl_eq_zero_iff (C.A_le_QG hh) (C.B_le_QG h')]
  exact eq_comm

include hσ2 in
theorem exists_mem_centralizer_cl_eq {a : S.Qt} (ha : a ∈ C.At)
    (haa : C.formOf (S.ρ ⟨σ, hσM⟩) ⟨a, ha⟩ ⟨a, ha⟩ = 0) :
    ∃ q ∈ S.QG, σ * q = q * σ ∧ S.cl q = a + (S.ρ ⟨σ, hσM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
  obtain ⟨h, hhQ, rfl⟩ := S.exists_cl a
  have hh : h ∈ C.A := ⟨hhQ, ha⟩
  have h' : σ * h * σ⁻¹ ∈ C.B := C.conj_mem_B_of_not_mem_X hσM hσX hh
  refine ⟨h * (σ * h * σ⁻¹), S.QG.mul_mem hhQ (C.B_le_QG h'), ?_, ?_⟩
  · have := (conj_mul_conj_eq_iff hσM hσX hσ2 hh).mpr haa
    calc σ * (h * (σ * h * σ⁻¹)) = σ * (h * (σ * h * σ⁻¹)) * σ⁻¹ * σ := by group
      _ = _ := by rw [this]
  · rw [S.cl_mul hhQ (C.B_le_QG h'), cl_conj hσM hhQ]

include hσ2 in
theorem exists_cl_eq_of_commute {q : G} (hq : q ∈ S.QG) (hqσ : σ * q = q * σ) :
    ∃ a, ∃ ha : a ∈ C.At, C.formOf (S.ρ ⟨σ, hσM⟩) ⟨a, ha⟩ ⟨a, ha⟩ = 0 ∧
      S.cl q = a + (S.ρ ⟨σ, hσM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
  set s := S.ρ ⟨σ, hσM⟩
  have hsM : s ∈ S.Mbar := ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := ρ_not_mem_Xbar hσM hσX
  have hfix : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl q := by
    rw [← cl_conj hσM hq, hqσ, mul_inv_cancel_right]
  obtain ⟨a, ha, b, hb, hab⟩ := C.exists_eq_add (S.cl q)
  have hsab : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) b + (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + b := by
    rw [add_comm, ← map_add, hab, hfix]
  obtain ⟨-, hb'⟩ := C.eq_of_add_eq (C.apply_mem_At_of_not_mem hsM hsX hb) ha
    (C.apply_mem_Bt_of_not_mem hsM hsX ha) hb hsab
  have hcl : S.cl q = a + (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by rw [← hab, hb']
  refine ⟨a, ha, ?_, hcl⟩
  obtain ⟨h, hhQ, rfl⟩ := S.exists_cl a
  have hh : h ∈ C.A := ⟨hhQ, ha⟩
  have h' : σ * h * σ⁻¹ ∈ C.B := C.conj_mem_B_of_not_mem_X hσM hσX hh
  have hq₀ : h * (σ * h * σ⁻¹) ∈ S.QG := S.QG.mul_mem hhQ (C.B_le_QG h')
  have hcl₀ : S.cl (h * (σ * h * σ⁻¹)) = S.cl q := by
    rw [S.cl_mul hhQ (C.B_le_QG h'), cl_conj hσM hhQ, hcl]
  refine (conj_mul_conj_eq_iff hσM hσX hσ2 hh).mp ?_
  rcases (S.cl_eq_cl_iff hq₀ hq).mp hcl₀ with h1 | h1
  · rw [← h1, hqσ, mul_inv_cancel_right]
  · have hz : σ * S.z * σ⁻¹ = S.z := by rw [S.z_comm hσM, mul_inv_cancel_right]
    have : σ * q * σ⁻¹ = q := by rw [hqσ, mul_inv_cancel_right]
    rw [h1] at this
    have e : σ * (h * (σ * h * σ⁻¹) * S.z) * σ⁻¹ =
        σ * (h * (σ * h * σ⁻¹)) * σ⁻¹ * (σ * S.z * σ⁻¹) := by group
    rw [e, hz] at this
    exact mul_right_cancel this

theorem conj_eq_z_of_commute {k : G} (hk : k * S.z * k⁻¹ ∈ S.QG)
    (hkσ : σ * (k * S.z * k⁻¹) = (k * S.z * k⁻¹) * σ) : k * S.z * k⁻¹ = S.z := by
  set s := S.ρ ⟨σ, hσM⟩
  have hsM : s ∈ S.Mbar := ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := ρ_not_mem_Xbar hσM hσX
  have hfix : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) = S.cl (k * S.z * k⁻¹) := by
    rw [← cl_conj hσM hk, hkσ, mul_inv_cancel_right]
  have h0 : S.cl (k * S.z * k⁻¹) = 0 := by
    rcases C.fusion k hk with h | h
    · exact C.eq_zero_of_mem_inf h (hfix ▸ C.apply_mem_Bt_of_not_mem hsM hsX h)
    · exact C.eq_zero_of_mem_inf (hfix ▸ C.apply_mem_At_of_not_mem hsM hsX h) h
  rcases (S.cl_eq_zero_iff hk).mp h0 with h1 | h1
  · exfalso
    apply S.z_ne_one
    calc S.z = k⁻¹ * (k * S.z * k⁻¹) * k := by group
      _ = 1 := by rw [h1]; group
  · exact h1

include hσ2 in
theorem mem_QG_of_commute (hβ : IsGoodForm (C.formOf (S.ρ ⟨σ, hσM⟩))) {x : G}
    (hx : x ∈ C.X) (hxc : ∀ q ∈ S.QG, σ * q = q * σ → x * q = q * x) : x ∈ S.QG := by
  set s := S.ρ ⟨σ, hσM⟩
  have hsM : s ∈ S.Mbar := ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := ρ_not_mem_Xbar hσM hσX
  have hxM := C.X_le_M hx
  have hxX := C.ρ_mem_Xbar hx hxM
  set xb := S.ρ ⟨x, hxM⟩
  have hfix : ∀ a (ha : a ∈ C.At), C.formOf s ⟨a, ha⟩ ⟨a, ha⟩ = 0 →
      (xb : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a ∧
        (xb : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) a) =
          (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a := by
    intro a ha haa
    obtain ⟨q, hq, hqσ, hcl⟩ := exists_mem_centralizer_cl_eq hσM hσX hσ2 ha haa
    have h1 : (xb : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl q) = S.cl q := by
      rw [← cl_conj hxM hq, hxc q hq hqσ, mul_inv_cancel_right]
    rw [hcl, map_add] at h1
    have hsa := C.apply_mem_Bt_of_not_mem hsM hsX ha
    exact C.eq_of_add_eq (C.apply_At _ hxX _ ha) ha (C.apply_Bt _ hxX _ hsa) hsa h1
  have hg := hβ.eq_id (C.resAt ⟨xb, hxX⟩ : C.At →ₗ[ZMod 2] C.At)
    (by exact (C.resAt ⟨xb, hxX⟩).injective)
    (fun w hw => Subtype.ext (hfix w.1 w.2 hw).1)
    (fun a w hw => by
      change polar S.q ((xb : S.Qt ≃ₗ[ZMod 2] S.Qt) a) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w) =
        polar S.q a ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) w)
      conv_lhs => rw [← (hfix w.1 w.2 hw).2]
      exact polar_apply_apply xb a _)
  have h1 : xb = 1 := C.eq_one_of_forall_At hxX fun a ha => by
    have := LinearMap.congr_fun hg ⟨a, ha⟩
    exact congrArg Subtype.val this
  exact (S.ρ_eq_one_iff ⟨x, hxM⟩).mp h1

include hσ2 in
theorem mul_conj_ne_z {p : G} (hp : p ∈ S.QG) : p * (σ * p * σ⁻¹) ≠ S.z := by
  intro hpz
  set s := S.ρ ⟨σ, hσM⟩
  have hsM : s ∈ S.Mbar := ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := ρ_not_mem_Xbar hσM hσX
  have hfix : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl p) = S.cl p := by
    have h1 : S.cl (p * (σ * p * σ⁻¹)) = 0 := by rw [hpz, S.cl_z]
    rw [S.cl_mul hp (S.conj_mem_QG hσM hp), cl_conj hσM hp] at h1
    have h2 := eq_neg_of_add_eq_zero_left h1
    rw [ZModModule.neg_eq_self] at h2
    exact h2.symm
  obtain ⟨a, ha, b, hb, hab⟩ := C.exists_eq_add (S.cl p)
  have hsab : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) b + (s : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a + b := by
    rw [add_comm, ← map_add, hab, hfix]
  obtain ⟨-, hb'⟩ := C.eq_of_add_eq (C.apply_mem_At_of_not_mem hsM hsX hb) ha
    (C.apply_mem_Bt_of_not_mem hsM hsX ha) hb hsab
  obtain ⟨h, hhQ, rfl⟩ := S.exists_cl a
  have hh : h ∈ C.A := ⟨hhQ, ha⟩
  have h' : σ * h * σ⁻¹ ∈ C.B := C.conj_mem_B_of_not_mem_X hσM hσX hh
  have hp₀ : h * (σ * h * σ⁻¹) ∈ S.QG := S.QG.mul_mem hhQ (C.B_le_QG h')
  have hcl₀ : S.cl (h * (σ * h * σ⁻¹)) = S.cl p := by
    rw [S.cl_mul hhQ (C.B_le_QG h'), cl_conj hσM hhQ, ← hab, hb']
  have key : (h * (σ * h * σ⁻¹)) * (σ * (h * (σ * h * σ⁻¹)) * σ⁻¹) = 1 := by
    have e1 := sq_conj hσ2 (S.QG_le_M hhQ)
    calc (h * (σ * h * σ⁻¹)) * (σ * (h * (σ * h * σ⁻¹)) * σ⁻¹)
        = h * ((σ * h * σ⁻¹) * (σ * h * σ⁻¹)) * (σ * σ * h * (σ * σ)⁻¹) := by group
      _ = h * h := by rw [C.B_mul_self h', e1, mul_one]
      _ = 1 := C.A_mul_self hh
  rcases (S.cl_eq_cl_iff hp₀ hp).mp hcl₀ with h1 | h1
  · rw [h1, key] at hpz
    exact S.z_ne_one hpz.symm
  · set p₀ := h * (σ * h * σ⁻¹)
    have hσz : σ * S.z * σ⁻¹ = S.z := by rw [S.z_comm hσM, mul_inv_cancel_right]
    have hcz : (σ * p₀ * σ⁻¹) * S.z = S.z * (σ * p₀ * σ⁻¹) :=
      S.z_comm (S.QG_le_M (S.conj_mem_QG hσM hp₀))
    have e : p₀ * S.z * (σ * (p₀ * S.z) * σ⁻¹) = p₀ * (σ * p₀ * σ⁻¹) := by
      calc p₀ * S.z * (σ * (p₀ * S.z) * σ⁻¹)
          = p₀ * (S.z * (σ * p₀ * σ⁻¹)) * (σ * S.z * σ⁻¹) := by group
        _ = p₀ * ((σ * p₀ * σ⁻¹) * S.z) * S.z := by rw [hσz, hcz]
        _ = p₀ * (σ * p₀ * σ⁻¹) * (S.z * S.z) := by group
        _ = p₀ * (σ * p₀ * σ⁻¹) := by rw [S.z_mul_z, mul_one]
    rw [h1, e, key] at hpz
    exact S.z_ne_one hpz.symm

end Config

end CFSG.LargeExtraspecial.GLR
