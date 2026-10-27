module

public import CFSG.CGT.Stroth77.Stroth34Local
public import CFSG.CGT.Stroth77.Section33Frame

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

namespace StrothWeakTypeData

variable {G : Type*} [Group G] {B : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData B τ)

theorem rho_mul_t_mul_rho_inv : dD.ρ * dD.t * dD.ρ⁻¹ = dD.uv := by
  calc dD.ρ * dD.t * dD.ρ⁻¹ = (dD.uv * dD.ρ) * dD.ρ⁻¹ := by rw [← dD.uv_rho]
    _ = dD.uv := by group

theorem rho_mul_uv_mul_rho_inv : dD.ρ * dD.uv * dD.ρ⁻¹ = dD.uv * dD.t := by
  have huv : dD.uv⁻¹ = dD.uv := inv_eq_of_mul_eq_one_right dD.uv_sq
  have h1 : dD.ρ * dD.uv = dD.t * dD.ρ * dD.t⁻¹ := by
    calc dD.ρ * dD.uv = dD.ρ * dD.uv * dD.t * dD.t⁻¹ := by group
      _ = dD.t * dD.ρ * dD.t⁻¹ := by rw [← dD.t_rho]
  have h2 : dD.ρ * dD.t⁻¹ * dD.ρ⁻¹ = dD.uv := by
    have := congrArg (·⁻¹) dD.rho_mul_t_mul_rho_inv
    simp only [mul_inv_rev, inv_inv] at this
    rw [← huv, ← this]
    group
  calc dD.ρ * dD.uv * dD.ρ⁻¹ = dD.t * (dD.ρ * dD.t⁻¹ * dD.ρ⁻¹) := by rw [h1]; group
    _ = dD.t * dD.uv := by rw [h2]
    _ = dD.uv * dD.t := dD.uv_comm_t.symm

end StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

namespace StrothFrame.IsD

theorem setting (h : F.IsD D dD)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    Local.Setting (F.S : Subgroup G) D :=
  ⟨F.S.isPGroup', h.le_S, dD.isMulCommutative, h.cent, hns⟩

theorem uv_mem_S (h : F.IsD D dD) : dD.uv ∈ (F.S : Subgroup G) := h.uv_eq ▸ F.uv_mem_S

theorem t_mem_S (h : F.IsD D dD) : dD.t ∈ (F.S : Subgroup G) := h.t_eq ▸ F.t_mem_S

theorem rho_twist (h : F.IsD D dD) (hS : Local.Setting (F.S : Subgroup G) D) {e d₀ : G}
    (he : e ∈ hS.R) (huv : e⁻¹ * dD.uv * e * dD.uv⁻¹ ∈ D)
    (ht : e⁻¹ * dD.t * e * dD.t⁻¹ ∈ D) (hp : hS.proj dD.ρ e = e * d₀) :
    (e * d₀)⁻¹ * dD.uv * (e * d₀) * dD.uv⁻¹ =
        dD.ρ⁻¹ * (e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹) * dD.ρ ∧
      (e * d₀)⁻¹ * dD.t * (e * d₀) * dD.t⁻¹ = dD.ρ⁻¹ * (e⁻¹ * dD.uv * e * dD.uv⁻¹) * dD.ρ := by
  have huvt : e⁻¹ * (dD.uv * dD.t) * e * (dD.uv * dD.t)⁻¹ ∈ D := by
    have hc : dD.uv * (e⁻¹ * dD.t * e * dD.t⁻¹) * dD.uv⁻¹ ∈ D := by
      have := (Subgroup.mem_normalizer_iff''.mp (inv_mem dD.uv_mem) _).mp ht
      simpa using this
    have := mul_mem huv hc
    convert this using 1
    group
  constructor
  · have key := hS.proj_twist dD.ρ_mem he (h.uv_mem_S) dD.uv_mem huvt (by
      rw [dD.rho_mul_uv_mul_rho_inv]; group)
    rw [hp] at key
    rw [key]; group
  · have key := hS.proj_twist dD.ρ_mem he (h.t_mem_S) dD.t_mem huv (by
      rw [dD.rho_mul_t_mul_rho_inv]; group)
    rw [hp] at key
    rw [key]; group

theorem mem_of_conj_mem_E (h : F.IsD D dD) {g : G} (hgS : g ∈ (F.S : Subgroup G))
    (hgC : g ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (huv : g⁻¹ * dD.uv * g * dD.uv⁻¹ ∈ F.E) (ht : g⁻¹ * dD.t * g * dD.t⁻¹ ∈ F.E) : g ∈ D := by
  rw [h.uv_eq] at huv
  rw [h.t_eq] at ht
  have hfix : ∀ y : G, y * y = 1 → y ∈ F.A → g⁻¹ * y * g = y := fun y hyy hyA => by
    have hc := Subgroup.mem_centralizer_iff.mp hgC y
      (mem_omegaIn_one_of_mul_self (h.A_le hyA) hyy)
    rw [mul_assoc, hc]; group
  refine h.mem_of_mem_normalizer_E hgS hgC ?_
  rw [F.E_eq]
  refine mem_normalizer_closure_of_conj_mem ?_
  rw [← F.E_eq]
  rintro y (rfl | rfl | rfl | rfl)
  · rw [hfix _ F.a_sq_mul_a_sq (F.A.pow_mem F.dA.a.2 2)]; exact F.a_sq_mem_E
  · rw [hfix _ F.b_sq_mul_b_sq (F.A.pow_mem F.dA.b.2 2)]; exact F.b_sq_mem_E
  · have e : g⁻¹ * F.dA.uv * g = (g⁻¹ * F.dA.uv * g * F.dA.uv⁻¹) * F.dA.uv := by group
    rw [e]; exact mul_mem huv F.uv_mem_E
  · have e : g⁻¹ * F.dA.t * g = (g⁻¹ * F.dA.t * g * F.dA.t⁻¹) * F.dA.t := by group
    rw [e]; exact mul_mem ht F.t_mem_E

end StrothFrame.IsD

end CFSG.CGT.Stroth77
