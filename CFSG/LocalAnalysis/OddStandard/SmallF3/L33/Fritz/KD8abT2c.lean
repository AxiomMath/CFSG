module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abMix2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv

namespace KD8ab

open KD7

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

omit [Finite X] in
theorem d_conj_t : C.d * t * C.d⁻¹ = t := by
  rw [A.commute_t C.d_mem, mul_inv_cancel_right]

omit [Finite X] in
theorem d_inv_conj_t : C.d⁻¹ * t * C.d = t := by
  have := d_conj_t (C := C)
  calc C.d⁻¹ * t * C.d = C.d⁻¹ * (C.d * t * C.d⁻¹) * C.d := by rw [this]
    _ = t := by group

theorem d_conj_z : C.d * S.z * C.d⁻¹ = S.z := conj_z S C.d_mem

theorem d_inv_conj_z : C.d⁻¹ * S.z * C.d = S.z := by
  have := conj_z S (inv_mem C.d_mem)
  rwa [inv_inv] at this

theorem d_conj_y : C.d * S.y * C.d⁻¹ = S.x * S.y ∨ C.d * S.y * C.d⁻¹ = S.z * (S.x * S.y) := by
  rcases conj_refl_of_ψ C.d_mem (SDKD.ψX_d C) (isRefl_y S) with h | h
  · exact Or.inl h
  · right; rw [h, x_inv_eq S, mul_assoc]

theorem d_inv_conj_y :
    C.d⁻¹ * S.y * C.d = S.x * S.y ∨ C.d⁻¹ * S.y * C.d = S.z * (S.x * S.y) := by
  have h := conj_refl_of_ψ (inv_mem C.d_mem) (ψX_d_inv (C := C)) (isRefl_y S)
  rw [inv_inv] at h
  rcases h with h | h
  · exact Or.inl h
  · right; rw [h, x_inv_eq S, mul_assoc]

theorem d_conj_xy : C.d * (S.x * S.y) * C.d⁻¹ = S.z * S.y ∨
    C.d * (S.x * S.y) * C.d⁻¹ = S.y := by
  rcases conj_refl_of_ψ C.d_mem (SDKD.ψX_d C) (isRefl_xy S) with h | h
  · left; rw [h, x_mul_xy]
  · right; rw [h, inv_mul_cancel_left]

theorem d_inv_conj_xy : C.d⁻¹ * (S.x * S.y) * C.d = S.z * S.y ∨
    C.d⁻¹ * (S.x * S.y) * C.d = S.y := by
  have h := conj_refl_of_ψ (inv_mem C.d_mem) (ψX_d_inv (C := C)) (isRefl_xy S)
  rw [inv_inv] at h
  rcases h with h | h
  · left; rw [h, x_mul_xy]
  · right; rw [h, inv_mul_cancel_left]

theorem d_sq : C.d ^ 2 = 1 ∨ C.d ^ 2 = t := by
  refine SDKD.eq_one_or_eq_t_of_mem_K C ?_
  rw [← SD.ψX_eq_one_iff (pow_mem C.d_mem 2), SD.ψX_pow C.d_mem, SDKD.ψX_d C]
  exact SDKD.d8_sq

theorem y_not_comm_xy : S.y * (S.x * S.y) ≠ S.x * S.y * S.y := by
  intro hc
  have hy2 : S.y * S.y = 1 := by rw [← pow_two, S.y_sq]
  have hyinv : S.y⁻¹ = S.y := inv_eq_of_mul_eq_one_right hy2
  have h1 : S.y * S.x * S.y⁻¹ = S.x := by
    rw [hyinv]
    calc S.y * S.x * S.y = S.y * (S.x * S.y) := by group
      _ = S.x * S.y * S.y := hc
      _ = S.x := by rw [mul_assoc, hy2, mul_one]
  exact x_ne_inv S (h1.symm.trans S.y_inv)

variable {S}

theorem mem_B_of_fix {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {g : X} (hg : g ∈ T₁)
    (ht : g * t * g⁻¹ = t) (hk : g * S.k * g⁻¹ = S.k) (hy : g * S.y * g⁻¹ = S.y)
    (hxy : g * (S.x * S.y) * g⁻¹ = S.x * S.y) : g ∈ S.B := by
  have comm_of : ∀ {a : X}, g * a * g⁻¹ = a → g * a = a * g := fun {a} h => by
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [h]
  have hgE := mem_TE_of_mem_T₁ S h4 hg (comm_of ht) (comm_of hk)
  have hgy := mem_E_of_comm S (isRefl_y S) hgE (comm_of hy)
  rw [E_eq_B_sup] at hgy
  rcases Sec7.mem_or_of_mem_sup (elemAbelianTwo_B S) S.y_sq
    (fun b hb => (B_comm_R S hb S.y_mem).symm) hgy with h | h
  · exact h
  · exfalso
    apply y_not_comm_xy S
    have hy2 : S.y * S.y = 1 := by rw [← pow_two, S.y_sq]
    have hbc : (g * S.y) * (S.x * S.y) = (S.x * S.y) * (g * S.y) :=
      central_of_mem_B S h (R_le_TE S (mul_mem S.x_mem S.y_mem))
    have h2 : g * (S.x * S.y) = (S.x * S.y) * g := comm_of hxy
    have hgb : g = (g * S.y) * S.y := by rw [mul_assoc, hy2, mul_one]
    calc S.y * (S.x * S.y) = (g * S.y)⁻¹ * ((g * S.y) * S.y * (S.x * S.y)) := by group
      _ = (g * S.y)⁻¹ * (g * (S.x * S.y)) := by rw [← hgb]
      _ = (g * S.y)⁻¹ * ((S.x * S.y) * g) := by rw [h2]
      _ = (g * S.y)⁻¹ * ((S.x * S.y) * (g * S.y) * S.y) := by
          rw [mul_assoc (S.x * S.y), ← hgb]
      _ = (g * S.y)⁻¹ * ((g * S.y) * (S.x * S.y) * S.y) := by rw [hbc]
      _ = S.x * S.y * S.y := by group

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD
