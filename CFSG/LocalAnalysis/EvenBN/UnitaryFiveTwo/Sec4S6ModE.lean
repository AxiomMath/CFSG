module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSTen
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Matrix

theorem e₁SU_mem_normalizer_A₁sub : e₁SU ∈ normalizer (A₁sub : Set SU52) :=
  normalizer_Ssub_le_normalizer_A₁sub (Esub_le_normalizer_Ssub (mem_sup_left (mem_zpowers _)))

theorem mat_e₁SU_diag : mat e₁SU = Matrix.diagonal ![1, F4.ω, F4.ω, F4.ω, 1] := rfl

theorem cvec_conj_e₁ (a : SU52) :
    cvec (mat (e₁SU * a * e₁SU⁻¹)) = fun i => F4.ω * cvec (mat a) i := by
  have hd : ∀ i, (![1, F4.ω, F4.ω, F4.ω, 1] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simp <;> decide
  funext i
  unfold cvec
  rw [mat_conj_diag hd mat_e₁SU_diag]
  fin_cases i <;> simp [ι3]

theorem cvec_conj_e₂ (a : SU52) :
    cvec (mat (e₂SU * a * e₂SU⁻¹)) =
      ![cvec (mat a) 0, F4.ω * cvec (mat a) 1, cvec (mat a) 2] := by
  have hd : ∀ i, (![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] : Fin 5 → F4) i ≠ 0 := by
    intro i
    fin_cases i <;> simp [bar_apply] <;> decide
  have hg : mat e₂SU = Matrix.diagonal ![F4.ω, F4.ω, bar F4.ω, F4.ω, F4.ω] := rfl
  funext i
  unfold cvec
  rw [mat_conj_diag hd hg]
  have hlam : bar F4.ω * (F4.ω)⁻¹ = F4.ω := by
    simp only [bar_apply]
    decide
  have hone : F4.ω * (F4.ω)⁻¹ = 1 := by decide
  fin_cases i
  · simp only [ι3, Fin.zero_eta, Matrix.cons_val_zero, Fin.mk_one, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons]
    show F4.ω * mat a 1 0 * F4.ω⁻¹ = mat a 1 0
    rw [mul_comm F4.ω, mul_assoc, hone, mul_one]
  · show bar F4.ω * mat a 2 0 * F4.ω⁻¹ = F4.ω * mat a 2 0
    rw [mul_right_comm, hlam]
  · show F4.ω * mat a 3 0 * F4.ω⁻¹ = mat a 3 0
    rw [mul_comm F4.ω, mul_assoc, hone, mul_one]

theorem omega_mul_eq_self {c : F4} (h : F4.ω * c = c) : c = 0 := by
  revert c
  decide

theorem mem_ZX₄sub_of_conj_e₁ {a ζ : SU52} (ha : a ∈ A₁sub) (hζ : ζ ∈ ZX₄sub)
    (h : e₁SU * a * e₁SU⁻¹ = a * ζ) : a ∈ ZX₄sub := by
  refine mem_ZX₄sub_of_cvec_eq_zero ha ?_
  have h1 := cvec_conj_e₁ a
  rw [h, cvec_mul ha ((ZX₄sub_le_X₄sub.trans le_sup_right) hζ), cvec_of_mem_ZX₄sub hζ, add_zero] at h1
  funext i
  exact omega_mul_eq_self (congrFun h1 i).symm

theorem mem_sup_of_conj_e₂ {a : SU52} (ha : a ∈ A₁sub) (h : e₂SU * a * e₂SU⁻¹ = a) :
    a ∈ X₂sub ⊔ X₃sub ⊔ ZX₄sub := by
  obtain ⟨a₂, a₃, a₄, b₄, hv, e⟩ := exists_nf_of_mem_A₁sub ha
  have h1 := cvec_conj_e₂ a
  rw [h] at h1
  have hc : cvec (mat a) = ![a₂, a₄, a₃] := by rw [e, cvec_nf]
  have h14 : a₄ = 0 := by
    have := congrFun h1 1
    rw [hc] at this
    simp at this
    exact omega_mul_eq_self this.symm
  subst h14
  have hv' : (0 : F4) * bar 0 = b₄ + bar b₄ := hv
  have ea : a = x₂SU a₂ * x₃SU a₃ * x₄SU 0 b₄ hv' := ext_mat (by
    rw [e, mat_mul, mat_mul, mat_x₂SU, mat_x₃SU, mat_x₄SU])
  rw [ea]
  exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (x₂SU_mem _)))
    (mem_sup_left (mem_sup_right (x₃SU_mem _))))
    (mem_sup_right (mem_x₄Sub.2 ⟨0, b₄, rfl, rfl⟩))

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
