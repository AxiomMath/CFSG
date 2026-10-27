module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LieType.SeitzGeneration.OutdiagHeis
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescentFixed

public section

open scoped commutatorElement MatrixGroups
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

namespace CFSG.LieType.SeitzGeneration

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] def circMat (α x₀ x₁ x₂ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![x₀, α * x₂, α * x₁; x₁, x₀, α * x₂; x₂, x₁, x₀]

theorem eq_circMat_of_comm {α : K} {M : Matrix (Fin 3) (Fin 3) K}
    (hM : M * heisC α = heisC α * M) : M = circMat α (M 0 0) (M 1 0) (M 2 0) := by
  have e : ∀ i j, (M * heisC α) i j = (heisC α * M) i j := fun i j => by rw [hM]
  have e00 := e 0 0
  have e10 := e 1 0
  have e20 := e 2 0
  have e01 := e 0 1
  have e11 := e 1 1
  have e21 := e 2 1
  simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] at e00 e10 e20 e01 e11 e21
  ext i j
  fin_cases i <;> fin_cases j <;> simp [circMat] <;> grind

theorem circ_unitary_rel (h : UnitaryFieldData ℓ f K) {α x₀ x₁ x₂ : K}
    (hU : ((circMat α x₀ x₁ x₂).map h.bar)ᵀ * circMat α x₀ x₁ x₂ = 1) :
    h.bar x₀ * x₀ + h.bar x₁ * x₁ + h.bar x₂ * x₂ = 1 ∧
      α * h.bar x₀ * x₂ + h.bar x₁ * x₀ + h.bar x₂ * x₁ = 0 ∧
      α * h.bar x₀ * x₁ + α * h.bar x₁ * x₂ + h.bar x₂ * x₀ = 0 := by
  have h00 := congrFun (congrFun hU 0) 0
  have h01 := congrFun (congrFun hU 0) 1
  have h02 := congrFun (congrFun hU 0) 2
  simp [circMat, Matrix.mul_apply, Fin.sum_univ_three] at h00 h01 h02
  refine ⟨by linear_combination h00, by linear_combination h01, by linear_combination h02⟩

theorem circ_coord_ne_zero (h : UnitaryFieldData ℓ f K) {α x₀ x₁ x₂ : K} (hα : h.bar α * α = 1)
    (hU : ((circMat α x₀ x₁ x₂).map h.bar)ᵀ * circMat α x₀ x₁ x₂ = 1) :
    (x₀ = 0 → x₁ = 0 ∨ x₂ = 0) ∧ (x₁ = 0 → x₀ = 0 ∨ x₂ = 0) ∧ (x₂ = 0 → x₀ = 0 ∨ x₁ = 0) := by
  obtain ⟨-, e1, -⟩ := circ_unitary_rel h hU
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · subst h0
    have : h.bar x₂ * x₁ = 0 := by simpa using e1
    rcases mul_eq_zero.1 this with hh | hh
    · exact Or.inr ((map_eq_zero h.bar).1 hh)
    · exact Or.inl hh
  · subst h1
    have : α * h.bar x₀ * x₂ = 0 := by simpa using e1
    rcases mul_eq_zero.1 this with hh | hh
    · rcases mul_eq_zero.1 hh with hh' | hh'
      · exact absurd hh' hα0
      · exact Or.inl ((map_eq_zero h.bar).1 hh')
    · exact Or.inr hh
  · subst h2
    have : h.bar x₁ * x₀ = 0 := by simpa using e1
    rcases mul_eq_zero.1 this with hh | hh
    · exact Or.inr ((map_eq_zero h.bar).1 hh)
    · exact Or.inl hh

theorem circ_not_all_norm_one (h : UnitaryFieldData ℓ f K) {α x₀ x₁ x₂ : K}
    (hα : h.bar α * α = 1) (hnc : ¬ ∃ μ : K, μ ^ 3 = α)
    (hU : ((circMat α x₀ x₁ x₂).map h.bar)ᵀ * circMat α x₀ x₁ x₂ = 1) :
    ¬ (h.bar x₀ * x₀ = 1 ∧ h.bar x₁ * x₁ = 1 ∧ h.bar x₂ * x₂ = 1) := by
  rintro ⟨n0, n1, n2⟩
  obtain ⟨-, e1, e2⟩ := circ_unitary_rel h hU
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    simp at n0
  have hx1 : x₁ ≠ 0 := by
    rintro rfl
    simp at n1
  have hx2 : x₂ ≠ 0 := by
    rintro rfl
    simp at n2
  apply hnc
  refine ⟨α * x₂ / x₀, ?_⟩
  field_simp
  grind

theorem blaschke_unitary (h : UnitaryFieldData ℓ f K) {α β : K} (hα : h.bar α * α = 1)
    (hρ0 : 1 - α * h.bar β ^ 3 ≠ 0) :
    ((circMat α ((α * h.bar β ^ 2 - β) / (1 - α * h.bar β ^ 3))
        ((1 - β * h.bar β) / (1 - α * h.bar β ^ 3))
        (h.bar β * (1 - β * h.bar β) / (1 - α * h.bar β ^ 3))).map h.bar)ᵀ *
      circMat α ((α * h.bar β ^ 2 - β) / (1 - α * h.bar β ^ 3))
        ((1 - β * h.bar β) / (1 - α * h.bar β ^ 3))
        (h.bar β * (1 - β * h.bar β) / (1 - α * h.bar β ^ 3)) = 1 := by
  have hρb0 : 1 - h.bar α * β ^ 3 ≠ 0 := by
    intro h0
    apply hρ0
    have := congrArg h.bar h0
    simpa [map_sub, map_mul, map_pow, h.bar_bar] using this
  have hbb : ∀ c, h.bar (h.bar c) = c := h.bar_bar
  ext i j
  simp only [circMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.tail_cons, Matrix.head_fin_const]
  fin_cases i <;> fin_cases j <;> simp [hbb] <;> field_simp <;> grind


theorem circMat_comm (α x₀ x₁ x₂ : K) :
    circMat α x₀ x₁ x₂ * heisC α = heisC α * circMat α x₀ x₁ x₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circMat, heisC, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_circMat (α x₀ x₁ x₂ : K) :
    (circMat α x₀ x₁ x₂).det = x₀ ^ 3 + α * x₁ ^ 3 + α ^ 2 * x₂ ^ 3 - 3 * α * x₀ * x₁ * x₂ := by
  rw [Matrix.det_fin_three]
  simp [circMat]
  ring

end CFSG.LieType.SeitzGeneration
