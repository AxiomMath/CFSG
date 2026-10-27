module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.GH74.GLS.SP.Local.ModelCoord

open CFSG.LieType.Universal.Symplectic.SpExtras CFSG.Assembly.LowTwoRank TauCeti.GLSymplecticFin

variable {F : Type} [Field F]

@[expose] noncomputable def z₁ (s : F) : StatedSp 2 F :=
  elt (RootSubgroupIndex.positiveLong (1 : Fin 2)) (-s)

@[expose] noncomputable def z₂ (c : F) : StatedSp 2 F :=
  elt (RootSubgroupIndex.positiveLong (0 : Fin 2)) (-2 * c)

@[expose] noncomputable def z₃ (a : F) : StatedSp 2 F :=
  elt (RootSubgroupIndex.positiveSum (0 : Fin 2) 1 (by decide)) a

@[expose] noncomputable def z₄ (b : F) : StatedSp 2 F :=
  elt (RootSubgroupIndex.difference (0 : Fin 2) 1 (by decide)) b

theorem z₁_add (s s' : F) : z₁ (s + s') = z₁ s * z₁ s' := by
  simp only [z₁, neg_add, elt_add]

theorem z₂_add (c c' : F) : z₂ (c + c') = z₂ c * z₂ c' := by
  simp only [z₂, mul_add, elt_add]

theorem z₃_add (a a' : F) : z₃ (a + a') = z₃ a * z₃ a' := elt_add _ a a'

theorem z₄_add (b b' : F) : z₄ (b + b') = z₄ b * z₄ b' := elt_add _ b b'

theorem z₂_comm_z₁ (c s : F) : z₂ c * z₁ s = z₁ s * z₂ c := by
  apply mat_injective
  simp only [z₁, z₂, map_mul, mat_elt, E]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply, Matrix.one_apply]

theorem z₂_comm_z₃ (c a : F) : z₂ c * z₃ a = z₃ a * z₂ c := by
  apply mat_injective
  simp only [z₂, z₃, map_mul, mat_elt, E]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply, Matrix.one_apply]

theorem z₂_comm_z₄ (c b : F) : z₂ c * z₄ b = z₄ b * z₂ c := by
  apply mat_injective
  simp only [z₂, z₄, map_mul, mat_elt, E]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply, Matrix.one_apply]

theorem z₁_comm_z₃ (s a : F) : z₁ s * z₃ a = z₃ a * z₁ s := by
  apply mat_injective
  simp only [z₁, z₃, map_mul, mat_elt, E]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply, Matrix.one_apply]

theorem z₃_mul_z₄ (a b : F) : z₃ a * z₄ b = z₄ b * z₃ a * z₂ (a * b) := by
  apply mat_injective
  simp only [z₂, z₃, z₄, map_mul, mat_elt, E]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply, Matrix.one_apply]
  ring

theorem z₁_mul_z₄ (h2 : (2 : F) ≠ 0) (s b : F) :
    z₁ s * z₄ b = z₄ b * z₃ (s * b) * z₂ (s * b ^ 2 / 2) * z₁ s := by
  have e : z₂ (s * b ^ 2 / 2) = elt (RootSubgroupIndex.positiveLong (0 : Fin 2)) (-(s * b ^ 2)) := by
    rw [z₂]
    congr 1
    field_simp
  rw [e]
  apply mat_injective
  simp only [z₁, z₃, z₄, map_mul, mat_elt, E]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply, Matrix.one_apply] <;> ring

theorem entry_normalForm₁ (s c a b : F) :
    mat 2 F (z₁ s * z₂ c * z₃ a * z₄ b) (Sum.inl 0) (Sum.inl 1) = b := by
  simp [z₁, z₂, z₃, z₄, map_mul, mat_elt, E, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

theorem entry_normalForm₂ (s c a b : F) :
    mat 2 F (z₁ s * z₂ c * z₃ a * z₄ b) (Sum.inl 0) (Sum.inr 1) = a := by
  simp [z₁, z₂, z₃, z₄, map_mul, mat_elt, E, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

theorem entry_normalForm₃ (s c a b : F) :
    mat 2 F (z₁ s * z₂ c * z₃ a * z₄ b) (Sum.inl 1) (Sum.inr 1) = -s := by
  simp [z₁, z₂, z₃, z₄, map_mul, mat_elt, E, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]

theorem entry_normalForm₄ (s c a b : F) :
    mat 2 F (z₁ s * z₂ c * z₃ a * z₄ b) (Sum.inl 0) (Sum.inr 0) = -2 * c - a * b := by
  simp [z₁, z₂, z₃, z₄, map_mul, mat_elt, E, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two, Matrix.single_apply, Matrix.one_apply]
  ring

theorem normalForm_inj (h2 : (2 : F) ≠ 0) {s c a b s' c' a' b' : F}
    (h : z₁ s * z₂ c * z₃ a * z₄ b = z₁ s' * z₂ c' * z₃ a' * z₄ b') :
    s = s' ∧ c = c' ∧ a = a' ∧ b = b' := by
  have h1 := entry_normalForm₁ s c a b
  have h2' := entry_normalForm₂ s c a b
  have h3 := entry_normalForm₃ s c a b
  have h4 := entry_normalForm₄ s c a b
  rw [h] at h1 h2' h3 h4
  rw [entry_normalForm₁] at h1
  rw [entry_normalForm₂] at h2'
  rw [entry_normalForm₃] at h3
  rw [entry_normalForm₄] at h4
  obtain rfl : b' = b := h1
  obtain rfl : a' = a := h2'
  refine ⟨(neg_inj.1 h3).symm, ?_, rfl, rfl⟩
  have : (2 : F) * (c - c') = 0 := by linear_combination h4
  have := (mul_eq_zero.1 this).resolve_left h2
  exact sub_eq_zero.1 this

end CFSG.GH74.GLS.SP.Local.ModelCoord
