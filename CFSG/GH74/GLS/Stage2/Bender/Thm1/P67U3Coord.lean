module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

section Coord

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

noncomputable def u3Mat (α β : K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  oddDiag h (1 : Matrix (Fin 1) (Fin 1) K) 1 * oddUni h (fun _ => α) (Matrix.of fun _ _ => β)

variable {h}

theorem u3_barInvT_one : barInvT h (1 : Matrix (Fin 1) (Fin 1) K) = 1 := by
  simp [barInvT, Matrix.map_one _ (map_zero h.bar) (map_one h.bar)]

@[simp] theorem uMat_ee (α β : K) : u3Mat h α β (.inl 0) (.inl 0) = 1 := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_ew (α β : K) : u3Mat h α β (.inl 0) (.inr (.inl 0)) = α := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_ef (α β : K) : u3Mat h α β (.inl 0) (.inr (.inr 0)) = β := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_we (α β : K) : u3Mat h α β (.inr (.inl 0)) (.inl 0) = 0 := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_ww (α β : K) : u3Mat h α β (.inr (.inl 0)) (.inr (.inl 0)) = 1 := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_wf (α β : K) : u3Mat h α β (.inr (.inl 0)) (.inr (.inr 0)) = -h.bar α := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_fe (α β : K) : u3Mat h α β (.inr (.inr 0)) (.inl 0) = 0 := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_fw (α β : K) : u3Mat h α β (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
  simp [u3Mat, oddDiag_mul_oddUni]
@[simp] theorem uMat_ff (α β : K) : u3Mat h α β (.inr (.inr 0)) (.inr (.inr 0)) = 1 := by
  simp [u3Mat, oddDiag_mul_oddUni, u3_barInvT_one]


theorem mul_uMat_apply (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (a b : K) (i : HypIndex 1 1) :
    (A * u3Mat h a b) i (.inl 0) = A i (.inl 0) ∧
    (A * u3Mat h a b) i (.inr (.inl 0)) = A i (.inl 0) * a + A i (.inr (.inl 0)) ∧
    (A * u3Mat h a b) i (.inr (.inr 0)) =
      A i (.inl 0) * b - A i (.inr (.inl 0)) * h.bar a + A i (.inr (.inr 0)) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
    try ring

theorem uMat_mul_apply (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (α β : K) (j : HypIndex 1 1) :
    (u3Mat h α β * A) (.inl 0) j =
      A (.inl 0) j + α * A (.inr (.inl 0)) j + β * A (.inr (.inr 0)) j ∧
    (u3Mat h α β * A) (.inr (.inl 0)) j = A (.inr (.inl 0)) j - h.bar α * A (.inr (.inr 0)) j ∧
    (u3Mat h α β * A) (.inr (.inr 0)) j = A (.inr (.inr 0)) j := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
    try ring

omit [Field K] in
theorem u3_hyp3_forall {P : HypIndex 1 1 → Prop} (h1 : P (.inl 0)) (h2 : P (.inr (.inl 0)))
    (h3 : P (.inr (.inr 0))) : ∀ i, P i := by
  intro i
  rcases i with i | i | i
  · rw [Subsingleton.elim i 0]; exact h1
  · rw [Subsingleton.elim i 0]; exact h2
  · rw [Subsingleton.elim i 0]; exact h3

omit [Field K] in
theorem u3_hyp3_matrix_ext {M N : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hee : M (.inl 0) (.inl 0) = N (.inl 0) (.inl 0))
    (hew : M (.inl 0) (.inr (.inl 0)) = N (.inl 0) (.inr (.inl 0)))
    (hef : M (.inl 0) (.inr (.inr 0)) = N (.inl 0) (.inr (.inr 0)))
    (hwe : M (.inr (.inl 0)) (.inl 0) = N (.inr (.inl 0)) (.inl 0))
    (hww : M (.inr (.inl 0)) (.inr (.inl 0)) = N (.inr (.inl 0)) (.inr (.inl 0)))
    (hwf : M (.inr (.inl 0)) (.inr (.inr 0)) = N (.inr (.inl 0)) (.inr (.inr 0)))
    (hfe : M (.inr (.inr 0)) (.inl 0) = N (.inr (.inr 0)) (.inl 0))
    (hfw : M (.inr (.inr 0)) (.inr (.inl 0)) = N (.inr (.inr 0)) (.inr (.inl 0)))
    (hff : M (.inr (.inr 0)) (.inr (.inr 0)) = N (.inr (.inr 0)) (.inr (.inr 0))) : M = N := by
  ext i j
  revert j
  refine u3_hyp3_forall (P := fun i => ∀ j, M i j = N i j) ?_ ?_ ?_ i
  · exact u3_hyp3_forall hee hew hef
  · exact u3_hyp3_forall hwe hww hwf
  · exact u3_hyp3_forall hfe hfw hff

theorem u3_blockTriangular_of_hyp3 {A : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hwe : A (.inr (.inl 0)) (.inl 0) = 0) (hfe : A (.inr (.inr 0)) (.inl 0) = 0)
    (hfw : A (.inr (.inr 0)) (.inr (.inl 0)) = 0) : A.BlockTriangular fullPos := by
  intro i j hij
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    rw [Subsingleton.elim i 0] at hij ⊢ <;> rw [Subsingleton.elim j 0] at hij ⊢ <;>
    first | exact hwe | exact hfe | exact hfw | (simp at hij)

theorem uMat_zero_comm (β α' β' : K) :
    u3Mat h 0 β * u3Mat h α' β' = u3Mat h α' β' * u3Mat h 0 β := by
  refine u3_hyp3_matrix_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · simp [Matrix.mul_apply, Fintype.sum_sum_type]
    try ring

theorem uMat_map (σ : K ≃+* K) (α β : K) : (u3Mat h α β).map σ = u3Mat h (σ α) (σ β) := by
  refine u3_hyp3_matrix_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  · simp [map_bar_comm h σ α]

theorem exists_uMat_of_mem (g : hypSU h 1 1) (hg : g ∈ hypUnitriangular h 1 1) :
    ∃ α β : K, β + h.bar β = -(α * h.bar α) ∧
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h α β := by
  obtain ⟨A, C, x, hA, hC, hM⟩ :=
    (exists_mem_hypUnitriangular_odd_iff (h := h) (r := 1) _).mp ⟨g, hg, rfl⟩
  have hA1 : A = 1 := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa using hA.2 0
  refine ⟨x 0, C 0 0, ?_, ?_⟩
  · have := congrFun (congrFun hC 0) 0
    simpa [Matrix.add_apply, vecMulVec_apply] using this
  · rw [hM, hA1]
    have hx : x = fun _ => x 0 := by
      funext i
      rw [Subsingleton.elim i 0]
    have hC' : C = Matrix.of fun _ _ => C 0 0 := by
      ext i j
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp
    rw [u3Mat, ← hx, ← hC']

theorem exists_mem_of_uMat {α β : K} (hαβ : β + h.bar β = -(α * h.bar α)) :
    ∃ g : hypSU h 1 1, g ∈ hypUnitriangular h 1 1 ∧
      ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = u3Mat h α β := by
  have hC : (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => β) +
      ((Matrix.of fun (_ : Fin 1) (_ : Fin 1) => β).map h.bar)ᵀ =
      -vecMulVec (fun _ : Fin 1 => α) (fun j => h.bar ((fun _ : Fin 1 => α) j)) := by
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.add_apply, vecMulVec_apply] using hαβ
  obtain ⟨g, hg, hM⟩ := (exists_mem_hypUnitriangular_odd_iff (h := h) (r := 1)
    (u3Mat h α β)).mpr ⟨1, Matrix.of fun _ _ => β, fun _ => α,
      ⟨Matrix.blockTriangular_one, fun i => by simp⟩, hC, rfl⟩
  exact ⟨g, hg, hM⟩

theorem u3_fix_entries_central {A : Matrix (HypIndex 1 1) (HypIndex 1 1) K} {b β : K} (hβ : β ≠ 0)
    (hb : b ≠ 0) (hEq : A * u3Mat h 0 b = u3Mat h 0 β * A) :
    A (.inr (.inl 0)) (.inl 0) = 0 ∧ A (.inr (.inr 0)) (.inl 0) = 0 ∧
      A (.inr (.inr 0)) (.inr (.inl 0)) = 0 ∧
      b * A (.inl 0) (.inl 0) = β * A (.inr (.inr 0)) (.inr (.inr 0)) := by
  have hee := congrFun (congrFun hEq (.inl 0)) (.inl 0)
  have hew := congrFun (congrFun hEq (.inl 0)) (.inr (.inl 0))
  have hwf := congrFun (congrFun hEq (.inr (.inl 0))) (.inr (.inr 0))
  have hef := congrFun (congrFun hEq (.inl 0)) (.inr (.inr 0))
  rw [(mul_uMat_apply _ _ _ _).1, (uMat_mul_apply _ _ _ _).1] at hee
  rw [(mul_uMat_apply _ _ _ _).2.1, (uMat_mul_apply _ _ _ _).1] at hew
  rw [(mul_uMat_apply _ _ _ _).2.2, (uMat_mul_apply _ _ _ _).2.1] at hwf
  rw [(mul_uMat_apply _ _ _ _).2.2, (uMat_mul_apply _ _ _ _).1] at hef
  have hfe : A (.inr (.inr 0)) (.inl 0) = 0 := by
    have : β * A (.inr (.inr 0)) (.inl 0) = 0 := by linear_combination -hee
    exact (mul_eq_zero.mp this).resolve_left hβ
  have hfw : A (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
    have : β * A (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
      simp only [mul_zero, zero_mul, add_zero, zero_add] at hew
      linear_combination -hew
    exact (mul_eq_zero.mp this).resolve_left hβ
  have hwe : A (.inr (.inl 0)) (.inl 0) = 0 := by
    have : b * A (.inr (.inl 0)) (.inl 0) = 0 := by
      simp only [map_zero, mul_zero, zero_mul, sub_zero] at hwf
      linear_combination hwf
    exact (mul_eq_zero.mp this).resolve_left hb
  refine ⟨hwe, hfe, hfw, ?_⟩
  simp only [map_zero, mul_zero, zero_mul, add_zero, sub_zero] at hef
  linear_combination hef

theorem u3_fix_entries_regular {A : Matrix (HypIndex 1 1) (HypIndex 1 1) K} {a b α β : K}
    (hα : α ≠ 0) (hEq : A * u3Mat h a b = u3Mat h α β * A) :
    A (.inr (.inl 0)) (.inl 0) = 0 ∧ A (.inr (.inr 0)) (.inl 0) = 0 ∧
      A (.inr (.inr 0)) (.inr (.inl 0)) = 0 ∧
      a * A (.inl 0) (.inl 0) = α * A (.inr (.inl 0)) (.inr (.inl 0)) ∧
      h.bar a * A (.inr (.inl 0)) (.inr (.inl 0)) =
        h.bar α * A (.inr (.inr 0)) (.inr (.inr 0)) := by
  have hbα : h.bar α ≠ 0 := fun h0 => hα (by simpa using (h.bar.injective (by rw [h0, map_zero])))
  have hwe' := congrFun (congrFun hEq (.inr (.inl 0))) (.inl 0)
  have hee := congrFun (congrFun hEq (.inl 0)) (.inl 0)
  have hww := congrFun (congrFun hEq (.inr (.inl 0))) (.inr (.inl 0))
  have hew := congrFun (congrFun hEq (.inl 0)) (.inr (.inl 0))
  have hwf := congrFun (congrFun hEq (.inr (.inl 0))) (.inr (.inr 0))
  rw [(mul_uMat_apply _ _ _ _).1, (uMat_mul_apply _ _ _ _).2.1] at hwe'
  rw [(mul_uMat_apply _ _ _ _).1, (uMat_mul_apply _ _ _ _).1] at hee
  rw [(mul_uMat_apply _ _ _ _).2.1, (uMat_mul_apply _ _ _ _).2.1] at hww
  rw [(mul_uMat_apply _ _ _ _).2.1, (uMat_mul_apply _ _ _ _).1] at hew
  rw [(mul_uMat_apply _ _ _ _).2.2, (uMat_mul_apply _ _ _ _).2.1] at hwf
  have hfe : A (.inr (.inr 0)) (.inl 0) = 0 := by
    have : h.bar α * A (.inr (.inr 0)) (.inl 0) = 0 := by linear_combination hwe'
    exact (mul_eq_zero.mp this).resolve_left hbα
  have hwe : A (.inr (.inl 0)) (.inl 0) = 0 := by
    have : α * A (.inr (.inl 0)) (.inl 0) = 0 := by
      rw [hfe] at hee
      linear_combination -hee
    exact (mul_eq_zero.mp this).resolve_left hα
  have hfw : A (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
    have : h.bar α * A (.inr (.inr 0)) (.inr (.inl 0)) = 0 := by
      rw [hwe] at hww
      linear_combination hww
    exact (mul_eq_zero.mp this).resolve_left hbα
  refine ⟨hwe, hfe, hfw, ?_, ?_⟩
  · rw [hfw] at hew
    linear_combination hew
  · rw [hwe] at hwf
    linear_combination -hwf


theorem u3_diag_ne_zero_of_blockTriangular {A : GL (HypIndex 1 1) K}
    (hA : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos)
    (a : HypIndex 1 1) : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) a a ≠ 0 := by
  have := mul_apply_self_of_blockTriangular fullPos_injective hA (blockTriangular_inv_fullPos hA) a
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq] at this
  intro h0
  rw [h0, zero_mul] at this
  exact one_ne_zero this

theorem u3_conj_mem_fullUnitriangular {A : GL (HypIndex 1 1) K}
    (hA : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos) (σ : K ≃+* K)
    {g : GL (HypIndex 1 1) K} (hg : g ∈ fullUnitriangular 1 1 K) :
    A * glAut σ g * A⁻¹ ∈ fullUnitriangular 1 1 K := by
  have hgσ : ((glAut σ g : GL (HypIndex 1 1) K) :
      Matrix (HypIndex 1 1) (HypIndex 1 1) K).BlockTriangular fullPos := by
    intro i j hij
    rw [coe_glAut, Matrix.map_apply, hg.1 hij, map_zero]
  have hAi := blockTriangular_inv_fullPos hA
  refine ⟨?_, fun a => ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact (hA.mul hgσ).mul hAi
  · rw [Units.val_mul, Units.val_mul,
      mul_apply_self_of_blockTriangular fullPos_injective (hA.mul hgσ) hAi,
      mul_apply_self_of_blockTriangular fullPos_injective hA hgσ, coe_glAut, Matrix.map_apply,
      hg.2, map_one, mul_one]
    have := mul_apply_self_of_blockTriangular fullPos_injective hA hAi a
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq] at this
    exact this.symm

theorem u3_fullUnitriangular_pow_prime [Fact p.Prime] [CharP K p] (hp : p ≠ 2)
    {g : GL (HypIndex 1 1) K} (hg : g ∈ fullUnitriangular 1 1 K) : g ^ p = 1 := by
  have hwe : (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inl 0)) (.inl 0) = 0 :=
    hg.1 (by simp)
  have hfe : (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inl 0) = 0 :=
    hg.1 (by simp)
  have hfw : (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (.inr (.inr 0)) (.inr (.inl 0)) = 0 :=
    hg.1 (by simp)
  have hee := hg.2 (.inl 0)
  have hww := hg.2 (.inr (.inl 0))
  have hff := hg.2 (.inr (.inr 0))
  set M : Matrix (HypIndex 1 1) (HypIndex 1 1) K := (g : Matrix (HypIndex 1 1) (HypIndex 1 1) K)
    with hM
  set N : Matrix (HypIndex 1 1) (HypIndex 1 1) K := M - 1 with hN
  have hN3 : N ^ 3 = 0 := by
    refine u3_hyp3_matrix_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    · simp [hN, pow_succ, Matrix.mul_apply, Fintype.sum_sum_type, hwe, hfe, hfw, hee, hww, hff]
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hNp : N ^ p = 0 := pow_eq_zero_of_le hp3 hN3
  have hMp : M ^ p = 1 := by
    have : M = 1 + N := by rw [hN]; abel
    rw [this, add_pow_char_of_commute (p := p) (Commute.one_left N), one_pow, hNp, add_zero]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hMp)


theorem uMat_zero_zero : u3Mat h 0 0 = 1 := by
  refine u3_hyp3_matrix_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp

end Coord

end CFSG.GH74.GLS.Stage2.Bender.Thm1
