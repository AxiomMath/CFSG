module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15InnerL4X

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4

open Matrix CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mem_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {w : G} (hw : w ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = w := by
  let S : Subgroup G :=
    { carrier := {w | ∃ a ∈ A, ∃ b ∈ B, a * b = w}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [h a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc a⁻¹ * b⁻¹ = (b * a)⁻¹ := by group
          _ = (a * b)⁻¹ := by rw [h a ha b hb] }
  have : A ⊔ B ≤ S := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩)
  exact this hw

theorem blk_mul (A B C D : SL(2, F)) : blk A B * blk C D = blk (A * C) (B * D) := by
  unfold blk
  calc blockSL F 4 2 0 (by norm_num) A * blockSL F 4 2 2 (by norm_num) B *
        (blockSL F 4 2 0 (by norm_num) C * blockSL F 4 2 2 (by norm_num) D)
      = blockSL F 4 2 0 (by norm_num) A * (blockSL F 4 2 2 (by norm_num) B *
          blockSL F 4 2 0 (by norm_num) C) * blockSL F 4 2 2 (by norm_num) D := by group
    _ = blockSL F 4 2 0 (by norm_num) A * (blockSL F 4 2 0 (by norm_num) C *
          blockSL F 4 2 2 (by norm_num) B) * blockSL F 4 2 2 (by norm_num) D := by
        rw [← blockSL_comm C B]
    _ = blockSL F 4 2 0 (by norm_num) (A * C) * blockSL F 4 2 2 (by norm_num) (B * D) := by
        rw [map_mul, map_mul]
        group

theorem blk_one : (blk 1 1 : SL(4, F)) = 1 := by
  simp [blk]

theorem blk_inv (A B : SL(2, F)) : (blk A B)⁻¹ = blk A⁻¹ B⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [blk_mul, mul_inv_cancel, mul_inv_cancel, blk_one])

theorem sl2_sq_one (h2 : (2 : F) ≠ 0) (r : SL(2, F))
    (h : (r : Matrix (Fin 2) (Fin 2) F) * r = 1) :
    (r : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (r : Matrix (Fin 2) (Fin 2) F) = -1 := by
  obtain ⟨a, b, c, d, hM⟩ : ∃ a b c d : F, (r : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c = 1 := by
    have := r.2
    rw [hM, Matrix.det_fin_two_of] at this
    exact this
  rw [hM] at h ⊢
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hs : a + d ≠ 0 := by
    intro hs
    have hd : d = -a := by linear_combination hs
    rw [hd] at hdet
    apply h2
    linear_combination (-1 : F) * (e00 + hdet)
  have hb : b = 0 := by
    have : b * (a + d) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right hs
  have hc : c = 0 := by
    have : c * (a + d) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right hs
  subst hb hc
  have ha2 : a * a = 1 := by linear_combination e00
  have had : a * d = 1 := by linear_combination hdet
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one ha2
  have hda : d = a := by
    have : a * d = a * a := by rw [had, ha2]
    exact mul_left_cancel₀ ha0 this
  subst hda
  rcases mul_self_eq_one_iff.mp ha2 with h1 | h1
  · left
    rw [h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · right
    rw [h1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem sl2_sq_cases (h2 : (2 : F) ≠ 0) (r : SL(2, F)) {μ : F}
    (h : (r : Matrix (Fin 2) (Fin 2) F) * r = μ • 1) :
    (μ = 1 ∧ ((r : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (r : Matrix (Fin 2) (Fin 2) F) = -1)) ∨
      (μ = -1 ∧ (r : Matrix (Fin 2) (Fin 2) F) * r = -1) := by
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, r.2, Matrix.det_smul, Matrix.det_one] at hdet
  have hμ : μ * μ = 1 := by
    simpa [sq] using hdet.symm
  rcases mul_self_eq_one_iff.mp hμ with h1 | h1
  · left
    refine ⟨h1, sl2_sq_one h2 r ?_⟩
    rw [h, h1, one_smul]
  · right
    refine ⟨h1, ?_⟩
    rw [h, h1, neg_one_smul]

theorem classify_w [Finite F] (h2 : (2 : F) ≠ 0) {w : SL(4, F)} (hw : w ∈ R0 F ⊔ R0' F)
    (hw2 : w * w ∈ Subgroup.center SL(4, F)) :
    w = 1 ∨ w = x0 F ∨ w = zneg F * x0 F ∨ w = zneg F ∨
      ∃ h ∈ R0 F ⊔ R0' F, w = h * u0 F * h⁻¹ := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_comm (fun a ha b hb => R0_comm_R0' ha hb) hw
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨r', rfl⟩ := hb
  have hwb : w = blk r r' := hab.symm
  subst hwb
  rw [blk_mul] at hw2
  obtain ⟨μ, -, hμ⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hw2
  rw [coe_blk] at hμ
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hμ
  have f00 := congrFun (congrFun hμ 0) 0
  have f01 := congrFun (congrFun hμ 0) 1
  have f10 := congrFun (congrFun hμ 1) 0
  have f11 := congrFun (congrFun hμ 1) 1
  have g22 := congrFun (congrFun hμ 2) 2
  have g23 := congrFun (congrFun hμ 2) 3
  have g32 := congrFun (congrFun hμ 3) 2
  have g33 := congrFun (congrFun hμ 3) 3
  simp [Matrix.scalar_apply] at f00 f01 f10 f11 g22 g23 g32 g33
  have hrr : (r : Matrix (Fin 2) (Fin 2) F) * r = μ • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← f00, ← f01, ← f10, ← f11]
  have hrr' : (r' : Matrix (Fin 2) (Fin 2) F) * r' = μ • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← g22, ← g23, ← g32, ← g33]
  rcases sl2_sq_cases h2 r hrr with ⟨hμ1, hr1 | hr1⟩ | ⟨hμ1, hr1⟩ <;>
    rcases sl2_sq_cases h2 r' hrr' with ⟨hμ1', hr1' | hr1'⟩ | ⟨hμ1', hr1'⟩
  · left
    apply Subtype.ext
    rw [coe_blk, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hr1, hr1']
  · right; right; left
    apply Subtype.ext
    rw [coe_blk, Matrix.SpecialLinearGroup.coe_mul, coe_zneg, coe_x0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hr1, hr1']
  · exfalso
    apply h2
    linear_combination hμ1' - hμ1
  · right; left
    apply Subtype.ext
    rw [coe_blk, coe_x0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hr1, hr1']
  · right; right; right; left
    apply Subtype.ext
    rw [coe_blk, coe_zneg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hr1, hr1']
  · exfalso
    apply h2
    linear_combination hμ1' - hμ1
  · exfalso
    apply h2
    linear_combination hμ1 - hμ1'
  · exfalso
    apply h2
    linear_combination hμ1 - hμ1'
  · obtain ⟨h₁, hh₁⟩ := exists_conj_r0 h2 r hr1
    obtain ⟨h₂, hh₂⟩ := exists_conj_r0 h2 r' hr1'
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨blk h₁ h₂, blk_mem _ _, ?_⟩)))
    rw [u0_eq_blk, blk_inv, blk_mul, blk_mul, hh₁, hh₂]

end CFSG.ClassicalInvolution.ModelFacts.Orth15.InnerL4
