module

public import CFSG.ClassicalInvolution.Phan.AutSU2
public import CFSG.ClassicalInvolution.WeakCT.Torus

public section

namespace CFSG.ClassicalInvolution.WeakCT

open Matrix
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open scoped MatrixGroups

section Automorphisms

variable {K : Type} [Field K]

@[expose] def fieldAutSL (ψ : K ≃+* K) (d : ℕ) : SL(d, K) ≃* SL(d, K) :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map (ψ : K →+* K))
    (Matrix.SpecialLinearGroup.map (ψ.symm : K →+* K))
    (by
      ext A i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply])
    (by
      ext A i j
      simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply])

theorem coe_fieldAutSL (ψ : K ≃+* K) (d : ℕ) (A : SL(d, K)) :
    ((fieldAutSL ψ d A : SL(d, K)) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) K).map ψ :=
  rfl

@[expose] def conjSL {d : ℕ} (g g' : Matrix (Fin d) (Fin d) K) (h : g * g' = 1) :
    SL(d, K) ≃* SL(d, K) where
  toFun A := ⟨g * A * g', by
    have hdet : g.det * g'.det = 1 := by rw [← det_mul, h, det_one]
    rw [det_mul, det_mul, A.2, mul_one, hdet]⟩
  invFun A := ⟨g' * A * g, by
    have hdet : g'.det * g.det = 1 := by rw [← det_mul, mul_eq_one_comm.mp h, det_one]
    rw [det_mul, det_mul, A.2, mul_one, hdet]⟩
  left_inv A := by
    refine Subtype.ext ?_
    show g' * (g * (A : Matrix (Fin d) (Fin d) K) * g') * g = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp h, Matrix.one_mul,
      Matrix.mul_assoc, mul_eq_one_comm.mp h, Matrix.mul_one]
  right_inv A := by
    refine Subtype.ext ?_
    show g * (g' * (A : Matrix (Fin d) (Fin d) K) * g) * g' = A
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.one_mul, Matrix.mul_assoc, h,
      Matrix.mul_one]
  map_mul' A B := by
    refine Subtype.ext ?_
    show g * ((A : Matrix (Fin d) (Fin d) K) * B) * g' =
      g * (A : Matrix (Fin d) (Fin d) K) * g' * (g * (B : Matrix (Fin d) (Fin d) K) * g')
    have hg : g' * g = 1 := mul_eq_one_comm.mp h
    calc g * ((A : Matrix (Fin d) (Fin d) K) * B) * g'
        = g * (A : Matrix (Fin d) (Fin d) K) * 1 * B * g' := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = g * (A : Matrix (Fin d) (Fin d) K) * (g' * g) * B * g' := by rw [hg]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem coe_conjSL {d : ℕ} (g g' : Matrix (Fin d) (Fin d) K) (h : g * g' = 1) (A : SL(d, K)) :
    ((conjSL g g' h A : SL(d, K)) : Matrix (Fin d) (Fin d) K) = g * A * g' :=
  rfl

theorem transposeSL_mul {d : ℕ} (A B : SL(d, K)) :
    (A * B).transpose = B.transpose * A.transpose :=
  Subtype.ext (Matrix.transpose_mul _ _)

theorem transposeSL_one {d : ℕ} : (1 : SL(d, K)).transpose = 1 :=
  Subtype.ext Matrix.transpose_one

theorem transposeSL_transpose {d : ℕ} (A : SL(d, K)) : A.transpose.transpose = A :=
  Subtype.ext (Matrix.transpose_transpose _)

theorem transposeSL_inv {d : ℕ} (A : SL(d, K)) : (A.transpose)⁻¹ = (A⁻¹).transpose :=
  inv_eq_of_mul_eq_one_right (by rw [← transposeSL_mul, inv_mul_cancel, transposeSL_one])

@[expose] def invTransposeSL (d : ℕ) : SL(d, K) ≃* SL(d, K) where
  toFun A := (A⁻¹).transpose
  invFun A := (A⁻¹).transpose
  left_inv A := by
    show (((A⁻¹).transpose)⁻¹).transpose = A
    rw [transposeSL_inv, inv_inv, transposeSL_transpose]
  right_inv A := by
    show (((A⁻¹).transpose)⁻¹).transpose = A
    rw [transposeSL_inv, inv_inv, transposeSL_transpose]
  map_mul' A B := by
    show ((A * B)⁻¹).transpose = (A⁻¹).transpose * (B⁻¹).transpose
    rw [_root_.mul_inv_rev, transposeSL_mul]

theorem coe_invTransposeSL {d : ℕ} (A : SL(d, K)) :
    ((invTransposeSL d A : SL(d, K)) : Matrix (Fin d) (Fin d) K) =
      ((A⁻¹ : SL(d, K)) : Matrix (Fin d) (Fin d) K)ᵀ :=
  rfl

end Automorphisms

section BlockCompat

variable {K : Type} [Field K] {m k i : ℕ}

theorem map_blockMat (f : K →+* K) (A : Matrix (Fin k) (Fin k) K) :
    (blockMat m i A).map f = blockMat m i (A.map f) := by
  ext a b
  rw [Matrix.map_apply, blockMat_apply, blockMat_apply]
  split_ifs with h
  · rfl
  · simp only [Matrix.one_apply]
    split_ifs <;> simp

theorem transpose_blockMat (A : Matrix (Fin k) (Fin k) K) :
    (blockMat m i A)ᵀ = blockMat m i Aᵀ := by
  unfold blockMat
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_assoc]

theorem fieldAutSL_blockSL (ψ : K ≃+* K) (h : i + k ≤ m) (A : SL(k, K)) :
    fieldAutSL ψ m (blockSL K m k i h A) = blockSL K m k i h (fieldAutSL ψ k A) :=
  Subtype.ext (map_blockMat (ψ : K →+* K) _)

theorem invTransposeSL_blockSL (h : i + k ≤ m) (A : SL(k, K)) :
    invTransposeSL m (blockSL K m k i h A) = blockSL K m k i h (invTransposeSL k A) := by
  show ((blockSL K m k i h A)⁻¹).transpose = blockSL K m k i h ((A⁻¹).transpose)
  rw [← map_inv]
  exact Subtype.ext (transpose_blockMat _)

end BlockCompat

section DiagConj

variable {K : Type} [Field K]

theorem diag2_mul_diag2 (a b : Kˣ) :
    Matrix.diagonal ![(a : K), (b : K)] * Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] =
      (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem diag3_mul_diag3 (a b : Kˣ) :
    Matrix.diagonal ![(a : K), (b : K), 1] *
        Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K), 1] =
      (1 : Matrix (Fin 3) (Fin 3) K) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] def diagConj2 (a b : Kˣ) : SL(2, K) ≃* SL(2, K) :=
  conjSL (Matrix.diagonal ![(a : K), (b : K)])
    (Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)]) (diag2_mul_diag2 a b)

@[expose] def diagConj3 (a b : Kˣ) : SL(3, K) ≃* SL(3, K) :=
  conjSL (Matrix.diagonal ![(a : K), (b : K), 1])
    (Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K), 1]) (diag3_mul_diag3 a b)

theorem coe_diagConj2 (a b : Kˣ) (A : SL(2, K)) :
    ((diagConj2 a b A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(a : K), (b : K)] * A *
        Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] :=
  rfl

theorem coe_diagConj3 (a b : Kˣ) (A : SL(3, K)) :
    ((diagConj3 a b A : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(a : K), (b : K), 1] * A *
        Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K), 1] :=
  rfl

theorem diagConj3_blockSL_zero (a b : Kˣ) (A : SL(2, K)) :
    diagConj3 a b (blockSL K 3 2 0 (by omega) A) =
      blockSL K 3 2 0 (by omega) (diagConj2 a b A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagConj3, coe_diagConj2, coe_blockSL_three_zero, Matrix.mul_apply,
      Matrix.diagonal_apply]

theorem diagConj3_blockSL_one (a b : Kˣ) (A : SL(2, K)) :
    diagConj3 a b (blockSL K 3 2 1 (by omega) A) =
      blockSL K 3 2 1 (by omega) (diagConj2 b 1 A) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagConj3, coe_diagConj2, coe_blockSL_three_one, Matrix.mul_apply,
      Matrix.diagonal_apply]

end DiagConj

section Shape

variable {K : Type} [Field K]

theorem eq_zero_of_mul_sub_eq_zero {x c d : K} (h : x * (c - d) = 0) (hcd : c ≠ d) : x = 0 :=
  (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hcd)

theorem monomial_shape {σ t : Kˣ} (hσ : σ ^ 2 ≠ 1) (G : GL (Fin 2) K)
    (h : ((torusHom K t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) * (G : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) * ((torusHom K σ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) :
    ((G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) ∨
      ((G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 ∧ (G : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, coe_torusHom] at e00 e01 e10 e11
  set g : Matrix (Fin 2) (Fin 2) K := (G : Matrix (Fin 2) (Fin 2) K) with hg
  have hs0 : (σ : K) ≠ 0 := σ.ne_zero
  have ht0 : (t : K) ≠ 0 := t.ne_zero
  have hs2 : (σ : K) ≠ (σ : K)⁻¹ := by
    intro h2
    apply hσ
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_two]
    nth_rewrite 1 [h2]
    exact inv_mul_cancel₀ hs0
  have hdet : g.det ≠ 0 := by
    have := (Matrix.isUnits_det_units G).ne_zero
    exact this
  by_cases h1 : (t : K) = σ
  · left
    rw [h1] at e01 e10
    refine ⟨eq_zero_of_mul_sub_eq_zero (c := (σ : K)) (d := (σ : K)⁻¹) ?_ hs2,
      eq_zero_of_mul_sub_eq_zero (c := (σ : K)) (d := (σ : K)⁻¹) ?_ hs2⟩
    · linear_combination e01
    · field_simp at e10
      field_simp
      linear_combination -e10
  · by_cases h2 : (t : K) = (σ : K)⁻¹
    · right
      rw [h2] at e00 e11
      refine ⟨eq_zero_of_mul_sub_eq_zero (c := (σ : K)⁻¹) (d := (σ : K)) ?_ hs2.symm,
        eq_zero_of_mul_sub_eq_zero (c := (σ : K)) (d := (σ : K)⁻¹) ?_ hs2⟩
      · linear_combination e00
      · field_simp at e11
        field_simp
        linear_combination e11
    · exfalso
      apply hdet
      have g00 : g 0 0 = 0 :=
        eq_zero_of_mul_sub_eq_zero (c := (t : K)) (d := (σ : K)) (by linear_combination e00) h1
      have g01 : g 0 1 = 0 :=
        eq_zero_of_mul_sub_eq_zero (c := (t : K)) (d := (σ : K)⁻¹) (by linear_combination e01) h2
      rw [Matrix.det_fin_two, g00, g01]
      ring

theorem exists_diagonal_of_offDiag_zero (G : GL (Fin 2) K)
    (h01 : (G : Matrix (Fin 2) (Fin 2) K) 0 1 = 0) (h10 : (G : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    ∃ a b : Kˣ, (G : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![(a : K), (b : K)] ∧
      ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  set g : Matrix (Fin 2) (Fin 2) K := (G : Matrix (Fin 2) (Fin 2) K) with hg
  have hdet : g.det ≠ 0 := (Matrix.isUnits_det_units G).ne_zero
  rw [Matrix.det_fin_two, h01, h10] at hdet
  have h00 : g 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have h11 : g 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hgd : g = Matrix.diagonal ![g 0 0, g 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 2) (Fin 2) K,
      P = ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hinv : g * P = 1 := by rw [hP]; exact G.mul_inv
  refine ⟨Units.mk0 (g 0 0) h00, Units.mk0 (g 1 1) h11, hgd, ?_⟩
  rw [← hP]
  rw [hgd] at hinv
  ext i j
  have e := congrFun (congrFun hinv i) j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply] at e ⊢
  · exact eq_inv_of_mul_eq_one_right e
  · exact e.resolve_left h00
  · exact e.resolve_left h11
  · exact eq_inv_of_mul_eq_one_right e

theorem exists_diagonal_of_diag_zero (G : GL (Fin 2) K)
    (h00 : (G : Matrix (Fin 2) (Fin 2) K) 0 0 = 0) (h11 : (G : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    ∃ a b : Kˣ, ∀ M : Matrix (Fin 2) (Fin 2) K,
      (G : Matrix (Fin 2) (Fin 2) K) * M * ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        Matrix.diagonal ![(a : K), (b : K)] * (M.adjugate)ᵀ *
          Matrix.diagonal ![((a⁻¹ : Kˣ) : K), ((b⁻¹ : Kˣ) : K)] := by
  set g : Matrix (Fin 2) (Fin 2) K := (G : Matrix (Fin 2) (Fin 2) K) with hg
  have hdet : g.det ≠ 0 := (Matrix.isUnits_det_units G).ne_zero
  rw [Matrix.det_fin_two, h00, h11] at hdet
  have h01 : g 0 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have h10 : g 1 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hgd : g = !![0, g 0 1; g 1 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11]
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin 2) (Fin 2) K,
      P = ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := ⟨_, rfl⟩
  have hinv : g * P = 1 := by rw [hP]; exact G.mul_inv
  have hPd : P 0 0 = 0 ∧ P 1 1 = 0 ∧ P 0 1 = (g 1 0)⁻¹ ∧ P 1 0 = (g 0 1)⁻¹ := by
    rw [hgd] at hinv
    have e00 := congrFun (congrFun hinv 0) 0
    have e01 := congrFun (congrFun hinv 0) 1
    have e10 := congrFun (congrFun hinv 1) 0
    have e11 := congrFun (congrFun hinv 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    exact ⟨e10.resolve_left h10, e01.resolve_left h01, eq_inv_of_mul_eq_one_right e11,
      eq_inv_of_mul_eq_one_right e00⟩
  obtain ⟨hP00, hP11, hP01, hP10⟩ := hPd
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, (a : K) = g 0 1 := ⟨Units.mk0 _ h01, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Kˣ, (b : K) = -g 1 0 := ⟨Units.mk0 _ (neg_ne_zero.mpr h10), rfl⟩
  refine ⟨a, b, fun M => ?_⟩
  rw [← hP]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, h00, h11, hP00, hP11, hP01, hP10, ha, hb]

end Shape

section Extend

variable {K : Type} [Field K]

theorem map_torusHom (ψ : K ≃+* K) (s : Kˣ) :
    Matrix.SpecialLinearGroup.map (ψ : K →+* K) (torusHom K s) =
      torusHom K (Units.map (ψ : K →* K) s) := by
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_torusHom]

variable [Finite K]

theorem exists_unit_sq_ne_one (hK : 4 ≤ Nat.card K) : ∃ s : Kˣ, s ^ 2 ≠ 1 := by
  by_contra! h
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (h g)
  have h3 : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem map_B23_eq (β : SL(3, K) ≃* SL(3, K))
    (h : ∀ C : SL(2, K), β (blockSL K 3 2 1 (by omega) C) ∈ B23 K) :
    (B23 K).map β.toMonoidHom = B23 K := by
  have hle : (B23 K).map β.toMonoidHom ≤ B23 K := by
    rintro _ ⟨_, ⟨C, rfl⟩, rfl⟩
    exact h C
  exact Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective β.injective])

theorem exists_extend (hK : 4 ≤ Nat.card K) (α : SL(2, K) ≃* SL(2, K))
    (hα : (diagTorus2 K).map α.toMonoidHom ≤ diagTorus2 K) :
    ∃ β : SL(3, K) ≃* SL(3, K),
      (∀ A, β (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A)) ∧
        (B23 K).map β.toMonoidHom = B23 K := by
  obtain ⟨G, ψ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map α
  obtain ⟨s₀, hs₀⟩ := exists_unit_sq_ne_one hK
  obtain ⟨t, ht⟩ : α (torusHom K s₀) ∈ diagTorus2 K := hα ⟨_, ⟨s₀, rfl⟩, rfl⟩
  have hGd := hG (torusHom K s₀)
  rw [← ht, map_torusHom] at hGd
  have hmat : ((torusHom K t : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
      (G : Matrix (Fin 2) (Fin 2) K) = (G : Matrix (Fin 2) (Fin 2) K) *
        ((torusHom K (Units.map (ψ : K →* K) s₀) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    have h1 : Matrix.SpecialLinearGroup.toGL (torusHom K t) * G =
        G * Matrix.SpecialLinearGroup.toGL (torusHom K (Units.map (ψ : K →* K) s₀)) := by
      calc Matrix.SpecialLinearGroup.toGL (torusHom K t) * G
          = G * Matrix.SpecialLinearGroup.toGL (torusHom K (Units.map (ψ : K →* K) s₀)) * G⁻¹ * G :=
            by rw [← hGd]
        _ = _ := by group
    have h2 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) h1
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h2
  have hσ : (Units.map (ψ : K →* K) s₀) ^ 2 ≠ 1 := by
    intro h
    apply hs₀
    apply Units.map_injective (f := (ψ : K →* K)) ψ.injective
    rw [map_pow, h, map_one]
  have hcoe : ∀ A : SL(2, K), ((α A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      (G : Matrix (Fin 2) (Fin 2) K) *
        ((Matrix.SpecialLinearGroup.map (ψ : K →+* K) A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *
          ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro A
    have h2 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K)) (hG A)
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h2
  rcases monomial_shape hσ G hmat with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · obtain ⟨a, b, hGa, hGi⟩ := exists_diagonal_of_offDiag_zero G h01 h10
    have hα' : ∀ A, α A = diagConj2 a b (fieldAutSL ψ 2 A) := fun A =>
      Subtype.ext (by rw [hcoe A, hGa, hGi]; rfl)
    have hβ0 : ∀ A, (fieldAutSL ψ 3).trans (diagConj3 a b) (blockSL K 3 2 0 (by omega) A) =
        blockSL K 3 2 0 (by omega) (α A) := fun A => by
      show diagConj3 a b (fieldAutSL ψ 3 (blockSL K 3 2 0 _ A)) = _
      rw [fieldAutSL_blockSL, diagConj3_blockSL_zero, hα']
    refine ⟨(fieldAutSL ψ 3).trans (diagConj3 a b), hβ0, map_B23_eq _ fun C => ?_⟩
    show diagConj3 a b (fieldAutSL ψ 3 (blockSL K 3 2 1 _ C)) ∈ B23 K
    rw [fieldAutSL_blockSL, diagConj3_blockSL_one]
    exact ⟨_, rfl⟩
  · obtain ⟨a, b, hab⟩ := exists_diagonal_of_diag_zero G h00 h11
    have hα' : ∀ A, α A = diagConj2 a b (invTransposeSL 2 (fieldAutSL ψ 2 A)) := fun A =>
      Subtype.ext ((hcoe A).trans (hab _))
    have hβ0 : ∀ A, ((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b)
        (blockSL K 3 2 0 (by omega) A) = blockSL K 3 2 0 (by omega) (α A) := fun A => by
      show diagConj3 a b (invTransposeSL 3 (fieldAutSL ψ 3 (blockSL K 3 2 0 _ A))) = _
      rw [fieldAutSL_blockSL, invTransposeSL_blockSL, diagConj3_blockSL_zero, hα']
    refine ⟨((fieldAutSL ψ 3).trans (invTransposeSL 3)).trans (diagConj3 a b), hβ0,
      map_B23_eq _ fun C => ?_⟩
    show diagConj3 a b (invTransposeSL 3 (fieldAutSL ψ 3 (blockSL K 3 2 1 _ C))) ∈ B23 K
    rw [fieldAutSL_blockSL, invTransposeSL_blockSL, diagConj3_blockSL_one]
    exact ⟨_, rfl⟩

end Extend

end CFSG.ClassicalInvolution.WeakCT
