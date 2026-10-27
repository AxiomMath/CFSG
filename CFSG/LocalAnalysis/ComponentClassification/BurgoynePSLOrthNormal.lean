module

public import CFSG.RankThree.Classical.OddQuadraticFrame
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSlice
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

@[expose] def basisGL (v : Module.Basis (Fin n) K (Fin n → K)) : GL (Fin n) K :=
  ⟨(Pi.basisFun K (Fin n)).toMatrix v, v.toMatrix (Pi.basisFun K (Fin n)),
    (Pi.basisFun K (Fin n)).toMatrix_mul_toMatrix_flip v,
    v.toMatrix_mul_toMatrix_flip (Pi.basisFun K (Fin n))⟩

theorem basisGL_gram (R : Matrix (Fin n) (Fin n) K) (v : Module.Basis (Fin n) K (Fin n → K))
    (i j : Fin n) :
    ((basisGL v : Matrix (Fin n) (Fin n) K)ᵀ * R * (basisGL v : Matrix (Fin n) (Fin n) K)) i j =
      v i ⬝ᵥ R *ᵥ v j := by
  change (((Pi.basisFun K (Fin n)).toMatrix v)ᵀ * R * (Pi.basisFun K (Fin n)).toMatrix v) i j = _
  simp only [Matrix.mul_apply, transpose_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr,
    dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem exists_frame [Finite K] (hK : ringChar K ≠ 2) (hn : 2 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) {a : K} (ha : a ≠ 0) :
    ∃ (P : GL (Fin n) K) (w : Fin n → K), (∀ i, w i ≠ 0) ∧
      (∀ i : Fin n, (i : ℕ) + 1 < n → w i = a) ∧
      (P : Matrix (Fin n) (Fin n) K)ᵀ * R * P = diagonal w := by
  have hodd := CatalogueBLinearHigherB.odd_card_of_ringChar_ne_two K hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQ
  obtain ⟨v, hv, hva, hvl⟩ := CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hodd
    (Module.finrank_fin_fun K) hn Q
    (CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hK R hR) ha
  have hQv : ∀ x, Q x = x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ x := fun x =>
    CatalogueBLinearHigherB.matrixForm_apply R x x
  have hsym : ∀ x y : Fin n → K, y ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ x =
      x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ y := by
    intro x y
    rw [← CatalogueBLinearHigherB.matrixForm_apply, ← CatalogueBLinearHigherB.matrixForm_apply,
      CatalogueBLinearHigherB.matrixForm_symm R hR]
  have hpol : ∀ x y, QuadraticMap.polar Q x y =
      2 * (x ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ y) := by
    intro x y
    rw [hQ, LinearMap.BilinMap.polar_toQuadraticMap, CatalogueBLinearHigherB.matrixForm_apply,
      CatalogueBLinearHigherB.matrixForm_apply, hsym]
    ring
  refine ⟨basisGL v, fun i => v i ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ v i, fun i => ?_,
    fun i hi => ?_, ?_⟩
  · change v i ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ v i ≠ 0
    rw [← hQv]
    by_cases hil : (i : ℕ) + 1 < n
    · rw [hva i hil]
      exact ha
    · have : i = ⟨n - 1, by omega⟩ := Fin.ext (show (i : ℕ) = n - 1 by omega)
      rw [this]
      exact hvl
  · show v i ⬝ᵥ (R : Matrix (Fin n) (Fin n) K) *ᵥ v i = a
    rw [← hQv, hva i hi]
  · ext i j
    rw [basisGL_gram, diagonal_apply]
    split_ifs with hij
    · rw [hij]
    · have := hv i j hij
      rw [hpol] at this
      exact (mul_eq_zero.1 this).resolve_left h2

@[expose] def OrthNF (w : Fin n → K) : Prop :=
  (∀ i, w i ≠ 0) ∧ ∃ I : Finset (Fin n), 3 ≤ I.card ∧ (∀ x y, x ∉ I → y ∉ I → x = y) ∧
    ∀ i ∈ I, ∀ j ∈ I, w i = w j

theorem exists_orth_normal_form [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = R) :
    ∃ (P : GL (Fin n) K) (w : Fin n → K), OrthNF w ∧
      (P : Matrix (Fin n) (Fin n) K)ᵀ * R * P = diagonal w := by
  by_cases h3 : n = 3
  · subst h3
    obtain ⟨P₁, w₁, hw₁, hw₁a, hP₁⟩ := exists_frame hK (by omega) R hR one_ne_zero
    set c₁ := w₁ 2 with hc₁
    have hc₁0 : c₁ ≠ 0 := hw₁ 2
    obtain ⟨P₂, w₂, hw₂, hw₂a, hP₂⟩ := exists_frame hK (by omega) R hR hc₁0
    set c₂ := w₂ 2 with hc₂
    have hdet : ∀ (P : GL (Fin 3) K) (w : Fin 3 → K),
        (P : Matrix (Fin 3) (Fin 3) K)ᵀ * R * P = diagonal w →
        (P : Matrix (Fin 3) (Fin 3) K).det ^ 2 * (R : Matrix (Fin 3) (Fin 3) K).det =
          w 0 * w 1 * w 2 := by
      intro P w hP
      have := congrArg Matrix.det hP
      rw [det_mul, det_mul, det_transpose, det_diagonal, Fin.prod_univ_three] at this
      rw [← this]
      ring
    have e₁ := hdet P₁ w₁ hP₁
    have e₂ := hdet P₂ w₂ hP₂
    rw [hw₁a 0 (by simp), hw₁a 1 (by simp), ← hc₁] at e₁
    rw [hw₂a 0 (by simp), hw₂a 1 (by simp), ← hc₂] at e₂
    have hd₁ : (P₁ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnits_det_units P₁).ne_zero
    have hd₂ : (P₂ : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnits_det_units P₂).ne_zero
    have hdR : (R : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := (Matrix.isUnits_det_units R).ne_zero
    set s := c₁ * (P₁ : Matrix (Fin 3) (Fin 3) K).det / (P₂ : Matrix (Fin 3) (Fin 3) K).det
      with hs
    have hs0 : s ≠ 0 := div_ne_zero (mul_ne_zero hc₁0 hd₁) hd₂
    have hsq : c₂ * s ^ 2 = c₁ := by
      have hc₂e : c₂ = (P₂ : Matrix (Fin 3) (Fin 3) K).det ^ 2 *
          (R : Matrix (Fin 3) (Fin 3) K).det / (c₁ * c₁) := by
        rw [e₂]
        field_simp
      calc c₂ * s ^ 2 = ((P₂ : Matrix (Fin 3) (Fin 3) K).det ^ 2 *
            (R : Matrix (Fin 3) (Fin 3) K).det / (c₁ * c₁)) *
            (c₁ * (P₁ : Matrix (Fin 3) (Fin 3) K).det /
              (P₂ : Matrix (Fin 3) (Fin 3) K).det) ^ 2 := by rw [hc₂e]
        _ = (P₁ : Matrix (Fin 3) (Fin 3) K).det ^ 2 * (R : Matrix (Fin 3) (Fin 3) K).det := by
            field_simp
        _ = c₁ := by rw [e₁]; ring
    set E : GL (Fin 3) K := ⟨diagonal ![1, 1, s], diagonal ![1, 1, s⁻¹], by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      ext k
      fin_cases k <;> simp [hs0], by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      ext k
      fin_cases k <;> simp [hs0]⟩ with hE
    refine ⟨P₂ * E, fun _ => c₁, ⟨fun _ => hc₁0, Finset.univ, by simp, fun x y hx => ?_,
      fun _ _ _ _ => rfl⟩, ?_⟩
    · exact absurd (Finset.mem_univ x) hx
    · rw [Units.val_mul, transpose_mul, show ((E : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal ![1, 1, s] from rfl, diagonal_transpose]
      calc diagonal ![1, 1, s] * (P₂ : Matrix (Fin 3) (Fin 3) K)ᵀ * R *
            ((P₂ : Matrix (Fin 3) (Fin 3) K) * diagonal ![1, 1, s])
          = diagonal ![1, 1, s] * ((P₂ : Matrix (Fin 3) (Fin 3) K)ᵀ * R * P₂) *
            diagonal ![1, 1, s] := by simp only [Matrix.mul_assoc]
        _ = diagonal fun _ => c₁ := by
          rw [hP₂, diagonal_mul_diagonal, diagonal_mul_diagonal]
          congr 1
          ext k
          fin_cases k
          · simp [hw₂a 0 (by simp)]
          · simp [hw₂a 1 (by simp)]
          · simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
            rw [← hsq, hc₂]
            ring
  · obtain ⟨P, w, hw, hwa, hP⟩ := exists_frame hK (by omega) R hR one_ne_zero
    refine ⟨P, w, ⟨hw, Finset.univ.filter fun i : Fin n => (i : ℕ) + 1 < n, ?_, ?_, ?_⟩, hP⟩
    · have heq : (Finset.univ.filter fun i : Fin n => (i : ℕ) + 1 < n) =
          Finset.univ.erase ⟨n - 1, by omega⟩ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
          Fin.ext_iff, and_true]
        omega
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    · intro x y hx hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx hy
      exact Fin.ext (by omega)
    · intro i hi j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      rw [hwa i hi, hwa j hj]

section Rotation

variable {i j : Fin n}

variable (i j) in
@[expose] def planeP : Matrix (Fin n) (Fin n) K := single i i 1 + single j j 1

variable (i j) in
@[expose] def planeN : Matrix (Fin n) (Fin n) K := single i j 1 - single j i 1

theorem single_mul_single_ne (hij : i ≠ j) (a d : Fin n) (c c' : K) :
    single a i c * single j d c' = 0 := by
  rw [single_mul_single_of_ne]; exact hij

theorem planeP_mul_planeP (hij : i ≠ j) : planeP (K := K) i j * planeP i j = planeP i j := by
  simp only [planeP, Matrix.add_mul, Matrix.mul_add, single_mul_single_same,
    single_mul_single_ne hij, single_mul_single_ne hij.symm, mul_one, add_zero, zero_add]

theorem planeP_mul_planeN (hij : i ≠ j) : planeP (K := K) i j * planeN i j = planeN i j := by
  simp only [planeP, planeN, Matrix.add_mul, Matrix.mul_sub, single_mul_single_same,
    single_mul_single_ne hij, single_mul_single_ne hij.symm, mul_one]
  abel

theorem planeN_mul_planeP (hij : i ≠ j) : planeN (K := K) i j * planeP i j = planeN i j := by
  simp only [planeP, planeN, Matrix.sub_mul, Matrix.mul_add, single_mul_single_same,
    single_mul_single_ne hij, single_mul_single_ne hij.symm, mul_one]
  abel

theorem planeN_mul_planeN (hij : i ≠ j) : planeN (K := K) i j * planeN i j = -planeP i j := by
  simp only [planeP, planeN, Matrix.sub_mul, Matrix.mul_sub, single_mul_single_same,
    single_mul_single_ne hij, single_mul_single_ne hij.symm, mul_one, sub_zero, zero_sub]
  abel

variable (i j) in
@[expose] def rotMat (a b : K) : Matrix (Fin n) (Fin n) K :=
  1 + (a - 1) • planeP i j + b • planeN i j

theorem rotMat_mul (hij : i ≠ j) (a b c d : K) :
    rotMat i j a b * rotMat i j c d = rotMat i j (a * c - b * d) (a * d + b * c) := by
  simp only [rotMat, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, planeP_mul_planeP hij, planeP_mul_planeN hij,
    planeN_mul_planeP hij, planeN_mul_planeN hij, smul_neg]
  module

theorem rotMat_one_zero : rotMat (K := K) i j 1 0 = 1 := by simp [rotMat]

theorem rotMat_apply_left (hij : i ≠ j) (a b : K) : rotMat (K := K) i j a b i i = a := by
  simp [rotMat, planeP, planeN, Matrix.add_apply, Ne.symm hij, one_apply]

theorem transpose_planeP : (planeP (K := K) i j)ᵀ = planeP i j := by
  simp only [planeP, transpose_add, transpose_single]

theorem transpose_planeN : (planeN (K := K) i j)ᵀ = -planeN i j := by
  simp only [planeN, transpose_sub, transpose_single, neg_sub]

theorem transpose_rotMat (a b : K) : (rotMat (K := K) i j a b)ᵀ = rotMat i j a (-b) := by
  simp only [rotMat, transpose_add, transpose_one, transpose_smul, transpose_planeP,
    transpose_planeN, smul_neg, neg_smul]

theorem rotMat_neg_one_zero (hij : i ≠ j) : rotMat (K := K) i j (-1) 0 = signMat K {i, j} := by
  ext x y
  simp only [rotMat, planeP, planeN, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    single_apply, one_apply, signMat, diagonal_apply, Finset.mem_insert, Finset.mem_singleton,
    smul_eq_mul, zero_mul, add_zero]
  by_cases hxy : x = y
  · subst hxy
    by_cases hxi : x = i
    · subst hxi
      simp [hij, Ne.symm hij]
    · by_cases hxj : x = j
      · subst hxj
        simp [hxi, Ne.symm hxi]
      · simp [hxi, hxj, Ne.symm hxi, Ne.symm hxj]
  · simp only [hxy, ↓reduceIte]
    by_cases h1 : i = x ∧ i = y
    · exact absurd (h1.1.symm.trans h1.2) hxy
    · by_cases h2 : j = x ∧ j = y
      · exact absurd (h2.1.symm.trans h2.2) hxy
      · simp [h1, h2]

variable (i j) in
@[expose] def rotGL (hij : i ≠ j) {a b : K} (hab : a ^ 2 + b ^ 2 = 1) : GL (Fin n) K :=
  ⟨rotMat i j a b, rotMat i j a (-b),
    by rw [rotMat_mul hij, show a * a - b * -b = 1 by linear_combination hab,
      show a * -b + b * a = 0 by ring, rotMat_one_zero],
    by rw [rotMat_mul hij, show a * a - -b * b = 1 by linear_combination hab,
      show a * b + -b * a = 0 by ring, rotMat_one_zero]⟩

theorem signMat_single (i : Fin n) : signMat K {i} = 1 - (2 : K) • single i i 1 := by
  ext x y
  simp only [signMat, diagonal_apply, Finset.mem_singleton, Matrix.sub_apply, one_apply,
    Matrix.smul_apply, single_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst hxy
    by_cases hxi : x = i
    · subst hxi
      simp only [↓reduceIte, and_self, mul_one]
      ring
    · simp [hxi, Ne.symm hxi]
  · have : ¬ (i = x ∧ i = y) := fun h => hxy (h.1.symm.trans h.2)
    simp [hxy, this]

theorem signMat_mul_rotMat_mul (hij : i ≠ j) (a b : K) :
    signMat K {i} * rotMat i j a b * signMat K {i} = rotMat i j a (-b) := by
  rw [signMat_single]
  simp only [rotMat, planeP, planeN, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    single_mul_single_same, single_mul_single_ne hij, single_mul_single_ne hij.symm, smul_zero,
    mul_one, smul_add, smul_sub, smul_smul]
  module

end Rotation

@[expose] def diagGL {w : Fin n → K} (hw : ∀ i, w i ≠ 0) : GL (Fin n) K :=
  ⟨diagonal w, diagonal fun i => (w i)⁻¹,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact mul_inv_cancel₀ (hw i),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; ext i; exact inv_mul_cancel₀ (hw i)⟩

theorem coe_diagGL {w : Fin n → K} (hw : ∀ i, w i ≠ 0) :
    ((diagGL hw : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal w := rfl

@[expose] def reflGL (i : Fin n) : GL (Fin n) K :=
  ⟨signMat K {i}, signMat K {i}, signMat_mul_self _, signMat_mul_self _⟩

theorem reflGL_mem {w : Fin n → K} (hw : ∀ i, w i ≠ 0) (i : Fin n) :
    reflGL i ∈ CatalogueBGraphForm.isometryGroup n K (diagGL hw) := by
  rw [CatalogueBGraphForm.mem_isometryGroup]
  change (signMat K {i})ᵀ * diagonal w * signMat K {i} = diagonal w
  rw [signMat, diagonal_transpose, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  ext k
  split_ifs <;> ring

theorem rotMat_apply_ne_zero {i j : Fin n} {a b : K} {x y : Fin n} (hxy : x ≠ y)
    (h : rotMat i j a b x y ≠ 0) : (x = i ∧ y = j) ∨ (x = j ∧ y = i) := by
  by_contra hc
  push Not at hc
  apply h
  simp only [rotMat, planeP, planeN, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
    single_apply, one_apply, hxy, ↓reduceIte, smul_eq_mul]
  have e1 : ¬ (i = x ∧ i = y) := fun h' => hxy (h'.1.symm.trans h'.2)
  have e2 : ¬ (j = x ∧ j = y) := fun h' => hxy (h'.1.symm.trans h'.2)
  have e3 : ¬ (i = x ∧ j = y) := fun h' => (hc.1 h'.1.symm) h'.2.symm
  have e4 : ¬ (j = x ∧ i = y) := fun h' => (hc.2 h'.1.symm) h'.2.symm
  simp [e1, e2, e3, e4]

theorem rotGL_mem {w : Fin n → K} (hw : ∀ i, w i ≠ 0) {i j : Fin n} (hij : i ≠ j)
    (hwij : w i = w j) {a b : K} (hab : a ^ 2 + b ^ 2 = 1) :
    rotGL i j hij hab ∈ CatalogueBGraphForm.isometryGroup n K (diagGL hw) := by
  rw [CatalogueBGraphForm.mem_isometryGroup]
  change (rotMat i j a b)ᵀ * diagonal w * rotMat i j a b = diagonal w
  have hcomm : diagonal w * rotMat i j a b = rotMat i j a b * diagonal w := by
    ext x y
    rw [diagonal_mul, mul_diagonal]
    by_cases hxy : x = y
    · rw [hxy]
      ring
    by_cases h0 : rotMat i j a b x y = 0
    · rw [h0, mul_zero, zero_mul]
    rcases rotMat_apply_ne_zero hxy h0 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hwij]
      ring
    · rw [hwij]
      ring
  rw [transpose_rotMat, Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, rotMat_mul hij,
    show a * a - -b * b = 1 by linear_combination hab, show a * b + -b * a = 0 by ring,
    rotMat_one_zero, Matrix.one_mul]

theorem commutatorElement_reflGL_rotGL {i j : Fin n} (hij : i ≠ j) {a b : K}
    (hab : a ^ 2 + b ^ 2 = 1) :
    ((⁅reflGL (K := K) i, rotGL i j hij hab⁆ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      rotMat i j (a ^ 2 - b ^ 2) (-(2 * a * b)) := by
  rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
  change signMat K {i} * rotMat i j a b * signMat K {i} * rotMat i j a (-b) = _
  rw [signMat_mul_rotMat_mul hij, rotMat_mul hij]
  congr 1 <;> ring

end CFSG.ComponentClassification.Burgoyne.PSL
