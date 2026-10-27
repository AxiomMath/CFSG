module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.LocalRing.Basic

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

structure InvPlacement (n k : ℕ) where
  u : Fin k → Fin n
  w : Fin k → Fin n
  u_injective : Function.Injective u
  w_injective : Function.Injective w
  u_ne_w : ∀ a b, u a ≠ w b

namespace InvPlacement

variable {n k : ℕ} (P : InvPlacement n k)

@[expose] def level (i : Fin n) : ℕ :=
  if ∃ a, P.u a = i then 0 else if ∃ a, P.w a = i then 2 else 1

theorem level_u (a : Fin k) : P.level (P.u a) = 0 :=
  ite_eq_left ⟨a, rfl⟩

theorem level_w (a : Fin k) : P.level (P.w a) = 2 := by
  rw [level, ite_eq_right (fun ⟨b, hb⟩ => P.u_ne_w b a hb), ite_eq_left ⟨a, rfl⟩]

theorem level_le_two (i : Fin n) : P.level i ≤ 2 := by
  unfold level
  split_ifs <;> omega

theorem level_eq_zero_iff {i : Fin n} : P.level i = 0 ↔ ∃ a, P.u a = i := by
  unfold level
  split_ifs with h1 h2 <;> simp_all

theorem level_eq_two_iff {i : Fin n} : P.level i = 2 ↔ ∃ a, P.w a = i := by
  constructor
  · intro h
    unfold level at h
    split_ifs at h with h1 h2 <;> first | exact h2 | omega
  · rintro ⟨a, rfl⟩
    exact P.level_w a

theorem level_eq_one_iff {i : Fin n} : P.level i = 1 ↔ (∀ a, P.u a ≠ i) ∧ ∀ a, P.w a ≠ i := by
  unfold level
  split_ifs with h1 h2 <;> simp_all

theorem level_ne_zero_iff {i : Fin n} : P.level i ≠ 0 ↔ ∀ a, P.u a ≠ i := by
  rw [Ne, level_eq_zero_iff, not_exists]

theorem level_ne_two_iff {i : Fin n} : P.level i ≠ 2 ↔ ∀ a, P.w a ≠ i := by
  rw [Ne, level_eq_two_iff, not_exists]

@[expose] def free : Finset (Fin n) :=
  Finset.univ.filter fun i => P.level i = 1

theorem mem_free {i : Fin n} : i ∈ P.free ↔ P.level i = 1 := by
  simp [free]

@[expose] def supp : Fin k ⊕ Fin k → Fin n :=
  Sum.elim P.u P.w

theorem supp_injective : Function.Injective P.supp :=
  P.u_injective.sumElim P.w_injective P.u_ne_w

theorem free_eq_compl : P.free = (Finset.univ.image P.supp)ᶜ := by
  ext i
  simp only [mem_free, level_eq_one_iff, Finset.mem_compl, Finset.mem_image, Finset.mem_univ,
    true_and, supp, Sum.exists, Sum.elim_inl, Sum.elim_inr, not_or, not_exists]

theorem card_free : P.free.card = n - 2 * k := by
  rw [free_eq_compl, Finset.card_compl, Finset.card_image_of_injective _ P.supp_injective,
    Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  omega

variable (K : Type*) [Field K]

@[expose] def nil : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if ∃ a, P.u a = i ∧ P.w a = j then 1 else 0

variable {K}

theorem nil_apply_w (i : Fin n) (b : Fin k) :
    P.nil K i (P.w b) = if P.u b = i then 1 else 0 := by
  simp only [nil, of_apply]
  by_cases h : P.u b = i
  · rw [ite_eq_left ⟨b, h, rfl⟩, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨a, ha, hab⟩
    exact h (P.w_injective hab ▸ ha)

theorem nil_apply_u (a : Fin k) (j : Fin n) :
    P.nil K (P.u a) j = if P.w a = j then 1 else 0 := by
  simp only [nil, of_apply]
  by_cases h : P.w a = j
  · rw [ite_eq_left ⟨a, rfl, h⟩, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right]
    rintro ⟨b, hab, hb⟩
    exact h (P.u_injective hab ▸ hb)

theorem nil_apply_of_ne_zero {i j : Fin n} (hi : P.level i ≠ 0) : P.nil K i j = 0 := by
  rw [level_ne_zero_iff] at hi
  exact ite_eq_right fun ⟨a, ha, _⟩ => hi a ha

theorem nil_apply_of_ne_two {i j : Fin n} (hj : P.level j ≠ 2) : P.nil K i j = 0 := by
  rw [level_ne_two_iff] at hj
  exact ite_eq_right fun ⟨a, _, ha⟩ => hj a ha

theorem mul_nil_apply_w (B : Matrix (Fin n) (Fin n) K) (i : Fin n) (b : Fin k) :
    (B * P.nil K) i (P.w b) = B i (P.u b) := by
  simp only [mul_apply, nil_apply_w, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem mul_nil_apply_of_ne_two (B : Matrix (Fin n) (Fin n) K) (i : Fin n) {j : Fin n}
    (hj : P.level j ≠ 2) : (B * P.nil K) i j = 0 := by
  simp only [mul_apply, P.nil_apply_of_ne_two hj, mul_zero, Finset.sum_const_zero]

theorem nil_mul_apply_u (B : Matrix (Fin n) (Fin n) K) (a : Fin k) (j : Fin n) :
    (P.nil K * B) (P.u a) j = B (P.w a) j := by
  simp only [mul_apply, nil_apply_u, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem nil_mul_apply_of_ne_zero (B : Matrix (Fin n) (Fin n) K) {i : Fin n} (j : Fin n)
    (hi : P.level i ≠ 0) : (P.nil K * B) i j = 0 := by
  simp only [mul_apply, P.nil_apply_of_ne_zero hi, zero_mul, Finset.sum_const_zero]

theorem nil_apply_of_le {i j : Fin n} (hij : P.level j ≤ P.level i) : P.nil K i j = 0 := by
  by_cases hi : P.level i = 0
  · exact P.nil_apply_of_ne_two (by omega)
  · exact P.nil_apply_of_ne_zero hi

theorem mul_apply_of_level_eq {B B' : Matrix (Fin n) (Fin n) K}
    (hB : B.BlockTriangular P.level) (hB' : B'.BlockTriangular P.level) {i j : Fin n}
    (hij : P.level i = P.level j) :
    (B * B') i j = ∑ l, if P.level l = P.level i then B i l * B' l j else 0 := by
  rw [mul_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with hl
  · rfl
  · rcases lt_or_gt_of_ne hl with h | h
    · rw [hB h, zero_mul]
    · rw [hB' (hij ▸ h), mul_zero]

theorem submatrix_mul_of_level {B B' : Matrix (Fin n) (Fin n) K}
    (hB : B.BlockTriangular P.level) (hB' : B'.BlockTriangular P.level) {ι : Type*} [Fintype ι]
    (e : ι → Fin n) (he : Function.Injective e) (c : ℕ)
    (hec : ∀ i, P.level i = c ↔ ∃ x, e x = i) :
    (B * B').submatrix e e = B.submatrix e e * B'.submatrix e e := by
  ext x y
  have hx : P.level (e x) = c := (hec _).2 ⟨x, rfl⟩
  have hy : P.level (e y) = c := (hec _).2 ⟨y, rfl⟩
  rw [submatrix_apply, P.mul_apply_of_level_eq hB hB' (hx.trans hy.symm), mul_apply]
  symm
  refine Fintype.sum_of_injective e he _ _ (fun l hl => ?_) (fun z => ?_)
  · rw [ite_eq_right]
    rw [hx]
    exact fun h => hl ((hec l).1 h)
  · rw [submatrix_apply, submatrix_apply, ite_eq_left (((hec _).2 ⟨z, rfl⟩).trans hx.symm)]

theorem level_eq_zero_iff' (i : Fin n) : P.level i = 0 ↔ ∃ a, P.u a = i :=
  P.level_eq_zero_iff

theorem level_eq_two_iff' (i : Fin n) : P.level i = 2 ↔ ∃ a, P.w a = i :=
  P.level_eq_two_iff

theorem level_eq_one_iff_free (i : Fin n) :
    P.level i = 1 ↔ ∃ x : P.free, (x : Fin n) = i :=
  ⟨fun h => ⟨⟨i, P.mem_free.2 h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ P.mem_free.1 x.2⟩

theorem submatrix_mul_u {B B' : Matrix (Fin n) (Fin n) K}
    (hB : B.BlockTriangular P.level) (hB' : B'.BlockTriangular P.level) :
    (B * B').submatrix P.u P.u = B.submatrix P.u P.u * B'.submatrix P.u P.u :=
  P.submatrix_mul_of_level hB hB' P.u P.u_injective 0 P.level_eq_zero_iff'

theorem submatrix_mul_w {B B' : Matrix (Fin n) (Fin n) K}
    (hB : B.BlockTriangular P.level) (hB' : B'.BlockTriangular P.level) :
    (B * B').submatrix P.w P.w = B.submatrix P.w P.w * B'.submatrix P.w P.w :=
  P.submatrix_mul_of_level hB hB' P.w P.w_injective 2 P.level_eq_two_iff'

theorem submatrix_mul_free {B B' : Matrix (Fin n) (Fin n) K}
    (hB : B.BlockTriangular P.level) (hB' : B'.BlockTriangular P.level) :
    (B * B').submatrix (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) =
      B.submatrix (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) *
        B'.submatrix (Subtype.val : P.free → Fin n) (Subtype.val : P.free → Fin n) :=
  P.submatrix_mul_of_level hB hB' Subtype.val Subtype.val_injective 1 P.level_eq_one_iff_free

theorem det_one_add_of_strict {Y : Matrix (Fin n) (Fin n) K}
    (hY : ∀ i j, P.level j ≤ P.level i → Y i j = 0) : (1 + Y).det = 1 := by
  classical
  have hT : (1 + Y).BlockTriangular P.level := by
    intro i j hij
    rw [Matrix.add_apply, hY i j hij.le, add_zero, one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hij
  rw [hT.det]
  refine Finset.prod_eq_one fun c _ => ?_
  have : (1 + Y).toSquareBlock P.level c = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    rw [toSquareBlock_def, of_apply, Matrix.add_apply, hY i j (by rw [hi, hj]), add_zero]
    by_cases hij : i = j
    · subst hij
      rw [one_apply_eq, one_apply_eq]
    · rw [one_apply_ne hij, one_apply_ne fun h => hij (congrArg Subtype.val h)]
  rw [this, det_one]

theorem det_one_add_nil : (1 + P.nil K).det = 1 :=
  P.det_one_add_of_strict fun _ _ h => P.nil_apply_of_le h

variable (K)

@[expose] def mat : SpecialLinearGroup (Fin n) K :=
  ⟨1 + P.nil K, P.det_one_add_nil⟩

variable {K}

theorem coe_mat : (P.mat K : Matrix (Fin n) (Fin n) K) = 1 + P.nil K :=
  rfl

theorem nil_mul_nil : P.nil K * P.nil K = 0 := by
  ext i j
  by_cases hi : P.level i = 0
  · obtain ⟨a, rfl⟩ := P.level_eq_zero_iff.1 hi
    rw [nil_mul_apply_u, P.nil_apply_of_ne_zero (by rw [level_w]; omega), Matrix.zero_apply]
  · rw [P.nil_mul_apply_of_ne_zero _ j hi, Matrix.zero_apply]

theorem mat_mul_self [CharP K 2] : P.mat K * P.mat K = 1 := by
  ext i j
  rw [SpecialLinearGroup.coe_mul, coe_mat, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, nil_mul_nil, add_zero,
    SpecialLinearGroup.coe_one, add_assoc, Matrix.add_apply, Matrix.add_apply,
    CharTwo.add_self_eq_zero, add_zero]

theorem mem_centralizer_mat_iff {B : SpecialLinearGroup (Fin n) K} :
    B ∈ Subgroup.centralizer {P.mat K} ↔
      (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level ∧
        ∀ a b, (B : Matrix (Fin n) (Fin n) K) (P.w a) (P.w b) =
          (B : Matrix (Fin n) (Fin n) K) (P.u a) (P.u b) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : ((B * P.mat K : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) + (B : Matrix (Fin n) (Fin n) K) * P.nil K := by
    rw [SpecialLinearGroup.coe_mul, coe_mat, Matrix.mul_add, Matrix.mul_one]
  have h2 : ((P.mat K * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) + P.nil K * (B : Matrix (Fin n) (Fin n) K) := by
    rw [SpecialLinearGroup.coe_mul, coe_mat, Matrix.add_mul, Matrix.one_mul]
  have key : B * P.mat K = P.mat K * B ↔
      (B : Matrix (Fin n) (Fin n) K) * P.nil K = P.nil K * (B : Matrix (Fin n) (Fin n) K) := by
    constructor
    · intro h
      have := congrArg (fun X : SpecialLinearGroup (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) h
      rw [h1, h2] at this
      exact add_left_cancel this
    · intro h
      apply Subtype.ext
      rw [h1, h2, h]
  rw [key]
  constructor
  · intro h
    refine ⟨fun i j hij => ?_, fun a b => ?_⟩
    · have hj2 : P.level j < 2 := lt_of_lt_of_le hij (P.level_le_two i)
      rcases (by omega : P.level j = 0 ∨ P.level j = 1) with hj0 | hj1
      · obtain ⟨b, rfl⟩ := P.level_eq_zero_iff.1 hj0
        have := congrFun (congrFun h i) (P.w b)
        rwa [mul_nil_apply_w, P.nil_mul_apply_of_ne_zero _ _ (by omega)] at this
      · have hi2 : P.level i = 2 := by have := P.level_le_two i; omega
        obtain ⟨a, rfl⟩ := P.level_eq_two_iff.1 hi2
        have := congrFun (congrFun h (P.u a)) j
        rw [P.mul_nil_apply_of_ne_two _ _ (by omega), nil_mul_apply_u] at this
        exact this.symm
    · have := congrFun (congrFun h (P.u a)) (P.w b)
      rw [mul_nil_apply_w, nil_mul_apply_u] at this
      exact this.symm
  · rintro ⟨hB, hB'⟩
    ext i j
    by_cases hi : P.level i = 0 <;> by_cases hj : P.level j = 2
    · obtain ⟨a, rfl⟩ := P.level_eq_zero_iff.1 hi
      obtain ⟨b, rfl⟩ := P.level_eq_two_iff.1 hj
      rw [mul_nil_apply_w, nil_mul_apply_u, hB']
    · obtain ⟨a, rfl⟩ := P.level_eq_zero_iff.1 hi
      rw [P.mul_nil_apply_of_ne_two _ _ hj, nil_mul_apply_u, hB]
      rw [level_w]
      have := P.level_le_two j
      omega
    · obtain ⟨b, rfl⟩ := P.level_eq_two_iff.1 hj
      rw [mul_nil_apply_w, P.nil_mul_apply_of_ne_zero _ _ hi, hB]
      rw [level_u]
      omega
    · rw [P.mul_nil_apply_of_ne_two _ _ hj, P.nil_mul_apply_of_ne_zero _ _ hi]

theorem coe_inv_eq_inv (B : SpecialLinearGroup (Fin n) K) :
    ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K)⁻¹ := by
  rw [SpecialLinearGroup.coe_inv, Matrix.inv_def, SpecialLinearGroup.det_coe, Ring.inverse_one,
    one_smul]

theorem blockTriangular_coe_inv {α : Type*} [LinearOrder α] {b : Fin n → α}
    {B : SpecialLinearGroup (Fin n) K} (hB : (B : Matrix (Fin n) (Fin n) K).BlockTriangular b) :
    ((B⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular b := by
  have : Invertible (B : Matrix (Fin n) (Fin n) K).det :=
    invertibleOfNonzero (by rw [SpecialLinearGroup.det_coe]; exact one_ne_zero)
  have : Invertible (B : Matrix (Fin n) (Fin n) K) := Matrix.invertibleOfDetInvertible _
  rw [coe_inv_eq_inv]
  exact blockTriangular_inv_of_blockTriangular hB

variable (K) in
@[expose] def parabolic : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {B | (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level}
  one_mem' := by
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular P.level
    rw [SpecialLinearGroup.coe_one]
    exact blockTriangular_one
  mul_mem' {A B} hA hB := by
    show ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K).BlockTriangular P.level
    rw [SpecialLinearGroup.coe_mul]
    exact BlockTriangular.mul hA hB
  inv_mem' {B} hB := blockTriangular_coe_inv hB

theorem mem_parabolic {B : SpecialLinearGroup (Fin n) K} :
    B ∈ P.parabolic K ↔ (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
  Iff.rfl

theorem centralizer_le_parabolic : Subgroup.centralizer {P.mat K} ≤ P.parabolic K :=
  fun _ hB => (P.mem_centralizer_mat_iff.1 hB).1

theorem blockTriangular_of_unitri {B : Matrix (Fin n) (Fin n) K}
    (hB : ∀ i j, P.level j ≤ P.level i → B i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    B.BlockTriangular P.level := by
  intro i j hij
  rw [hB i j hij.le, one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem mul_unitri_apply {M B : Matrix (Fin n) (Fin n) K} (hM : M.BlockTriangular P.level)
    (hB : ∀ i j, P.level j ≤ P.level i → B i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    {i j : Fin n} (hij : P.level i = P.level j) : (M * B) i j = M i j := by
  rw [P.mul_apply_of_level_eq hM (P.blockTriangular_of_unitri hB) hij,
    Finset.sum_eq_single j]
  · rw [ite_eq_left hij.symm, hB j j le_rfl, one_apply_eq, mul_one]
  · intro l _ hlj
    split_ifs with hl
    · rw [hB l j (by omega), one_apply_ne hlj, mul_zero]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem unitri_mul_apply {M B : Matrix (Fin n) (Fin n) K} (hM : M.BlockTriangular P.level)
    (hB : ∀ i j, P.level j ≤ P.level i → B i j = (1 : Matrix (Fin n) (Fin n) K) i j)
    {i j : Fin n} (hij : P.level i = P.level j) : (B * M) i j = M i j := by
  rw [P.mul_apply_of_level_eq (P.blockTriangular_of_unitri hB) hM hij,
    Finset.sum_eq_single i]
  · rw [ite_eq_left rfl, hB i i le_rfl, one_apply_eq, one_mul]
  · intro l _ hli
    split_ifs with hl
    · rw [hB i l (by omega), one_apply_ne (Ne.symm hli), zero_mul]
    · rfl
  · intro h
    exact absurd (Finset.mem_univ i) h

variable (K) in
@[expose] def radical : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {B | ∀ i j, P.level j ≤ P.level i →
    (B : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j}
  one_mem' := fun _ _ _ => rfl
  mul_mem' {A B} hA hB := by
    intro i j hij
    show ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = _
    rw [SpecialLinearGroup.coe_mul, mul_apply, Finset.sum_eq_single i]
    · rw [hA i i le_rfl, hB i j hij, one_apply_eq, one_mul]
    · intro l _ hli
      by_cases hl : P.level l ≤ P.level i
      · rw [hA i l hl, one_apply_ne (Ne.symm hli), zero_mul]
      · rw [hB l j (by omega), one_apply_ne, mul_zero]
        rintro rfl
        omega
    · intro h
      exact absurd (Finset.mem_univ i) h
  inv_mem' {B} hB := by
    have hBp : (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
      P.blockTriangular_of_unitri hB
    have hinv := blockTriangular_coe_inv hBp
    intro i j hij
    rcases lt_or_eq_of_le hij with h | h
    · rw [hinv h, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · rw [← P.mul_unitri_apply hinv hB h.symm, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
        SpecialLinearGroup.coe_one]

theorem mem_radical {B : SpecialLinearGroup (Fin n) K} :
    B ∈ P.radical K ↔ ∀ i j, P.level j ≤ P.level i →
      (B : Matrix (Fin n) (Fin n) K) i j = (1 : Matrix (Fin n) (Fin n) K) i j :=
  Iff.rfl

theorem radical_le_parabolic : P.radical K ≤ P.parabolic K :=
  fun _ hB => P.blockTriangular_of_unitri hB

theorem radical_le_centralizer : P.radical K ≤ Subgroup.centralizer {P.mat K} := by
  intro B hB
  rw [mem_centralizer_mat_iff]
  refine ⟨P.blockTriangular_of_unitri hB, fun a b => ?_⟩
  rw [hB _ _ (by rw [level_w, level_w]), hB _ _ (by rw [level_u, level_u])]
  simp only [one_apply, P.w_injective.eq_iff, P.u_injective.eq_iff]

theorem conj_mem_radical {p r : SpecialLinearGroup (Fin n) K} (hp : p ∈ P.parabolic K)
    (hr : r ∈ P.radical K) : p * r * p⁻¹ ∈ P.radical K := by
  have hpi : p⁻¹ ∈ P.parabolic K := inv_mem hp
  have hpr : p * r ∈ P.parabolic K := mul_mem hp (P.radical_le_parabolic hr)
  have hT : p * r * p⁻¹ ∈ P.parabolic K := mul_mem hpr hpi
  intro i j hij
  rcases lt_or_eq_of_le hij with h | h
  · rw [hT h, one_apply_ne]
    rintro rfl
    exact lt_irrefl _ h
  · have hpr' : ∀ l, P.level l = P.level i →
        ((p * r : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i l =
          (p : Matrix (Fin n) (Fin n) K) i l := fun l hl => by
      rw [SpecialLinearGroup.coe_mul]
      exact P.mul_unitri_apply hp hr hl.symm
    calc ((p * r * p⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j
        = ∑ l, if P.level l = P.level i then
            ((p * r : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i l *
              ((p⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) l j else 0 := by
          rw [SpecialLinearGroup.coe_mul _ (p⁻¹)]
          exact P.mul_apply_of_level_eq hpr hpi h.symm
      _ = ∑ l, if P.level l = P.level i then (p : Matrix (Fin n) (Fin n) K) i l *
            ((p⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) l j else 0 := by
          refine Finset.sum_congr rfl fun l _ => ?_
          split_ifs with hl
          · rw [hpr' l hl]
          · rfl
      _ = ((p * p⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j := by
          rw [SpecialLinearGroup.coe_mul]
          exact (P.mul_apply_of_level_eq hp hpi h.symm).symm
      _ = (1 : Matrix (Fin n) (Fin n) K) i j := by
          rw [mul_inv_cancel, SpecialLinearGroup.coe_one]

theorem parabolic_le_normalizer_radical :
    P.parabolic K ≤ Subgroup.normalizer (P.radical K : Set (SpecialLinearGroup (Fin n) K)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => P.conj_mem_radical hp hr, fun hr => ?_⟩
  have := P.conj_mem_radical (inv_mem hp) hr
  simpa [mul_assoc] using this

variable (K) in
@[expose] def blockDiag : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {B | ∀ i j, P.level i ≠ P.level j → (B : Matrix (Fin n) (Fin n) K) i j = 0}
  one_mem' := by
    intro i j h
    show ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0
    rw [SpecialLinearGroup.coe_one, one_apply_ne]
    rintro rfl
    exact h rfl
  mul_mem' {A B} hA hB := by
    intro i j hij
    show ((A * B : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0
    rw [SpecialLinearGroup.coe_mul, mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : P.level i = P.level l
    · rw [hB l j (hl ▸ hij), mul_zero]
    · rw [hA i l hl, zero_mul]
  inv_mem' {B} hB := by
    have h1 : (B : Matrix (Fin n) (Fin n) K).BlockTriangular P.level :=
      fun i j h => hB i j (ne_of_gt h)
    have h2 : (B : Matrix (Fin n) (Fin n) K).BlockTriangular
        (fun i => OrderDual.toDual (P.level i)) :=
      fun i j h => hB i j (ne_of_lt (OrderDual.toDual_lt_toDual.1 h))
    have h1' := blockTriangular_coe_inv h1
    have h2' := blockTriangular_coe_inv h2
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2' (OrderDual.toDual_lt_toDual.2 h)
    · exact h1' h

theorem mem_blockDiag {B : SpecialLinearGroup (Fin n) K} :
    B ∈ P.blockDiag K ↔
      ∀ i j, P.level i ≠ P.level j → (B : Matrix (Fin n) (Fin n) K) i j = 0 :=
  Iff.rfl

theorem blockDiag_le_parabolic : P.blockDiag K ≤ P.parabolic K :=
  fun _ hB _ _ h => hB _ _ (ne_of_gt h)

theorem eq_one_of_mem_radical_of_mem_blockDiag {B : SpecialLinearGroup (Fin n) K}
    (hR : B ∈ P.radical K) (hD : B ∈ P.blockDiag K) : B = 1 := by
  ext i j
  rw [SpecialLinearGroup.coe_one]
  by_cases h : P.level j ≤ P.level i
  · exact hR i j h
  · rw [hD i j (by omega), one_apply_ne]
    rintro rfl
    exact h le_rfl

variable (K) in
@[expose] def regionPart (α β : ℕ) (X : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if P.level i = α ∧ P.level j = β then X i j else 0

theorem regionPart_apply (α β : ℕ) (X : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    P.regionPart K α β X i j = if P.level i = α ∧ P.level j = β then X i j else 0 :=
  rfl

theorem regionPart_add (α β : ℕ) (X Y : Matrix (Fin n) (Fin n) K) :
    P.regionPart K α β (X + Y) = P.regionPart K α β X + P.regionPart K α β Y := by
  ext i j
  simp only [regionPart_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem regionPart_sub (α β : ℕ) (X Y : Matrix (Fin n) (Fin n) K) :
    P.regionPart K α β (X - Y) = P.regionPart K α β X - P.regionPart K α β Y := by
  ext i j
  simp only [regionPart_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem regionPart_mul_regionPart_of_ne {α β γ δ : ℕ} (h : β ≠ γ) (X Y : Matrix (Fin n) (Fin n) K) :
    P.regionPart K α β X * P.regionPart K γ δ Y = 0 := by
  ext i j
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  simp only [regionPart_apply]
  split_ifs with h1 h2
  · exact absurd (h1.2.symm.trans h2.1) h
  · rw [mul_zero]
  · rw [zero_mul]
  · rw [zero_mul]

theorem regionPart_mul_regionPart (α β γ : ℕ) (X Y : Matrix (Fin n) (Fin n) K) :
    P.regionPart K α γ (P.regionPart K α β X * P.regionPart K β γ Y) =
      P.regionPart K α β X * P.regionPart K β γ Y := by
  ext i j
  rw [regionPart_apply]
  split_ifs with h
  · rfl
  · rw [mul_apply]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    simp only [regionPart_apply]
    split_ifs with h1 h2
    · exact absurd ⟨h1.1, h2.2⟩ h
    · rw [mul_zero]
    · rw [zero_mul]
    · rw [zero_mul]

theorem regionPart_one {α β : ℕ} (h : α ≠ β) : P.regionPart K α β 1 = 0 := by
  ext i j
  rw [regionPart_apply, Matrix.zero_apply]
  split_ifs with hij
  · rw [one_apply_ne]
    rintro rfl
    exact h (hij.1.symm.trans hij.2)
  · rfl

theorem coe_eq_of_mem_radical {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.radical K) :
    (B : Matrix (Fin n) (Fin n) K) = 1 + (P.regionPart K 0 1 (B - 1) +
      P.regionPart K 1 2 (B - 1) + P.regionPart K 0 2 (B - 1)) := by
  ext i j
  simp only [Matrix.add_apply, regionPart_apply, Matrix.sub_apply]
  have hi := P.level_le_two i
  have hj := P.level_le_two j
  by_cases hij : P.level j ≤ P.level i
  · rw [hB i j hij]
    split_ifs <;> first | omega | simp
  · split_ifs <;> first | omega | abel

variable (K) in
@[expose] def regionHom (α β : ℕ) (hαβ : α < β) :
    Multiplicative (Matrix (Fin n) (Fin n) K) →* SpecialLinearGroup (Fin n) K where
  toFun X := ⟨1 + P.regionPart K α β (Multiplicative.toAdd X), P.det_one_add_of_strict
    fun i j hij => by
      rw [regionPart_apply, ite_eq_right]
      rintro ⟨hi, hj⟩
      omega⟩
  map_one' := by
    apply Subtype.ext
    show 1 + P.regionPart K α β 0 = 1
    rw [show P.regionPart K α β (0 : Matrix (Fin n) (Fin n) K) = 0 by
      ext i j; simp [regionPart_apply], add_zero]
  map_mul' X Y := by
    apply Subtype.ext
    show 1 + P.regionPart K α β (Multiplicative.toAdd X + Multiplicative.toAdd Y) =
      (1 + P.regionPart K α β (Multiplicative.toAdd X)) *
        (1 + P.regionPart K α β (Multiplicative.toAdd Y))
    rw [regionPart_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, P.regionPart_mul_regionPart_of_ne hαβ.ne', add_zero]
    abel

theorem coe_regionHom (α β : ℕ) (hαβ : α < β) (X : Matrix (Fin n) (Fin n) K) :
    ((P.regionHom K α β hαβ (Multiplicative.ofAdd X) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 + P.regionPart K α β X :=
  rfl

theorem regionHom_mem_radical (α β : ℕ) (hαβ : α < β)
    (X : Multiplicative (Matrix (Fin n) (Fin n) K)) :
    P.regionHom K α β hαβ X ∈ P.radical K := by
  intro i j hij
  show (1 + P.regionPart K α β (Multiplicative.toAdd X)) i j = _
  rw [Matrix.add_apply, regionPart_apply, ite_eq_right, add_zero]
  rintro ⟨hi, hj⟩
  omega

@[expose] def radicalRootSet : Set (SpecialLinearGroup (Fin n) K) :=
  {g | ∃ (i j : Fin n) (hij : i ≠ j) (c : K), P.level i < P.level j ∧
    g = SpecialLinearGroup.transvection hij c}

theorem transvection_mem_radical {i j : Fin n} (hij : i ≠ j) (h : P.level i < P.level j) (c : K) :
    SpecialLinearGroup.transvection hij c ∈ P.radical K := by
  intro p q hpq
  rw [SpecialLinearGroup.transvection_coe, Matrix.add_apply, single_apply, ite_eq_right, add_zero]
  rintro ⟨rfl, rfl⟩
  omega

theorem radicalRootSet_subset_radical : P.radicalRootSet (K := K) ⊆ P.radical K := by
  rintro _ ⟨i, j, hij, c, h, rfl⟩
  exact P.transvection_mem_radical hij h c

theorem regionHom_single_mem_closure (α β : ℕ) (hαβ : α < β) (i j : Fin n) (c : K) :
    P.regionHom K α β hαβ (Multiplicative.ofAdd (single i j c)) ∈
      Subgroup.closure (P.radicalRootSet (K := K)) := by
  by_cases h : P.level i = α ∧ P.level j = β
  · have hij : i ≠ j := by
      rintro rfl
      omega
    have : P.regionHom K α β hαβ (Multiplicative.ofAdd (single i j c)) =
        SpecialLinearGroup.transvection hij c := by
      apply Subtype.ext
      rw [coe_regionHom, SpecialLinearGroup.transvection_coe]
      congr 1
      ext p q
      simp only [regionPart_apply, single_apply]
      by_cases hpq : i = p ∧ j = q
      · obtain ⟨rfl, rfl⟩ := hpq
        simp [h]
      · simp [hpq]
    rw [this]
    exact Subgroup.subset_closure ⟨i, j, hij, c, by omega, rfl⟩
  · have : P.regionHom K α β hαβ (Multiplicative.ofAdd (single i j c)) = 1 := by
      apply Subtype.ext
      rw [coe_regionHom, SpecialLinearGroup.coe_one]
      conv_rhs => rw [← add_zero (1 : Matrix (Fin n) (Fin n) K)]
      congr 1
      ext p q
      simp only [regionPart_apply, single_apply, Matrix.zero_apply]
      by_cases hpq : i = p ∧ j = q
      · obtain ⟨rfl, rfl⟩ := hpq
        simp [h]
      · simp [hpq]
    rw [this]
    exact one_mem _

theorem regionHom_mem_closure (α β : ℕ) (hαβ : α < β)
    (X : Multiplicative (Matrix (Fin n) (Fin n) K)) :
    P.regionHom K α β hαβ X ∈ Subgroup.closure (P.radicalRootSet (K := K)) := by
  classical
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) K),
      (∀ x ∈ s, P.regionHom K α β hαβ (Multiplicative.ofAdd (f x)) ∈
        Subgroup.closure (P.radicalRootSet (K := K))) →
      P.regionHom K α β hαβ (Multiplicative.ofAdd (∑ x ∈ s, f x)) ∈
        Subgroup.closure (P.radicalRootSet (K := K)) := by
    intro ι s f hf
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, ofAdd_zero, map_one]; exact one_mem _
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, ofAdd_add, map_mul]
      exact mul_mem (hf a (Finset.mem_insert_self a s))
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
  obtain ⟨X, rfl⟩ : ∃ Y, Multiplicative.ofAdd Y = X := ⟨Multiplicative.toAdd X, rfl⟩
  rw [matrix_eq_sum_single X]
  exact hsum _ _ fun i _ => hsum _ _ fun j _ => P.regionHom_single_mem_closure α β hαβ i j _

theorem radical_eq_regionHom_mul {B : SpecialLinearGroup (Fin n) K} (hB : B ∈ P.radical K) :
    B = P.regionHom K 0 2 (by norm_num) (Multiplicative.ofAdd
        ((B : Matrix (Fin n) (Fin n) K) - 1 -
          P.regionPart K 0 1 ((B : Matrix (Fin n) (Fin n) K) - 1) *
            P.regionPart K 1 2 ((B : Matrix (Fin n) (Fin n) K) - 1))) *
      P.regionHom K 0 1 (by norm_num)
        (Multiplicative.ofAdd ((B : Matrix (Fin n) (Fin n) K) - 1)) *
      P.regionHom K 1 2 (by norm_num)
        (Multiplicative.ofAdd ((B : Matrix (Fin n) (Fin n) K) - 1)) := by
  apply Subtype.ext
  set X := (B : Matrix (Fin n) (Fin n) K) - 1 with hX
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_regionHom, coe_regionHom,
    coe_regionHom, regionPart_sub, regionPart_mul_regionPart, P.coe_eq_of_mem_radical hB, ← hX]
  set A := P.regionPart K 0 2 X
  set Xb := P.regionPart K 0 1 X
  set Xe := P.regionPart K 1 2 X
  have h1 : (A - Xb * Xe) * Xb = 0 := by
    rw [Matrix.sub_mul, P.regionPart_mul_regionPart_of_ne (by norm_num), Matrix.mul_assoc,
      P.regionPart_mul_regionPart_of_ne (by norm_num), Matrix.mul_zero, sub_zero]
  have h2 : (A - Xb * Xe) * Xe = 0 := by
    rw [Matrix.sub_mul, P.regionPart_mul_regionPart_of_ne (by norm_num), Matrix.mul_assoc,
      P.regionPart_mul_regionPart_of_ne (by norm_num), Matrix.mul_zero, sub_zero]
  set Z := A - Xb * Xe with hZ
  have e1 : (1 + Z) * (1 + Xb) = 1 + Z + Xb := by
    rw [show (1 + Z) * (1 + Xb) = 1 + Z + Xb + Z * Xb by noncomm_ring, h1, add_zero]
  have e2 : (1 + Z + Xb) * (1 + Xe) = 1 + Z + Xb + Xe + Xb * Xe := by
    rw [show (1 + Z + Xb) * (1 + Xe) = 1 + Z + Xb + Xe + Z * Xe + Xb * Xe by noncomm_ring, h2,
      add_zero]
  rw [e1, e2, hZ]
  abel

theorem radical_le_closure : P.radical K ≤ Subgroup.closure (P.radicalRootSet (K := K)) := by
  intro B hB
  rw [P.radical_eq_regionHom_mul hB]
  exact mul_mem (mul_mem (P.regionHom_mem_closure _ _ _ _) (P.regionHom_mem_closure _ _ _ _))
    (P.regionHom_mem_closure _ _ _ _)

end InvPlacement

end CFSG.SeitzReduction.LinearPilot
