module

public import CFSG.RankThree.PartOne.SEITZ2.SL2Line
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear

public section

namespace CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.RankThree.PartOne.CTP

section Traces

variable {F : Type} [Field F]

theorem trace_u2_mul_l2_odd (a b : F) :
    Matrix.trace ((u2 a * l2 b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      2 + a * b := by
  rw [coe_u2_mul_l2, Matrix.trace_fin_two]
  simp
  ring

theorem coe_mul_self_eq (A : SpecialLinearGroup (Fin 2) F) :
    ((A * A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) • (A : Matrix (Fin 2) (Fin 2) F) - 1 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first | ring1 | linear_combination (-1 : F) * hdet

theorem trace_pow_add_two (A : SpecialLinearGroup (Fin 2) F) (n : ℕ) :
    Matrix.trace ((A ^ (n + 2) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.trace ((A ^ (n + 1) : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
      Matrix.trace ((A ^ n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have h1 : (A ^ (n + 2) : SpecialLinearGroup (Fin 2) F) = A ^ n * (A * A) := by
    rw [pow_add, pow_two]
  have h2 : (A ^ (n + 1) : SpecialLinearGroup (Fin 2) F) = A ^ n * A := pow_succ A n
  rw [h1, Matrix.SpecialLinearGroup.coe_mul, coe_mul_self_eq, h2,
    Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul]
  simp [smul_eq_mul]

theorem trace_pow_two (A : SpecialLinearGroup (Fin 2) F) :
    Matrix.trace ((A ^ 2 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 - 2 := by
  have := trace_pow_add_two A 0
  simp only [zero_add, pow_one, pow_zero, Matrix.SpecialLinearGroup.coe_one,
    Matrix.trace_one, Fintype.card_fin] at this
  rw [this]
  push_cast
  ring

theorem trace_pow_three (A : SpecialLinearGroup (Fin 2) F) :
    Matrix.trace ((A ^ 3 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 3 -
        3 * Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) := by
  have h := trace_pow_add_two A 1
  rw [pow_one] at h
  rw [show (1 + 2 : ℕ) = 3 by norm_num] at h
  rw [h, trace_pow_two]
  ring

theorem trace_pow_five (A : SpecialLinearGroup (Fin 2) F) :
    Matrix.trace ((A ^ 5 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 5 -
        5 * Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 3 +
        5 * Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) := by
  have h4 := trace_pow_add_two A 2
  have h5 := trace_pow_add_two A 3
  rw [show (3 + 2 : ℕ) = 5 by norm_num, show (3 + 1 : ℕ) = 4 by norm_num] at h5
  rw [show (2 + 2 : ℕ) = 4 by norm_num, show (2 + 1 : ℕ) = 3 by norm_num] at h4
  rw [h5, h4, trace_pow_three, trace_pow_two]
  ring

theorem trace_pow_sq_eq_four {A : SpecialLinearGroup (Fin 2) F} {n : ℕ}
    (h : A ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    Matrix.trace ((A ^ n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ^ 2 = 4 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, hr, hA⟩ := h
  rw [Fintype.card_fin] at hr
  rw [← hA, Matrix.trace_fin_two]
  simp [Matrix.scalar_apply]
  linear_combination 4 * hr

theorem mkPSL_pow_eq_one_iff {A : SpecialLinearGroup (Fin 2) F} {n : ℕ} :
    (mkPSL F A) ^ n = 1 ↔ A ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  rw [← map_pow, mkPSL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem center_sq_eq_one {z : SpecialLinearGroup (Fin 2) F}
    (hz : z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : z * z = 1 := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨r, hr, hA⟩ := hz
  rw [Fintype.card_fin] at hr
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, ← hA]
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply] <;> linear_combination hr

theorem mkPSL_u2_l2_comm_ne {a : F} (ha : a ≠ 0) :
    mkPSL F (u2 1) * mkPSL F (l2 a) ≠ mkPSL F (l2 a) * mkPSL F (u2 1) := by
  intro h
  rw [← map_mul, ← map_mul, mkPSL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, hr, hZ⟩ := h
  generalize hZdef : (u2 1 * l2 a)⁻¹ * (l2 a * u2 (1 : F)) = Z at hZ
  have hB : l2 a * u2 (1 : F) = (u2 1 * l2 a) * Z := by
    rw [← hZdef, mul_inv_cancel_left]
  have hM := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hB
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hM
  rw [← hZ] at hM
  have h01 := congrFun (congrFun hM 0) 1
  have h00 := congrFun (congrFun hM 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, u2_coe, l2_coe, Matrix.scalar_apply] at h01 h00
  subst h01
  exact ha (by linear_combination (-1 : F) * h00)

theorem exists_int_of_pow_central [CharP F 5] {a : F} {g : SpecialLinearGroup (Fin 2) F}
    (hT : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 2 + a)
    (h : g ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      g ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      g ^ 5 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    ∃ n : ℤ, a = (n : F) := by
  have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rcases h with h | h | h
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_two, hT] at h'
    have e : (((2 + a) ^ 2 - 4) * (2 + a) ^ 2) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 e with h1 | h1
    · have h2 : a * (4 + a) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact ⟨0, by simpa using h3⟩
      · exact ⟨-4, by push_cast; linear_combination h3⟩
    · have h3 : 2 + a = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
      exact ⟨-2, by push_cast; linear_combination h3⟩
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_three, hT] at h'
    have e : (a * (3 + a) ^ 2) * ((4 + a) * (1 + a) ^ 2) = 0 := by linear_combination h'
    rcases mul_eq_zero.1 e with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact ⟨0, by simpa using h2⟩
      · have h3 : 3 + a = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
        exact ⟨-3, by push_cast; linear_combination h3⟩
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact ⟨-4, by push_cast; linear_combination h2⟩
      · have h3 : 1 + a = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h2
        exact ⟨-1, by push_cast; linear_combination h3⟩
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_five, hT] at h'
    have e5 : (2 + a) ^ 5 - 5 * (2 + a) ^ 3 + 5 * (2 + a) = (2 + a) ^ 5 := by
      rw [h5]; ring
    rw [e5] at h'
    have e : ((2 + a) ^ 5 - 2) * ((2 + a) ^ 5 + 2) = 0 := by
      linear_combination h'
    have h32 : (2 : F) ^ 5 = 2 := by linear_combination 6 * h5
    rcases mul_eq_zero.1 e with h1 | h1
    · have h2 : (2 + a - 2) ^ 5 = 0 := by
        rw [sub_pow_char, h32]; linear_combination h1
      have h3 : 2 + a - 2 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h2
      exact ⟨0, by simpa using (by linear_combination h3 : a = 0)⟩
    · have h2 : (2 + a + 2) ^ 5 = 0 := by
        rw [add_pow_char, h32]; linear_combination h1
      have h3 : 2 + a + 2 = 0 := pow_eq_zero_iff (by norm_num) |>.1 h2
      exact ⟨-4, by push_cast; linear_combination h3⟩

theorem trace_pow_four (A : SpecialLinearGroup (Fin 2) F) :
    Matrix.trace ((A ^ 4 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 - 2) ^ 2 - 2 := by
  have h := trace_pow_two (A ^ 2)
  rw [← pow_mul, trace_pow_two] at h
  exact h

theorem pow_nine_of_pow_central [CharP F 3] {A : SpecialLinearGroup (Fin 2) F}
    (h : A ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      A ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      A ^ 4 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      A ^ 5 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 9 = Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  set t := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) with ht
  have hsq : t ^ 2 = 1 → t ^ 9 = t := fun e => by
    linear_combination (t * (t ^ 6 + t ^ 4 + t ^ 2 + 1)) * e
  have hz : t ^ 2 = 0 → t ^ 9 = t := fun e => by
    have : t = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 e
    rw [this]; ring
  rcases h with h | h | h | h
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_two] at h'
    have e : t ^ 2 * (t ^ 2 - 1) = 0 := by linear_combination h' + t ^ 2 * h3
    rcases mul_eq_zero.1 e with e | e
    · exact hz e
    · exact hsq (by linear_combination e)
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_three] at h'
    have e : (t ^ 2 - 1) ^ 3 = 0 := by linear_combination h' + (t ^ 2 - 1) ^ 2 * h3
    exact hsq (by linear_combination pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0) |>.1 e)
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_four] at h'
    have e : ((t ^ 2 - 2) ^ 2) * ((t ^ 2 - 2) ^ 2 - 1) = 0 := by
      linear_combination h' + ((t ^ 2 - 2) ^ 2) * h3
    rcases mul_eq_zero.1 e with e | e
    · have e2 : t ^ 2 = 2 := by
        have := pow_eq_zero_iff (two_ne_zero) |>.1 e
        linear_combination this
      linear_combination (t * (t ^ 6 + 2 * t ^ 4 + 4 * t ^ 2 + 8)) * e2 + (t * 5) * h3
    · have e2 : (t ^ 2 - 3) * (t ^ 2 - 1) = 0 := by linear_combination e
      rcases mul_eq_zero.1 e2 with e3 | e3
      · exact hz (by linear_combination e3 + h3)
      · exact hsq (by linear_combination e3)
  · have h' := trace_pow_sq_eq_four h
    rw [trace_pow_five] at h'
    have e : (t ^ 2 - 4) * (t ^ 4 - 3 * t ^ 2 + 1) ^ 2 = 0 := by linear_combination h'
    rcases mul_eq_zero.1 e with e | e
    · exact hsq (by linear_combination e + h3)
    · have e2 : t ^ 4 - 3 * t ^ 2 + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 e
      have e3 : t ^ 4 = -1 := by linear_combination e2 + t ^ 2 * h3
      linear_combination (t * (t ^ 4 - 1)) * e3

theorem pow_nine_of_trace [CharP F 3] {a : F} (h : (2 + a) ^ 9 = 2 + a) : a ^ 9 = a := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h2 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have e := add_pow_char_pow (p := 3) (n := 2) (2 : F) a
  have e9 : (512 : F) = 2 := by linear_combination 170 * h2
  norm_num at e
  rw [e, e9] at h
  linear_combination h

end Traces

section Fields

open Polynomial in
theorem mem_of_pow_card_eq {F : Type} [Field F] [Finite F] (k : Subfield F) {a : F}
    (h : a ^ Nat.card k = a) : a ∈ k := by
  classical
  by_contra ha
  have : Fintype F := Fintype.ofFinite F
  have : Fintype k := Fintype.ofFinite k
  set q := Nat.card k with hq
  have hq1 : 1 < q := Finite.one_lt_card
  let Z : Finset F := insert a (Finset.univ.image (fun x : k => (x : F)))
  have haZ : a ∉ Finset.univ.image (fun x : k => (x : F)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact fun x hx => ha (hx ▸ x.2)
  have hZ : Z.card = q + 1 := by
    rw [Finset.card_insert_of_notMem haZ, Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hne : (X ^ q - X : F[X]) ≠ 0 := by
    intro h0
    have := FiniteField.X_pow_card_sub_X_natDegree_eq F hq1
    rw [h0, natDegree_zero] at this
    omega
  have hsub : Z.val ⊆ (X ^ q - X : F[X]).roots := by
    intro x hx
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]
    have hx' : x ∈ Z := hx
    rcases Finset.mem_insert.1 hx' with rfl | hx'
    · exact h
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx'
      have := FiniteField.pow_card y
      rw [Fintype.card_eq_nat_card] at this
      exact congrArg (Subtype.val : k → F) this
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hq1, hZ] at this
  omega

theorem mem_of_pow_nine {F : Type} [Field F] [Finite F] [CharP F 3] {k : Subfield F} {d : ℕ}
    (hd : Odd d) (hK : Nat.card F = Nat.card k ^ d) {a : F} (h : a ^ 9 = a) : a ∈ k := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype k := Fintype.ofFinite k
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hkc : CharP k 3 := inferInstance
  obtain ⟨m, -, hm⟩ := FiniteField.card k 3
  have hqm : Nat.card k = 3 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  obtain ⟨e, rfl⟩ := hd
  have hper1 : ∀ j : ℕ, a ^ 3 ^ (j + 2) = a ^ 3 ^ j := by
    intro j
    rw [pow_add, show (3 : ℕ) ^ 2 = 9 by norm_num, mul_comm, pow_mul, h]
  have hper : ∀ j s : ℕ, a ^ 3 ^ (j + 2 * s) = a ^ 3 ^ j := by
    intro j s
    induction s with
    | zero => rfl
    | succ s ih =>
      rw [show j + 2 * (s + 1) = (j + 2 * s) + 2 by ring, hper1, ih]
  have hF : Nat.card F = 3 ^ ((m : ℕ) * (2 * e + 1)) := by
    rw [hK, hqm, ← pow_mul]
  have h1 : a ^ Nat.card F = a := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card a
  have h2 : a ^ Nat.card k = a := by
    rw [hqm, ← hper (m : ℕ) ((m : ℕ) * e), show (m : ℕ) + 2 * ((m : ℕ) * e) =
      (m : ℕ) * (2 * e + 1) by ring, ← hF]
    exact h1
  exact mem_of_pow_card_eq k h2

end Fields

section Powers

variable {F : Type} [Field F]

theorem u2_pow (c : F) (n : ℕ) : u2 c ^ n = u2 ((n : F) * c) := by
  induction n with
  | zero => simp [u2_zero]
  | succ n ih => rw [pow_succ, ih, ← u2_add]; congr 1; push_cast; ring

theorem l2_pow (c : F) (n : ℕ) : l2 c ^ n = l2 ((n : F) * c) := by
  induction n with
  | zero => simp [l2_zero]
  | succ n ih => rw [pow_succ, ih, ← l2_add]; congr 1; push_cast; ring

theorem mkPSL_u2_ne_one {c : F} (hc : c ≠ 0) : mkPSL F (u2 c) ≠ 1 := by
  intro h
  rw [mkPSL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have h01 := congrFun (congrFun hr 0) 1
  simp [u2_coe, Matrix.scalar_apply] at h01
  first | exact hc h01 | exact hc h01.symm

theorem mkPSL_l2_ne_one {c : F} (hc : c ≠ 0) : mkPSL F (l2 c) ≠ 1 := by
  intro h
  rw [mkPSL, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have h10 := congrFun (congrFun hr 1) 0
  simp [l2_coe, Matrix.scalar_apply] at h10
  first | exact hc h10 | exact hc h10.symm

end Powers

section Lift

variable {F : Type} [Field F]

theorem eq_top_of_map_mkPSL_eq_top (h2 : (2 : F) ≠ 0) {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hH : M.map (mkPSL F) = ⊤) : M = ⊤ := by
  have hsq : ∀ g : SpecialLinearGroup (Fin 2) F, g * g ∈ M := by
    intro g
    have hg : mkPSL F g ∈ M.map (mkPSL F) := hH ▸ Subgroup.mem_top _
    obtain ⟨m, hmM, hm⟩ := Subgroup.mem_map.1 hg
    have hz : m⁻¹ * g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
      rw [mkPSL, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hm
      exact hm
    set z := m⁻¹ * g with hzdef
    have hgz : g = m * z := by rw [hzdef, mul_inv_cancel_left]
    have hcomm : m * z = z * m := Subgroup.mem_center_iff.1 hz m
    have : g * g = (m * m) * (z * z) := by
      rw [hgz]
      calc m * z * (m * z) = m * (z * m) * z := by group
        _ = m * (m * z) * z := by rw [hcomm]
        _ = (m * m) * (z * z) := by group
    rw [this, center_sq_eq_one hz, mul_one]
    exact M.mul_mem hmM hmM
  have hu : ∀ c : F, u2 c ∈ M := fun c => by
    have := hsq (u2 (c / 2))
    have e : c / 2 + c / 2 = c := by field_simp; ring
    rwa [← u2_add, e] at this
  have hl : ∀ c : F, l2 c ∈ M := fun c => by
    have := hsq (l2 (c / 2))
    have e : c / 2 + c / 2 = c := by field_simp; ring
    rwa [← l2_add, e] at this
  rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := F),
    Subgroup.closure_le]
  rintro g (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · have e : CFSG.LocalAnalysis.ComponentInitial.sl2Upper F c = u2 c :=
      Subtype.ext (by rw [CFSG.LocalAnalysis.ComponentInitial.coe_sl2Upper, u2_coe])
    rw [SetLike.mem_coe, e]
    exact hu c
  · have e : CFSG.LocalAnalysis.ComponentInitial.sl2Lower F c = l2 c :=
      Subtype.ext (by rw [CFSG.LocalAnalysis.ComponentInitial.coe_sl2Lower, l2_coe])
    rw [SetLike.mem_coe, e]
    exact hl c

end Lift

section Dickson


open CFSG.Glauberman.Dickson

theorem mem_of_pow_eq_one_of_sup {G : Type*} [Group G] {N C : Subgroup G} [N.Normal]
    (hdisj : Disjoint N C) (hsup : N ⊔ C = ⊤) {q : ℕ} (hq : q.Prime)
    (hcop : ¬ q ∣ Nat.card C) {g : G} (hg : g ^ q = 1) : g ∈ N := by
  have hg' : g ∈ N ⊔ C := hsup ▸ Subgroup.mem_top g
  obtain ⟨n, hn, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hg'
  have h1 : (QuotientGroup.mk' N c) ^ q = 1 := by
    have h := congrArg (QuotientGroup.mk' N) hg
    rw [map_pow, map_mul, map_one] at h
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rwa [hn1, one_mul] at h
  have hdvd1 : orderOf (QuotientGroup.mk' N c) ∣ q := orderOf_dvd_of_pow_eq_one h1
  have hdvd2 : orderOf (QuotientGroup.mk' N c) ∣ Nat.card C := by
    have h2 : orderOf c ∣ Nat.card C := by
      have := orderOf_dvd_natCard (⟨c, hc⟩ : C)
      rwa [Subgroup.orderOf_mk] at this
    exact (orderOf_map_dvd _ c).trans h2
  have hord : orderOf (QuotientGroup.mk' N c) = 1 := by
    rcases (Nat.dvd_prime hq).1 hdvd1 with h | h
    · exact h
    · rw [h] at hdvd2
      exact absurd hdvd2 hcop
  have hcN : c ∈ N := (QuotientGroup.eq_one_iff c).1 (orderOf_eq_one_iff.1 hord)
  have hc1 : c = 1 := Subgroup.disjoint_def.mp hdisj hcN hc
  rw [hc1, mul_one]
  exact hn

theorem witness_eq_top_odd {F : Type} [Field F] [Finite F] {k : Subfield F} {d : ℕ}
    (hd : d.Prime) (hK : Nat.card F = Nat.card k ^ d) (h8 : (8 : F) ≠ 0) {a : F} (ha : a ∉ k)
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)} (hu : ∀ c ∈ k, u2 c ∈ M)
    (hl : ∀ c ∈ k, l2 (c * a) ∈ M) {p m : ℕ}
    (W : SubfieldConjugacyWitness p m (M.map (mkPSL F))) : W.K = ⊤ := by
  have ha0 : a ≠ 0 := fun h => ha (h ▸ k.zero_mem)
  have h2 : (2 : F) ≠ 0 := fun h => h8 (by
    rw [show (8 : F) = 2 * 2 * 2 by norm_num, h]; ring)
  have h2K : (2 : F) ∈ W.K := by simp
  have h8K : (8 : F) ∈ W.K := by simp
  have hsq : ∀ c ∈ k, c ≠ 0 → (2 + c * a) ^ 2 ∈ W.K := by
    intro c hc hc0
    set A : SpecialLinearGroup (Fin 2) F := u2 1 * l2 (c * a) with hA
    have hAM : A ∈ M := M.mul_mem (hu 1 k.one_mem) (hl c hc)
    have hT : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = 2 + c * a := by
      rw [hA, trace_u2_mul_l2_odd, one_mul]
    have hT0 : 2 + c * a ≠ 0 := by
      intro h0
      apply ha
      have : a = -2 / c := by field_simp; linear_combination h0
      rw [this]
      exact k.div_mem (k.neg_mem (by simp)) hc
    have h := normalizedTrace_mem_subfield (M.map (mkPSL F)) W
      ⟨mkPSL F A, Subgroup.mem_map_of_mem _ hAM⟩ ⟨mkPSL F A, Subgroup.mem_map_of_mem _ hAM⟩
      A A rfl rfl (by rw [hT]; exact hT0) (by rw [hT]; exact hT0)
    rw [← pow_two, trace_pow_two, hT] at h
    have e1 : ((2 + c * a) ^ 2 - 2) / ((2 + c * a) * (2 + c * a)) = 1 - 2 / (2 + c * a) ^ 2 := by
      field_simp
    rw [e1] at h
    have h3 : 2 / (2 + c * a) ^ 2 ∈ W.K := by
      have := W.K.sub_mem W.K.one_mem h
      simpa using this
    have h4 : (2 + c * a) ^ 2 / 2 ∈ W.K := by
      have := W.K.inv_mem h3
      rwa [inv_div] at this
    have h5 := W.K.mul_mem h4 h2K
    rwa [div_mul_cancel₀ _ h2] at h5
  have hca : ∀ c ∈ k, c ≠ 0 → c * a ∈ W.K := by
    intro c hc hc0
    have h3 := W.K.sub_mem (hsq c hc hc0) (hsq (-c) (k.neg_mem hc) (neg_ne_zero.2 hc0))
    have e : (2 + c * a) ^ 2 - (2 + -c * a) ^ 2 = 8 * (c * a) := by ring
    rw [e] at h3
    have := W.K.mul_mem h3 (W.K.inv_mem h8K)
    rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ h8, one_mul] at this
  have haW : a ∈ W.K := by simpa using hca 1 k.one_mem one_ne_zero
  have hkW : k ≤ W.K := by
    intro c hc
    by_cases hc0 : c = 0
    · rw [hc0]; exact W.K.zero_mem
    · have := W.K.mul_mem (hca c hc hc0) (W.K.inv_mem haW)
      rwa [mul_inv_cancel_right₀ ha0] at this
  rcases subfield_eq_or_eq_top hkW hd hK with h | h
  · exact absurd (h ▸ haW) ha
  · exact h

theorem pow_central_of_equiv {F : Type} [Field F] {X : Type*} [Group X]
    {M : Subgroup (SpecialLinearGroup (Fin 2) F)} (e : ↥(M.map (mkPSL F)) ≃* X)
    {g : SpecialLinearGroup (Fin 2) F} (hg : g ∈ M) {n : ℕ}
    (hn : (e ⟨mkPSL F g, Subgroup.mem_map_of_mem _ hg⟩) ^ n = 1) :
    g ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
  have h1 : (⟨mkPSL F g, Subgroup.mem_map_of_mem _ hg⟩ : ↥(M.map (mkPSL F))) ^ n = 1 :=
    e.injective (by rw [map_pow, hn, map_one])
  have h2 : (mkPSL F g) ^ n = 1 := by simpa using congrArg Subtype.val h1
  exact mkPSL_pow_eq_one_iff.1 h2

theorem false_of_pow_central_three {F : Type} [Field F] [Finite F] [CharP F 3] {k : Subfield F}
    {d : ℕ} (hd : Odd d) (hK : Nat.card F = Nat.card k ^ d) {a : F} (ha : a ∉ k)
    {g : SpecialLinearGroup (Fin 2) F}
    (hT : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 2 + a)
    (h : g ^ 2 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      g ^ 3 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      g ^ 4 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ∨
      g ^ 5 ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) : False := by
  have := pow_nine_of_pow_central h
  rw [hT] at this
  exact ha (mem_of_pow_nine hd hK (pow_nine_of_trace this))

theorem sl2_eq_top_of_root_lines_odd {F : Type} [Field F] [Finite F] {r : ℕ} [CharP F r]
    (hr3 : 3 ≤ r) {k : Subfield F} {d : ℕ} (hd : d.Prime) (hrd : 5 ≤ r ∨ d ≠ 2)
    (hK : Nat.card F = Nat.card k ^ d)
    {a : F} (ha : a ∉ k) {M : Subgroup (SpecialLinearGroup (Fin 2) F)}
    (hu : ∀ c ∈ k, u2 c ∈ M) (hl : ∀ c ∈ k, l2 (c * a) ∈ M) : M = ⊤ := by
  classical
  have hrp : r.Prime := (CharP.char_is_prime_or_zero F r).resolve_right (by omega)
  have : Fact r.Prime := ⟨hrp⟩
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hFf⟩ := FiniteField.card F r
  have hF : Nat.card F = r ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hFf
  have hf0 : 0 < (f : ℕ) := f.pos
  have hnz : ∀ n : ℕ, 0 < n → n < r → (n : F) ≠ 0 := fun n hn hnr h => by
    have := (CharP.cast_eq_zero_iff F r n).1 h
    exact absurd (Nat.le_of_dvd hn this) (by omega)
  have h2 : (2 : F) ≠ 0 := by simpa using hnz 2 (by norm_num) (by omega)
  have h8 : (8 : F) ≠ 0 := by rw [show (8 : F) = 2 ^ 3 by norm_num]; exact pow_ne_zero 3 h2
  have ha0 : a ≠ 0 := fun h => ha (h ▸ k.zero_mem)
  have hxM : u2 (1 : F) ∈ M := hu 1 k.one_mem
  have hyM : l2 a ∈ M := by simpa using hl 1 k.one_mem
  have hrr : (r : F) = 0 := CharP.cast_eq_zero F r
  let H : Subgroup (PSL2MatrixGroup F) := M.map (mkPSL F)
  let x : H := ⟨mkPSL F (u2 1), Subgroup.mem_map_of_mem _ hxM⟩
  let y : H := ⟨mkPSL F (l2 a), Subgroup.mem_map_of_mem _ hyM⟩
  have hxy : x * y ≠ y * x := fun h => mkPSL_u2_l2_comm_ne ha0 (congrArg Subtype.val h)
  have hxr : x ^ r = 1 := Subtype.ext (by
    show (mkPSL F (u2 1)) ^ r = 1
    rw [← map_pow, u2_pow, hrr, zero_mul, u2_zero, map_one])
  have hyr : y ^ r = 1 := Subtype.ext (by
    show (mkPSL F (l2 a)) ^ r = 1
    rw [← map_pow, l2_pow, hrr, zero_mul, l2_zero, map_one])
  have hx1 : x ≠ 1 := fun h => mkPSL_u2_ne_one (one_ne_zero (α := F)) (congrArg Subtype.val h)
  have hrdvd : r ∣ Nat.card H := by
    rw [← orderOf_eq_prime hxr hx1]
    exact orderOf_dvd_natCard x
  have hNr : r ∣ Nat.card F := by rw [hF]; exact dvd_pow_self r hf0.ne'
  have hrodd : Odd r := hrp.odd_of_ne_two (by omega)
  have hNodd : Odd (Nat.card F) := by rw [hF]; exact hrodd.pow
  have hg2 : Nat.gcd (Nat.card F - 1) 2 = 2 := by
    apply Nat.gcd_eq_right
    obtain ⟨c, hc⟩ := hNodd
    exact ⟨c, by omega⟩
  have hr1 : ¬ r ∣ Nat.card F - 1 := by
    intro h
    have h1 : r ∣ (Nat.card F - 1) + 1 := by
      rw [Nat.sub_add_cancel Nat.card_pos]; exact hNr
    exact hrp.not_dvd_one ((Nat.dvd_add_right h).1 h1)
  have hr2 : ¬ r ∣ Nat.card F + 1 := fun h => hrp.not_dvd_one ((Nat.dvd_add_right hNr).1 h)
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield (p := r)
      (f := (f : ℕ)) hF H with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, hz, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m', t, -, ht, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩ | ⟨m, hm0, hmf, ⟨eP⟩, ⟨W⟩⟩
  · exact absurd (hEl.toIsMulCommutative.is_comm.comm x y) hxy
  · have : IsCyclic H := hcyc
    exact absurd (IsCyclic.isMulCommutative.is_comm.comm x y) hxy
  ·
    exfalso
    rw [hg2] at hz
    have h2dvd1 : 2 ∣ Nat.card F - 1 := by
      obtain ⟨c, hc⟩ := hNodd
      exact ⟨c, by omega⟩
    have h2dvd2 : 2 ∣ Nat.card F + 1 := by
      obtain ⟨c, hc⟩ := hNodd
      exact ⟨c + 1, by omega⟩
    have hrz : r ∣ z := by
      rw [hcard] at hrdvd
      rcases (Nat.Prime.dvd_mul hrp).1 hrdvd with h | h
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact h
    rcases hz with hz | hz
    · exact hr1 ((hrz.trans hz).trans (Nat.div_dvd_of_dvd h2dvd1))
    · exact hr2 ((hrz.trans hz).trans (Nat.div_dvd_of_dvd h2dvd2))
  ·
    by_cases hr5 : 5 ≤ r
    · exfalso
      have h12 : Nat.card H = 12 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Fintype.card_fin]
        decide
      rw [h12, show (12 : ℕ) = 2 * 2 * 3 by norm_num] at hrdvd
      rcases (Nat.Prime.dvd_mul hrp).1 hrdvd with h | h
      · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h <;>
          exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exfalso
      have hr3e : r = 3 := by
        interval_cases r
        · rfl
        · norm_num at hrp
      subst hr3e
      have hd2 : Odd d := hd.odd_of_ne_two (hrd.resolve_left hr5)
      have hg : u2 (1 : F) * l2 a ∈ M := M.mul_mem hxM hyM
      have hT : Matrix.trace ((u2 1 * l2 a : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = 2 + a := by rw [trace_u2_mul_l2_odd, one_mul]
      have hord : ∀ σ : alternatingGroup (Fin 4), σ ^ 2 = 1 ∨ σ ^ 3 = 1 := by decide
      rcases hord (e ⟨mkPSL F (u2 1 * l2 a), Subgroup.mem_map_of_mem _ hg⟩) with h | h
      · exact false_of_pow_central_three hd2 hK ha hT (Or.inl (pow_central_of_equiv e hg h))
      · exact false_of_pow_central_three hd2 hK ha hT
          (Or.inr (Or.inl (pow_central_of_equiv e hg h)))
  ·
    by_cases hr5 : 5 ≤ r
    · exfalso
      have h24 : Nat.card H = 24 := by
        rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
        simp [Fintype.card_fin]
        decide
      rw [h24, show (24 : ℕ) = 2 * 2 * 2 * 3 by norm_num] at hrdvd
      rcases (Nat.Prime.dvd_mul hrp).1 hrdvd with h | h
      · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h <;>
            exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
    · exfalso
      have hr3e : r = 3 := by
        interval_cases r
        · rfl
        · norm_num at hrp
      subst hr3e
      have hd2 : Odd d := hd.odd_of_ne_two (hrd.resolve_left hr5)
      have hg : u2 (1 : F) * l2 a ∈ M := M.mul_mem hxM hyM
      have hT : Matrix.trace ((u2 1 * l2 a : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = 2 + a := by rw [trace_u2_mul_l2_odd, one_mul]
      have hord : ∀ σ : Equiv.Perm (Fin 4), σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by decide
      rcases hord (e ⟨mkPSL F (u2 1 * l2 a), Subgroup.mem_map_of_mem _ hg⟩) with h | h | h
      · exact false_of_pow_central_three hd2 hK ha hT (Or.inl (pow_central_of_equiv e hg h))
      · exact false_of_pow_central_three hd2 hK ha hT
          (Or.inr (Or.inl (pow_central_of_equiv e hg h)))
      · exact false_of_pow_central_three hd2 hK ha hT
          (Or.inr (Or.inr (Or.inl (pow_central_of_equiv e hg h))))
  ·
    by_cases hr3e : r = 3
    · exfalso
      subst hr3e
      have hd2 : Odd d := hd.odd_of_ne_two (hrd.resolve_left (by omega))
      have hg : u2 (1 : F) * l2 a ∈ M := M.mul_mem hxM hyM
      have hT : Matrix.trace ((u2 1 * l2 a : SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = 2 + a := by rw [trace_u2_mul_l2_odd, one_mul]
      rcases CFSG.RankThree.PartOne.SEITZ2.alternating_five_orders
          (e ⟨mkPSL F (u2 1 * l2 a), Subgroup.mem_map_of_mem _ hg⟩) with h | h | h
      · exact false_of_pow_central_three hd2 hK ha hT (Or.inl (pow_central_of_equiv e hg h))
      · exact false_of_pow_central_three hd2 hK ha hT
          (Or.inr (Or.inl (pow_central_of_equiv e hg h)))
      · exact false_of_pow_central_three hd2 hK ha hT
          (Or.inr (Or.inr (Or.inr (pow_central_of_equiv e hg h))))
    exfalso
    have h60 : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Fintype.card_fin]
      decide
    have hr5eq : r = 5 := by
      rw [h60, show (60 : ℕ) = 2 * 2 * 3 * 5 by norm_num] at hrdvd
      rcases (Nat.Prime.dvd_mul hrp).1 hrdvd with h | h
      · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hrp).1 h with h | h <;>
            exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
        · exact absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
      · have := Nat.le_of_dvd (by norm_num) h
        have hr4 : r ≠ 4 := fun e => by rw [e] at hrp; norm_num at hrp
        omega
    subst hr5eq
    have hg : u2 (1 : F) * l2 a ∈ M := M.mul_mem hxM hyM
    set g : SpecialLinearGroup (Fin 2) F := u2 1 * l2 a with hgdef
    let gH : H := ⟨mkPSL F g, Subgroup.mem_map_of_mem _ hg⟩
    have hT : Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) = 2 + a := by
      rw [hgdef, trace_u2_mul_l2_odd, one_mul]
    have hcen : ∀ n : ℕ, (e gH) ^ n = 1 →
        g ^ n ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := fun n hn => by
      have h1 : gH ^ n = 1 := e.injective (by rw [map_pow, hn, map_one])
      have h2 : (mkPSL F g) ^ n = 1 := by
        simpa [gH] using congrArg Subtype.val h1
      exact mkPSL_pow_eq_one_iff.1 h2
    obtain ⟨n, hn⟩ := exists_int_of_pow_central hT (by
      rcases CFSG.RankThree.PartOne.SEITZ2.alternating_five_orders (e gH) with h | h | h
      · exact Or.inl (hcen 2 h)
      · exact Or.inr (Or.inl (hcen 3 h))
      · exact Or.inr (Or.inr (hcen 5 h)))
    exact ha (hn ▸ intCast_mem k n)
  ·
    exfalso
    have := hN
    have hr1' : ¬ r ∣ r ^ (f : ℕ) - 1 := by rw [← hF]; exact hr1
    have hcop : ¬ r ∣ Nat.card C := by
      rw [hCcard]
      intro h
      exact hr1' (h.trans (ht.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))))
    have hxN : x ∈ N := mem_of_pow_eq_one_of_sup hdisj hsup hrp hcop hxr
    have hyN : y ∈ N := mem_of_pow_eq_one_of_sup hdisj hsup hrp hcop hyr
    have hcN := hNel.toIsMulCommutative.is_comm.comm (⟨x, hxN⟩ : N) ⟨y, hyN⟩
    exact hxy (congrArg Subtype.val hcN)
  ·
    have hWK : W.K = ⊤ := witness_eq_top_odd hd hK h8 ha hu hl W
    have hmf' : m = (f : ℕ) := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective hrp.two_le h1
    have e2 : GaloisField r m ≃+* F := by
      have := Fintype.ofFinite (GaloisField r m)
      exact FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, GaloisField.card r m hm0,
          hmf'])
    have hcardH : Nat.card H = Nat.card (PSL2MatrixGroup F) := by
      rw [Nat.card_congr eP.toEquiv]
      exact Nat.card_congr (h826_pslEquiv e2).toEquiv
    exact eq_top_of_map_mkPSL_eq_top h2 (Subgroup.eq_top_of_card_eq H hcardH)
  ·
    exfalso
    have hWK : W.K = ⊤ := witness_eq_top_odd hd hK h8 ha hu hl W
    have hmf' : m = (f : ℕ) := by
      have h1 : Nat.card W.K = Nat.card F := by
        rw [hWK]
        exact Nat.card_congr Subfield.topEquiv.toEquiv
      rw [W.card_eq, hF] at h1
      exact Nat.pow_right_injective hrp.two_le h1
    have := Nat.le_of_dvd hf0 hmf
    omega

end Dickson

end CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair
