module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

universe u

namespace CFSG.GH74.KGroups.L3Eps

open Matrix Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

section Field

variable {K : Type*} [Field K]

theorem pow_apply_of_frob {p : ℕ} {φ : K ≃+* K} (hφ : ∀ x, φ x = x ^ p) :
    ∀ (k : ℕ) (x : K), (φ ^ k) x = x ^ p ^ k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]

theorem eq_pow_of_involution [Finite K] {σ : K ≃+* K} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) :
    ∃ q₀ : ℕ, q₀ * q₀ = Nat.card K ∧ ∀ x, σ x = x ^ q₀ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp0⟩ : ∃ p, CharP K p := ⟨ringChar K, ringChar.charP K⟩
  obtain ⟨n, hp, hpn⟩ := FiniteField.card K p
  have hcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hpn
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality hp n.pos hcard
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; exact n.pos)
  obtain ⟨k, hk, rfl⟩ : ∃ k < (n : ℕ), φ ^ k = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k % n, Nat.mod_lt _ n.pos, ?_⟩
    rw [← hk, ← hord, pow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hσ (pow_zero φ)
  have h2k : (n : ℕ) ∣ 2 * k := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, two_mul, pow_add, hσσ]
  obtain ⟨c, hc⟩ := h2k
  have hc1 : c = 1 := by
    rcases c with _ | _ | c
    · omega
    · rfl
    · nlinarith [n.pos]
  rw [hc1, mul_one] at hc
  refine ⟨p ^ k, ?_, fun x => pow_apply_of_frob hφ k x⟩
  rw [hcard, ← pow_add, ← two_mul, ← hc]

theorem exists_orderOf_eq_of_dvd [Finite K] {d : ℕ}
    (hd : d ∣ Nat.card Kˣ) : ∃ x : Kˣ, orderOf x = d := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf γ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hγ
  obtain ⟨r, hr⟩ := hd
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact (Nat.card_pos (α := Kˣ)).ne' hr
  refine ⟨γ ^ r, ?_⟩
  rw [orderOf_pow_of_dvd hr0 (by rw [hord, hr]; exact Dvd.intro_left _ rfl), hord, hr,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]

theorem exists_pow_eq_of_pow_eq [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) {y : K} (hy : y ^ q = y) : ∃ b : K, b ^ (q + 1) = y := by
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0, zero_pow (by omega)]⟩
  have hcard : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hK]
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf γ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hγ
  have hmem : (Units.mk0 y hy0) ∈ Submonoid.powers γ :=
    mem_powers_iff_mem_zpowers.2 (hγ _)
  obtain ⟨k, hk0⟩ := hmem
  have hk : γ ^ k = Units.mk0 y hy0 := hk0
  have hq1 : 1 ≤ q := by omega
  have hdiv : γ ^ (k * (q - 1)) = 1 := by
    have h1 : (Units.mk0 y hy0) ^ q = Units.mk0 y hy0 := Units.ext (by simpa using hy)
    rw [← hk, ← pow_mul] at h1
    have h2 : γ ^ (k * q) = γ ^ k * γ ^ (k * (q - 1)) := by
      rw [← pow_add]; congr 1
      zify [hq1]; ring
    rw [h2] at h1
    exact (mul_eq_left.1 h1)
  have hdvd : q ^ 2 - 1 ∣ k * (q - 1) := by
    rw [← hcard, ← hord]
    exact orderOf_dvd_iff_pow_eq_one.2 hdiv
  have hsq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [hq1, Nat.one_le_pow 2 _ hq1]
    ring
  rw [hsq] at hdvd
  have hq0 : 0 < q - 1 := by omega
  obtain ⟨m, hm⟩ := Nat.dvd_of_mul_dvd_mul_right hq0 hdvd
  refine ⟨(γ ^ m : Kˣ), ?_⟩
  have : (γ ^ m : Kˣ) ^ (q + 1) = Units.mk0 y hy0 := by
    rw [← pow_mul, ← hk, hm, mul_comm]
  have := congrArg (fun u : Kˣ => (u : K)) this
  simpa using this

omit [Field K] in
theorem two_mul_pow_dvd_sq_sub_one {q e : ℕ} (hodd : Odd q) (he : 2 ^ e ∣ q + 1) :
    2 * 2 ^ e ∣ q ^ 2 - 1 := by
  have h1 : 1 ≤ q := hodd.pos
  have : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [h1, Nat.one_le_pow 2 _ h1]
    ring
  rw [this]
  exact Nat.mul_dvd_mul (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩) he

omit [Field K] in
theorem two_mul_pow_dvd_sq_sub_one' {q a : ℕ} (hodd : Odd q) (ha : 2 ^ a ∣ q - 1) :
    2 * 2 ^ a ∣ q ^ 2 - 1 := by
  have h1 : 1 ≤ q := hodd.pos
  have : q ^ 2 - 1 = (q + 1) * (q - 1) := by
    zify [h1, Nat.one_le_pow 2 _ h1]
    ring
  rw [this]
  exact Nat.mul_dvd_mul (by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩) ha

theorem odd_card_of_ringChar_ne_two [Finite K] (hK2 : ringChar K ≠ 2) : Odd (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hK2)

end Field

section Matrices

variable {K : Type*} [Field K]

@[expose] def diagSL (a b c : K) (h : a * b * c = 1) : SL(3, K) :=
  ⟨Matrix.diagonal ![a, b, c], by
    rw [Matrix.det_diagonal]
    simpa [Fin.prod_univ_succ, mul_assoc] using h⟩

theorem coe_diagSL (a b c : K) (h : a * b * c = 1) :
    ((diagSL a b c h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal ![a, b, c] := rfl

theorem diagSL_congr {a b c a' b' c' : K} {h : a * b * c = 1} {h' : a' * b' * c' = 1}
    (ha : a = a') (hb : b = b') (hc : c = c') : diagSL a b c h = diagSL a' b' c' h' := by
  subst ha hb hc
  rfl

theorem diagSL_mul (a b c a' b' c' : K) (h : a * b * c = 1) (h' : a' * b' * c' = 1) :
    diagSL a b c h * diagSL a' b' c' h' = diagSL (a * a') (b * b') (c * c') (by
      calc a * a' * (b * b') * (c * c') = (a * b * c) * (a' * b' * c') := by ring
        _ = 1 := by rw [h, h', one_mul]) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_diagSL, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem diagSL_one (h : (1 : K) * 1 * 1 = 1) : diagSL (1 : K) 1 1 h = 1 := by
  apply Subtype.ext
  simp only [coe_diagSL, Matrix.SpecialLinearGroup.coe_one]
  rw [← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp

theorem trace_diagSL (a b c : K) (h : a * b * c = 1) :
    ((diagSL a b c h : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace = a + b + c := by
  simp [coe_diagSL, Matrix.trace_diagonal, Fin.sum_univ_succ, add_assoc]

theorem diagSL_pow (a b c : K) (h : a * b * c = 1) (n : ℕ) :
    diagSL a b c h ^ n = diagSL (a ^ n) (b ^ n) (c ^ n) (by
      calc a ^ n * b ^ n * c ^ n = (a * b * c) ^ n := by ring
        _ = 1 := by rw [h, one_pow]) := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact (diagSL_one (by ring)).symm
  | succ n ih =>
    rw [pow_succ, ih, diagSL_mul]
    exact diagSL_congr (pow_succ _ _).symm (pow_succ _ _).symm (pow_succ _ _).symm

theorem diagSL_unitary {p f : ℕ} (h : UnitaryFieldData p f K) (a b c : K) (habc : a * b * c = 1)
    (ha : h.bar a * a = 1) (hb : h.bar b * b = 1) (hc : h.bar c * c = 1) :
    (((diagSL a b c habc : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
      ((diagSL a b c habc : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  simp only [coe_diagSL]
  rw [Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  fin_cases i <;> simp [ha, hb, hc]

@[expose] def blk (M : Matrix (Fin 2) (Fin 2) K) (c : K) : Matrix (Fin 3) (Fin 3) K :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, c]

theorem blk_mul (M M' : Matrix (Fin 2) (Fin 2) K) (c c' : K) :
    blk M c * blk M' c' = blk (M * M') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.mul_apply, Fin.sum_univ_succ]

theorem blk_one : blk (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem det_blk (M : Matrix (Fin 2) (Fin 2) K) (c : K) : (blk M c).det = M.det * c := by
  simp [blk, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

theorem trace_blk (M : Matrix (Fin 2) (Fin 2) K) (c : K) : (blk M c).trace = M.trace + c := by
  simp [blk, Matrix.trace_fin_three, Matrix.trace_fin_two]

theorem blk_pow (M : Matrix (Fin 2) (Fin 2) K) (c : K) (n : ℕ) :
    blk M c ^ n = blk (M ^ n) (c ^ n) := by
  induction n with
  | zero => simp [blk_one]
  | succ n ih => rw [pow_succ, ih, blk_mul, ← pow_succ, ← pow_succ]

theorem blk_map {L : Type*} [Field L] (φ : K →+* L) (M : Matrix (Fin 2) (Fin 2) K) (c : K) :
    (blk M c).map φ = blk (M.map φ) (φ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_transpose (M : Matrix (Fin 2) (Fin 2) K) (c : K) : (blk M c)ᵀ = blk Mᵀ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

end Matrices

section Linear

variable {K : Type u} [Field K]

theorem exists_trace_ne_inv_lin_split (hK : ringChar K ≠ 2) {i : K} (hi : i * i = -1) :
    ∃ g : SL(3, K), (∃ k, g ^ 2 ^ k = 1) ∧
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace ≠
        (g : Matrix (Fin 3) (Fin 3) K).trace := by
  have h1 : i * i * (-1) = 1 := by rw [hi]; ring
  have h2 : (-i) * (-i) * (-1) = 1 := by rw [neg_mul_neg]; exact h1
  have h3 : i * (-i) = 1 := by rw [mul_neg, hi]; ring
  have h2K : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  let g : SL(3, K) := diagSL i i (-1) h1
  let g' : SL(3, K) := diagSL (-i) (-i) (-1) h2
  have hg : g * g' = 1 := by
    simp only [g, g', diagSL_mul]
    rw [← diagSL_one (by ring)]
    exact diagSL_congr h3 h3 (by simp)
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_right hg
  refine ⟨g, ⟨2, ?_⟩, ?_⟩
  · have hsq : g * g = diagSL (-1) (-1) 1 (by ring) := by
      simp only [g, diagSL_mul]
      exact diagSL_congr hi hi (by simp)
    have h4 : g * g * (g * g) = 1 := by
      rw [hsq, diagSL_mul, ← diagSL_one (by ring)]
      exact diagSL_congr (by simp) (by simp) (by simp)
    have : g ^ 2 ^ 2 = g * g * (g * g) := by
      rw [show (2 : ℕ) ^ 2 = 4 from rfl]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    exact h4
  · rw [hinv]
    simp only [g, g', trace_diagSL]
    intro h
    have : (4 : K) * i = 0 := by linear_combination -h
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2K h2K
    exact mul_ne_zero h4 hi0 this

theorem exists_quadratic_extension [Finite K] (hK2 : ringChar K ≠ 2) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Finite L), Module.finrank K L = 2 := by
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hK2
  have hirr : Irreducible (X ^ 2 - C n : K[X]) := by
    apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    exact hn ⟨b, by rw [← hb]; ring⟩
  have : Fact (Irreducible (X ^ 2 - C n : K[X])) := ⟨hirr⟩
  have hP0 : (X ^ 2 - C n : K[X]) ≠ 0 := hirr.ne_zero
  have hfin : Module.finrank K (AdjoinRoot (X ^ 2 - C n : K[X])) = 2 := by
    rw [(AdjoinRoot.powerBasis hP0).finrank, AdjoinRoot.powerBasis_dim, natDegree_X_pow_sub_C]
  have : Module.Finite K (AdjoinRoot (X ^ 2 - C n : K[X])) :=
    (AdjoinRoot.powerBasis hP0).finite
  exact ⟨AdjoinRoot (X ^ 2 - C n : K[X]), inferInstance, inferInstance,
    Module.finite_of_finite K, hfin⟩

theorem nat_card_field_ext {L : Type*} [Field L] [Algebra K L] [Finite L]
    (hfin : Module.finrank K L = 2) : Nat.card L = Nat.card K ^ 2 := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := L), hfin]

variable {L : Type*} [Field L] [Algebra K L] [Finite L]

theorem exists_trace_ne_inv_lin_nonsplit (hK2 : ringChar K ≠ 2) (hq : Nat.card K % 4 = 3)
    (hfin : Module.finrank K L = 2) :
    ∃ g : SL(3, K), (∃ k, g ^ 2 ^ k = 1) ∧
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace ≠
        (g : Matrix (Fin 3) (Fin 3) K).trace := by
  set q := Nat.card K with hqdef
  have hodd : Odd q := by rw [Nat.odd_iff]; omega
  set e := padicValNat 2 (q + 1) with hedef
  have hq1 : q + 1 ≠ 0 := by omega
  have he : 2 ^ e ∣ q + 1 := pow_padicValNat_dvd
  have he2 : 2 ≤ e := by
    have : 2 ^ 2 ∣ q + 1 := by omega
    exact (padicValNat_dvd_iff_le hq1).1 this
  have hcardL : Nat.card Lˣ = q ^ 2 - 1 := by rw [Nat.card_units, nat_card_field_ext hfin]
  obtain ⟨x, hx⟩ := exists_orderOf_eq_of_dvd (K := L) (d := 2 * 2 ^ e)
    (by rw [hcardL]; exact two_mul_pow_dvd_sq_sub_one hodd he)
  set y : L := (x : L) with hy
  have hy0 : y ≠ 0 := x.ne_zero
  have hxN : x ^ (2 * 2 ^ e) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h2q : x ^ (2 * (q + 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hx ▸ Nat.mul_dvd_mul_left 2 he)
  have hq1' : ¬ x ^ (q + 1) = 1 := by
    intro h1
    have : 2 * 2 ^ e ∣ q + 1 := hx ▸ orderOf_dvd_iff_pow_eq_one.2 h1
    have h3 : 2 ^ (e + 1) ∣ q + 1 := by rwa [pow_succ, mul_comm]
    have := (padicValNat_dvd_iff_le hq1).1 h3
    omega
  have hyq1 : y ^ (q + 1) = -1 := by
    have h1 : y ^ (q + 1) * y ^ (q + 1) = 1 := by
      rw [← pow_add, ← two_mul, hy, ← Units.val_pow_eq_pow_val, h2q, Units.val_one]
    rcases mul_self_eq_one_iff.1 h1 with h | h
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)) hq1'
    · exact h
  have hyq : y ^ q = -y⁻¹ := by
    have : y ^ q * y = -1 := by rw [← pow_succ]; exact hyq1
    field_simp at this ⊢
    linear_combination this
  have hy2 : y ^ 2 ≠ 1 := by
    intro h
    have h1 : x ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)
    have : 2 * 2 ^ e ∣ 2 := hx ▸ orderOf_dvd_iff_pow_eq_one.2 h1
    have : 2 ^ e ∣ 1 := by
      have := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
        (by simpa using this : 2 * 2 ^ e ∣ 2 * 1)
      exact this
    have := Nat.le_of_dvd (by norm_num) this
    have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he2
    omega
  let B : Module.Basis (Fin 2) K L := Module.finBasisOfFinrankEq K L hfin
  let M : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix B y
  let Mi : Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix B y⁻¹
  have hMMi : M * Mi = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hy0, map_one]
  have hMN : M ^ (2 * 2 ^ e) = 1 := by
    rw [← map_pow, hy, ← Units.val_pow_eq_pow_val, hxN, Units.val_one, map_one]
  have hnorm : Algebra.norm K y = -1 := by
    apply (algebraMap K L).injective
    rw [FiniteField.algebraMap_norm_eq_prod_pow K L y, hfin]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one, map_neg,
      map_one]
    rw [← pow_succ', ← hqdef]
    exact hyq1
  have hdet : M.det = -1 := by
    rw [← hnorm, Algebra.norm_eq_matrix_det B y]
  have hdet' : Mi.det = -1 := by
    have : M.det * Mi.det = 1 := by rw [← Matrix.det_mul, hMMi, Matrix.det_one]
    rw [hdet] at this
    linear_combination -this
  have hdetg : (blk M (-1)).det = 1 := by rw [det_blk, hdet]; ring
  have hgg' : blk M (-1) * blk Mi (-1) = 1 := by
    rw [blk_mul, hMMi, ← blk_one]
    congr 1
    ring
  let g : SL(3, K) := ⟨blk M (-1), hdetg⟩
  let g' : SL(3, K) := ⟨blk Mi (-1), by rw [det_blk, hdet']; ring⟩
  have hg : g * g' = 1 := Subtype.ext hgg'
  have hinv : g⁻¹ = g' := inv_eq_of_mul_eq_one_right hg
  refine ⟨g, ⟨e + 1, ?_⟩, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change blk M (-1) ^ 2 ^ (e + 1) = 1
    rw [blk_pow, pow_succ', hMN, ← blk_one]
    congr 1
    exact (Even.neg_one_pow ⟨2 ^ e, by ring⟩)
  · rw [hinv]
    change (blk Mi (-1)).trace ≠ (blk M (-1)).trace
    rw [trace_blk, trace_blk]
    intro h
    have htr : Mi.trace = M.trace := by linear_combination h
    have hT : Algebra.trace K L y⁻¹ = Algebra.trace K L y := by
      rw [Algebra.trace_eq_matrix_trace B y⁻¹, Algebra.trace_eq_matrix_trace B y]
      exact htr
    have h1 := FiniteField.algebraMap_trace_eq_sum_pow K L y
    have h2 := FiniteField.algebraMap_trace_eq_sum_pow K L y⁻¹
    rw [hfin] at h1 h2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h1 h2
    rw [← hqdef] at h1 h2
    have h3 : y⁻¹ + (y⁻¹) ^ q = y + y ^ q := by rw [← h1, ← h2, hT]
    rw [inv_pow, hyq, inv_neg, inv_inv] at h3
    have h2L : (2 : L) ≠ 0 := by
      intro h20
      apply Ring.two_ne_zero hK2
      apply (algebraMap K L).injective
      rw [map_ofNat, map_zero]
      exact h20
    have : (2 : L) * (y - y⁻¹) = 0 := by linear_combination -h3
    rcases mul_eq_zero.1 this with h | h
    · exact h2L h
    · apply hy2
      field_simp at h
      linear_combination h

end Linear

section LinearAll

variable {K : Type u} [Field K]

theorem exists_trace_ne_inv_lin [Finite K] (hK2 : ringChar K ≠ 2) :
    ∃ g : SL(3, K), (∃ k, g ^ 2 ^ k = 1) ∧
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace ≠
        (g : Matrix (Fin 3) (Fin 3) K).trace := by
  have hodd := odd_card_of_ringChar_ne_two hK2
  have h13 : Nat.card K % 4 = 1 ∨ Nat.card K % 4 = 3 := by
    rcases hodd with ⟨k, hk⟩
    omega
  rcases h13 with h1 | h3
  · have : Fintype K := Fintype.ofFinite K
    have hsq : IsSquare (-1 : K) :=
      FiniteField.isSquare_neg_one_iff.2 (by rw [← Nat.card_eq_fintype_card]; omega)
    obtain ⟨i, hi⟩ := hsq
    exact exists_trace_ne_inv_lin_split hK2 (i := i) (by rw [hi])
  · obtain ⟨L, _, _, _, hfin⟩ := exists_quadratic_extension (K := K) hK2
    exact exists_trace_ne_inv_lin_nonsplit hK2 h3 hfin

theorem exists_trace_moved_lin [Finite K] {σ : K ≃+* K} (hσ : σ ≠ 1) (hσσ : σ * σ = 1)
    (hK2 : ringChar K ≠ 2) :
    ∃ g : SL(3, K), (∃ k, g ^ 2 ^ k = 1) ∧
      σ ((g : Matrix (Fin 3) (Fin 3) K).trace) ≠ (g : Matrix (Fin 3) (Fin 3) K).trace ∧
      ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K).trace = (g : Matrix (Fin 3) (Fin 3) K).trace := by
  obtain ⟨q₀, hq₀, hσx⟩ := eq_pow_of_involution hσ hσσ
  have hqodd : Odd (Nat.card K) := odd_card_of_ringChar_ne_two hK2
  have hq₀odd : Odd q₀ := by
    rw [← hq₀] at hqodd
    exact (Nat.odd_mul.1 hqodd).1
  have hq2 : 2 ≤ Nat.card K := Nat.succ_le_of_lt Finite.one_lt_card
  have hq₀3 : 3 ≤ q₀ := by
    have h1 : 2 ≤ q₀ := by
      by_contra hlt
      have : q₀ ≤ 1 := by omega
      have : q₀ * q₀ ≤ 1 := by nlinarith
      omega
    obtain ⟨k, hk⟩ := hq₀odd
    omega
  set q := Nat.card K with hqdef
  set a := padicValNat 2 (q - 1) with hadef
  have hq1 : q - 1 ≠ 0 := by omega
  have ha : 2 ^ a ∣ q - 1 := pow_padicValNat_dvd
  obtain ⟨z, hz⟩ := exists_orderOf_eq_of_dvd (K := K) (d := 2 ^ a) (by rwa [Nat.card_units])
  set ζ : K := (z : K) with hζ
  have hζ0 : ζ ≠ 0 := z.ne_zero
  have hζN : ζ ^ 2 ^ a = 1 := by
    rw [hζ, ← Units.val_pow_eq_pow_val, ← hz, pow_orderOf_eq_one, Units.val_one]
  have hprod : ζ * ζ⁻¹ * 1 = 1 := by field_simp
  have hinv : (diagSL ζ ζ⁻¹ 1 hprod)⁻¹ = diagSL ζ⁻¹ ζ 1 (by field_simp) := by
    apply inv_eq_of_mul_eq_one_right
    rw [diagSL_mul, ← diagSL_one (by ring)]
    exact diagSL_congr (by field_simp) (by field_simp) (by simp)
  refine ⟨diagSL ζ ζ⁻¹ 1 hprod, ⟨a, ?_⟩, ?_, ?_⟩
  · rw [diagSL_pow, ← diagSL_one (by ring)]
    exact diagSL_congr hζN (by rw [inv_pow, hζN, inv_one]) (one_pow _)
  swap
  · rw [hinv, trace_diagSL, trace_diagSL]
    ring
  · rw [trace_diagSL]
    intro h
    rw [map_add, map_add, map_one, map_inv₀, hσx ζ] at h
    have h1 : (ζ ^ q₀ - ζ) * (ζ ^ q₀ * ζ - 1) = 0 := by
      have hne : ζ ^ q₀ ≠ 0 := pow_ne_zero _ hζ0
      field_simp at h
      linear_combination h
    have hqe : q - 1 = (q₀ - 1) * (q₀ + 1) := by
      rw [← hq₀]
      have : 1 ≤ q₀ := by omega
      zify [this, Nat.one_le_iff_ne_zero.2 (by positivity : q₀ * q₀ ≠ 0)]
      ring
    have h2a : ¬ 2 ^ a ∣ q₀ - 1 := by
      intro hd
      have h2 : 2 ∣ q₀ + 1 := by obtain ⟨k, hk⟩ := hq₀odd; exact ⟨k + 1, by omega⟩
      have : 2 ^ (a + 1) ∣ q - 1 := by
        rw [hqe, pow_succ]
        exact Nat.mul_dvd_mul hd h2
      have := (padicValNat_dvd_iff_le hq1).1 this
      omega
    have h2b : ¬ 2 ^ a ∣ q₀ + 1 := by
      intro hd
      have h2 : 2 ∣ q₀ - 1 := by obtain ⟨k, hk⟩ := hq₀odd; exact ⟨k, by omega⟩
      have : 2 ^ (a + 1) ∣ q - 1 := by
        rw [hqe, pow_succ']
        exact Nat.mul_dvd_mul h2 hd
      have := (padicValNat_dvd_iff_le hq1).1 this
      omega
    have hpow1 : ∀ m : ℕ, ζ ^ m = 1 → 2 ^ a ∣ m := fun m hm => by
      rw [← hz]
      exact orderOf_dvd_iff_pow_eq_one.2 (Units.ext (by simpa using hm))
    rcases mul_eq_zero.1 h1 with h3 | h3
    · apply h2a
      have h4 : ζ ^ q₀ = ζ := sub_eq_zero.1 h3
      have h5 : ζ ^ q₀ = ζ ^ (q₀ - 1) * ζ := by
        rw [← pow_succ]; congr 1; omega
      rw [h5] at h4
      exact hpow1 _ ((mul_left_eq_self₀.1 h4).resolve_right hζ0)
    · apply h2b
      apply hpow1
      rw [pow_succ]
      exact sub_eq_zero.1 h3

end LinearAll

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_trace_pow_ne_uni_split (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {i : K}
    (hi : i * i = -1) (hin : i ^ (p ^ f + 1) = 1) :
    ∃ g : SL(3, K), ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (∃ k, g ^ 2 ^ k = 1) ∧
      ((g : Matrix (Fin 3) (Fin 3) K).trace) ^ p ^ f ≠ (g : Matrix (Fin 3) (Fin 3) K).trace := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have h1 : i * i * (-1) = 1 := by rw [hi]; ring
  have hbari : h.bar i * i = 1 := by
    rw [h.bar_apply, ← pow_succ]; exact hin
  have hbarm : h.bar (-1) * (-1) = 1 := by
    rw [h.bar_apply, hodd.neg_one_pow]; ring
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    have := (CharP.cast_eq_zero_iff K p 2).1 this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
  let g : SL(3, K) := diagSL i i (-1) h1
  refine ⟨g, diagSL_unitary h i i (-1) h1 hbari hbari hbarm, ?_, ?_⟩
  · refine ⟨2, ?_⟩
    have hsq : g * g = diagSL (-1) (-1) 1 (by ring) := by
      simp only [g, diagSL_mul]
      exact diagSL_congr hi hi (by simp)
    have h4 : g * g * (g * g) = 1 := by
      rw [hsq, diagSL_mul, ← diagSL_one (by ring)]
      exact diagSL_congr (by simp) (by simp) (by simp)
    have : g ^ 2 ^ 2 = g * g * (g * g) := by
      rw [show (2 : ℕ) ^ 2 = 4 from rfl]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [this]
    exact h4
  · simp only [g, trace_diagSL]
    intro hq
    have hiq : i ^ p ^ f = -i := by
      have h3 : i ^ p ^ f * i = 1 := by rw [← pow_succ]; exact hin
      have : i * i = -1 := hi
      calc i ^ p ^ f = i ^ p ^ f * (i * i) * (-1) := by rw [this]; ring
        _ = (i ^ p ^ f * i) * i * (-1) := by ring
        _ = -i := by rw [h3]; ring
    rw [add_pow_char_pow, add_pow_char_pow, hiq, hodd.neg_one_pow] at hq
    have : (4 : K) * i = 0 := by linear_combination -hq
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2K h2K
    exact mul_ne_zero h4 hi0 this

theorem exists_trace_pow_ne_uni_nonsplit (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hq : p ^ f % 4 = 1) :
    ∃ g : SL(3, K), ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (∃ k, g ^ 2 ^ k = 1) ∧
      ((g : Matrix (Fin 3) (Fin 3) K).trace) ^ p ^ f ≠ (g : Matrix (Fin 3) (Fin 3) K).trace := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Finite K := h.finite
  set q := p ^ f with hqdef
  have hqodd : Odd q := (h.prime.odd_of_ne_two hp2).pow
  have hK : Nat.card K = q ^ 2 := by rw [h.card, hqdef, ← pow_mul, mul_comm]
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
    have := (CharP.cast_eq_zero_iff K p 2).1 this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  set a := padicValNat 2 (q - 1) with hadef
  have hq1 : q - 1 ≠ 0 := by omega
  have ha : 2 ^ a ∣ q - 1 := pow_padicValNat_dvd
  have h4 : 4 ∣ q - 1 := by omega
  have ha2 : 2 ≤ a := (padicValNat_dvd_iff_le hq1).1 (by simpa using h4 : 2 ^ 2 ∣ q - 1)
  have hcardK : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hK]
  obtain ⟨x, hx⟩ := exists_orderOf_eq_of_dvd (K := K) (d := 2 * 2 ^ a)
    (by rw [hcardK]; exact two_mul_pow_dvd_sq_sub_one' hqodd ha)
  set y : K := (x : K) with hy
  have hy0 : y ≠ 0 := x.ne_zero
  have hxN : x ^ (2 * 2 ^ a) = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have h2q : x ^ (2 * (q - 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (hx ▸ Nat.mul_dvd_mul_left 2 ha)
  have hq1' : ¬ x ^ (q - 1) = 1 := by
    intro h1
    have : 2 * 2 ^ a ∣ q - 1 := hx ▸ orderOf_dvd_iff_pow_eq_one.2 h1
    have h3 : 2 ^ (a + 1) ∣ q - 1 := by rwa [pow_succ, mul_comm]
    have := (padicValNat_dvd_iff_le hq1).1 h3
    omega
  have hyq1 : y ^ (q - 1) = -1 := by
    have h1 : y ^ (q - 1) * y ^ (q - 1) = 1 := by
      rw [← pow_add, ← two_mul, hy, ← Units.val_pow_eq_pow_val, h2q, Units.val_one]
    rcases mul_self_eq_one_iff.1 h1 with h | h
    · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h)) hq1'
    · exact h
  have hyq : y ^ q = -y := by
    have : y ^ q = y ^ (q - 1) * y := by
      rw [← pow_succ]; congr 1; omega
    rw [this, hyq1]; ring
  have hy4 : y ^ 4 ≠ 1 := by
    intro h4
    have h1 : x ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h4)
    have h5 : 2 * 2 ^ a ∣ 4 := hx ▸ orderOf_dvd_iff_pow_eq_one.2 h1
    have h6 : 2 ^ a ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2)
      (by simpa using h5 : 2 * 2 ^ a ∣ 2 * 2)
    have h7 := Nat.le_of_dvd (by norm_num) h6
    have h8 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
    omega
  have hy2 : y ^ 2 ≠ 1 := fun h2 => hy4 (by
    have : y ^ 4 = (y ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num)
  have hy2' : y ^ 2 ≠ -1 := fun h2 => hy4 (by
    have : y ^ 4 = (y ^ 2) ^ 2 := by ring
    rw [this, h2]; norm_num)
  have hbary : h.bar y = -y := by rw [h.bar_apply]; exact hyq
  have hbar2 : h.bar 2 = 2 := map_ofNat h.bar 2
  set t : K := y - y⁻¹ with htdef
  have hbart : h.bar t = -t := by
    rw [htdef, map_sub, map_inv₀, hbary, inv_neg]; ring
  have ht0 : t ≠ 0 := by
    intro h0
    apply hy2
    rw [htdef, sub_eq_zero] at h0
    field_simp at h0
    linear_combination h0
  obtain ⟨s, hts⟩ : ∃ s : K, t = 2 * s := ⟨t / 2, by field_simp⟩
  have hbars : h.bar s = -s := by
    have h1 : h.bar (2 * s) = 2 * h.bar s := by rw [map_mul, hbar2]
    have h3 : h.bar (2 * s) = -(2 * s) := by rw [← hts]; exact hbart
    exact mul_left_cancel₀ h2K (by linear_combination -h1 + h3)
  have hss : h.bar (1 + s ^ 2) = 1 + s ^ 2 := by
    rw [map_add, map_one, map_pow, hbars]; ring
  obtain ⟨b, hb⟩ := exists_pow_eq_of_pow_eq (K := K) (q := q) (by omega) hK (y := 1 + s ^ 2) (by
    have := hss
    rwa [h.bar_apply] at this)
  have hbb : h.bar b * b = 1 + s ^ 2 := by rw [h.bar_apply, ← pow_succ]; exact hb
  let U : Matrix (Fin 2) (Fin 2) K := !![s, b; h.bar b, s]
  have hUh : (U.map h.bar)ᵀ * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, Matrix.mul_apply, Fin.sum_univ_two, h.bar_bar, hbars] <;>
      first | ring1 | linear_combination hbb
  have hUtr : U.trace = t := by
    simp only [U, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hts]; ring
  have hUdet : U.det = -1 := by
    simp only [U, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination -hbb
  have hcp : U.charpoly = (X - C y) * (X - C (-y⁻¹)) := by
    rw [Matrix.charpoly_fin_two, hUtr, hUdet]
    have e1 : C y + C (-y⁻¹) = C t := by
      rw [← C_add, htdef]; congr 1; ring
    have e2 : C y * C (-y⁻¹) = C (-1 : K) := by
      rw [← C_mul]; congr 1; field_simp
    have : (X - C y) * (X - C (-y⁻¹)) = X ^ 2 - (C y + C (-y⁻¹)) * X + C y * C (-y⁻¹) := by ring
    rw [this, e1, e2]
  have hyN : y ^ (2 * 2 ^ a) = 1 := by
    rw [hy, ← Units.val_pow_eq_pow_val, hxN, Units.val_one]
  have hevenN : Even (2 * 2 ^ a) := ⟨2 ^ a, by ring⟩
  have hd1 : (X - C y) ∣ (X ^ (2 * 2 ^ a) - 1 : K[X]) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot, hyN]
  have hd2 : (X - C (-y⁻¹)) ∣ (X ^ (2 * 2 ^ a) - 1 : K[X]) := by
    rw [dvd_iff_isRoot]
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_one]
    rw [hevenN.neg_pow y⁻¹, inv_pow, hyN]; simp
  have hne : y + y⁻¹ ≠ 0 := by
    intro h0
    apply hy2'
    field_simp at h0
    linear_combination h0
  have hcop : IsCoprime (X - C y) (X - C (-y⁻¹) : K[X]) := by
    apply isCoprime_X_sub_C_of_isUnit_sub
    rw [sub_neg_eq_add]
    exact (isUnit_iff_ne_zero.2 hne)
  obtain ⟨Q, hQ⟩ := hcop.mul_dvd hd1 hd2
  have hUN : U ^ (2 * 2 ^ a) = 1 := by
    have h1 := congrArg (Polynomial.aeval U) hQ
    rw [← hcp] at h1
    simp only [map_sub, map_pow, aeval_X, map_one, map_mul, Matrix.aeval_self_charpoly,
      zero_mul] at h1
    exact sub_eq_zero.1 h1
  have hdetg : (blk U (-1)).det = 1 := by rw [det_blk, hUdet]; ring
  let g : SL(3, K) := ⟨blk U (-1), hdetg⟩
  refine ⟨g, ?_, ⟨a + 1, ?_⟩, ?_⟩
  · change ((blk U (-1)).map h.bar)ᵀ * blk U (-1) = 1
    rw [blk_map, blk_transpose, blk_mul, hUh, map_neg, map_one, ← blk_one]
    congr 1; ring
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow]
    change blk U (-1) ^ 2 ^ (a + 1) = 1
    have hpow : 2 ^ (a + 1) = 2 * 2 ^ a := by ring
    have hc : (-1 : K) ^ (2 * 2 ^ a) = 1 := Even.neg_one_pow hevenN
    rw [blk_pow, hpow, hUN, hc, blk_one]
  · change ((blk U (-1)).trace) ^ p ^ f ≠ (blk U (-1)).trace
    rw [trace_blk, hUtr, ← h.bar_apply, map_add, map_neg, map_one, hbart]
    intro h0
    have : 2 * t = 0 := by linear_combination -h0
    exact mul_ne_zero h2K ht0 this

theorem exists_trace_pow_ne_uni (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) :
    ∃ g : SL(3, K), ((g : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ *
        (g : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      (∃ k, g ^ 2 ^ k = 1) ∧
      ((g : Matrix (Fin 3) (Fin 3) K).trace) ^ p ^ f ≠ (g : Matrix (Fin 3) (Fin 3) K).trace := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hqodd : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have h13 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    rcases hqodd with ⟨k, hk⟩
    omega
  rcases h13 with h1 | h3
  · exact exists_trace_pow_ne_uni_nonsplit h hp2 h5 h1
  ·
    have hK : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
    have hcardK : Nat.card Kˣ = (p ^ f) ^ 2 - 1 := by rw [Nat.card_units, hK]
    have h4 : 4 ∣ (p ^ f) ^ 2 - 1 := by
      have : 4 ∣ (p ^ f + 1) := by omega
      have h6 : (p ^ f) ^ 2 - 1 = (p ^ f + 1) * (p ^ f - 1) := by
        have h1 : 1 ≤ p ^ f := by omega
        zify [h1, Nat.one_le_pow 2 _ h1]
        ring
      rw [h6]
      exact Dvd.dvd.mul_right this _
    obtain ⟨x, hx⟩ := exists_orderOf_eq_of_dvd (K := K) (d := 4) (by rw [hcardK]; exact h4)
    set i : K := (x : K) with hi
    have hx4 : x ^ 4 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hx2 : x ^ 2 ≠ 1 := by
      intro h2
      have : 4 ∣ 2 := hx ▸ orderOf_dvd_iff_pow_eq_one.2 h2
      omega
    have hii : i * i = -1 := by
      have h1 : (i * i) * (i * i) = 1 := by
        have : (i * i) * (i * i) = i ^ 4 := by ring
        rw [this, hi, ← Units.val_pow_eq_pow_val, hx4, Units.val_one]
      rcases mul_self_eq_one_iff.1 h1 with h | h
      · exact absurd (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, sq]; exact h)) hx2
      · exact h
    have hin : i ^ (p ^ f + 1) = 1 := by
      obtain ⟨m, hm⟩ : 4 ∣ p ^ f + 1 := by omega
      rw [hm, pow_mul, hi, ← Units.val_pow_eq_pow_val, hx4, Units.val_one, one_pow]
    exact exists_trace_pow_ne_uni_split h hp2 hii hin

end Unitary

end CFSG.GH74.KGroups.L3Eps
