module

public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.Assembly.Defs
public import CFSG.LinearAlgebra.LinearGroups.Elementary

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace MatrixExtension

open Matrix
open scoped commutatorElement

section Four

variable {K : Type*} [Field K]

theorem four_pow_four (hK : Nat.card K = 4) (a : K) : a ^ 4 = a := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem four_pow_three (hK : Nat.card K = 4) {a : K} (ha : a ≠ 0) : a ^ 3 = 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem four_charP (hK : Nat.card K = 4) : CharP K 2 :=
  finite_field_prime_power_characteristic Nat.prime_two (k := 2) (by norm_num) hK

variable [CharP K 2]

theorem four_add_self (a : K) : a + a = 0 :=
  CharTwo.add_self_eq_zero a

theorem four_neg (a : K) : -a = a :=
  CharTwo.neg_eq a

theorem four_sq_add (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 :=
  CharTwo.add_sq a b

omit [CharP K 2] in
theorem four_exists_omega (hK : Nat.card K = 4) : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, -, hω⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset K)) (t := Finset.univ) (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
      exact (Finset.card_le_two).trans_lt (by norm_num))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hω
  exact ⟨ω, hω.1, hω.2⟩

theorem four_omega_sq (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    ω ^ 2 = ω + 1 := by
  have h3 := four_pow_three hK h0
  have h : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd (sub_eq_zero.mp h') h1
  · linear_combination h' - four_add_self ω - four_add_self (1 : K)

theorem four_cases (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) (t : K) :
    t = 0 ∨ t = 1 ∨ t = ω ∨ t = ω + 1 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have hne : (ω + 1 : K) ≠ 0 := fun h => h1 (by
    have h' := eq_neg_of_add_eq_zero_left h
    rwa [four_neg] at h')
  have hne' : (ω + 1 : K) ≠ 1 := fun h => h0 (by simpa using h)
  have hne'' : (ω + 1 : K) ≠ ω := fun h => by simp at h
  have hcard : ({0, 1, ω, ω + 1} : Finset K).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hne''.symm]
    · simp [Ne.symm h1, Ne.symm hne']
    · simp [Ne.symm h0, Ne.symm hne, zero_ne_one]
  have huniv : ({0, 1, ω, ω + 1} : Finset K) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hcard, ← Nat.card_eq_fintype_card, hK])
  have ht : t ∈ ({0, 1, ω, ω + 1} : Finset K) := huniv ▸ Finset.mem_univ t
  simpa using ht

end Four

section Congruence

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

@[expose] def hconj (B : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  (B.map (· ^ 2))ᵀ

theorem hconj_mul (A B : Matrix (Fin r) (Fin r) K) : hconj (A * B) = hconj B * hconj A := by
  unfold hconj
  rw [show (A * B).map (· ^ 2) = A.map (· ^ 2) * B.map (· ^ 2) from
    Matrix.map_mul (f := frobenius K 2), transpose_mul]

omit [CharP K 2] in
theorem mul_vecMulVec_mul_transpose' (A B : Matrix (Fin r) (Fin r) K) (u v : Fin r → K) :
    A * vecMulVec u v * Bᵀ = vecMulVec (A *ᵥ u) (B *ᵥ v) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, transpose_apply, mulVec, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem map_sq_mulVec_sq (g : Matrix (Fin r) (Fin r) K) (y : Fin r → K) :
    g.map (· ^ 2) *ᵥ (fun i => y i ^ 2) = (fun i => (g *ᵥ y) i ^ 2) := by
  funext i
  simp only [mulVec, dotProduct, Matrix.map_apply]
  have := map_sum (frobenius K 2) (fun x => g i x * y x) Finset.univ
  simp only [frobenius_def, mul_pow] at this
  exact this.symm

theorem mul_vecMulVec_hconj (g : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    g * vecMulVec x (fun i => y i ^ 2) * hconj g =
      vecMulVec (g *ᵥ x) (fun i => (g *ᵥ y) i ^ 2) := by
  rw [hconj, mul_vecMulVec_mul_transpose', map_sq_mulVec_sq]

@[expose] def hermH (x y : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  vecMulVec x (fun i => y i ^ 2) + vecMulVec y (fun i => x i ^ 2)

@[expose] def hermQ (x : Fin r → K) : Matrix (Fin r) (Fin r) K :=
  vecMulVec x (fun i => x i ^ 2)

theorem mul_hermH_hconj (g : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    g * hermH x y * hconj g = hermH (g *ᵥ x) (g *ᵥ y) := by
  rw [hermH, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec_hconj, mul_vecMulVec_hconj]
  rfl

theorem mul_hermQ_hconj (g : Matrix (Fin r) (Fin r) K) (x : Fin r → K) :
    g * hermQ x * hconj g = hermQ (g *ᵥ x) := by
  rw [hermQ, mul_vecMulVec_hconj]
  rfl

theorem sq_add_fun (x y : Fin r → K) :
    (fun i => (x + y) i ^ 2) = (fun i => x i ^ 2) + fun i => y i ^ 2 := by
  funext i
  exact four_sq_add (x i) (y i)

theorem hermH_add_left (x x' y : Fin r → K) : hermH (x + x') y = hermH x y + hermH x' y := by
  simp only [hermH, add_vecMulVec, sq_add_fun, vecMulVec_add]
  abel

theorem hermH_add_right (x y y' : Fin r → K) : hermH x (y + y') = hermH x y + hermH x y' := by
  simp only [hermH, add_vecMulVec, sq_add_fun, vecMulVec_add]
  abel

theorem hermQ_add (x y : Fin r → K) : hermQ (x + y) = hermQ x + hermQ y + hermH x y := by
  simp only [hermQ, hermH, add_vecMulVec, sq_add_fun, vecMulVec_add]
  abel

omit [CharP K 2] in
omit [CharP K 2] in
theorem hermH_zero_right (x : Fin r → K) : hermH x 0 = 0 := by
  rw [hermH, show (fun i => (0 : Fin r → K) i ^ 2) = 0 from funext fun i => by simp,
    vecMulVec_zero, zero_vecMulVec, add_zero]

omit [CharP K 2] in
theorem hermH_zero_left (y : Fin r → K) : hermH 0 y = 0 := by
  rw [hermH, show (fun i => (0 : Fin r → K) i ^ 2) = 0 from funext fun i => by simp,
    vecMulVec_zero, zero_vecMulVec, add_zero]

omit [CharP K 2] in
theorem vecMulVec_single_single' (i j : Fin r) (a b : K) :
    vecMulVec (Pi.single i a) (Pi.single j b) = single i j (a * b) := by
  ext k l
  simp only [vecMulVec_apply, Pi.single_apply, single_apply]
  split_ifs <;> simp_all

omit [CharP K 2] in
theorem sq_single_fun (j : Fin r) (c : K) :
    (fun i => (Pi.single j c : Fin r → K) i ^ 2) = Pi.single j (c ^ 2) := by
  funext i
  simp only [Pi.single_apply]
  split_ifs <;> simp

omit [CharP K 2] in
theorem hermH_single (i j : Fin r) (w c : K) :
    hermH (Pi.single i w) (Pi.single j c) = single i j (w * c ^ 2) + single j i (c * w ^ 2) := by
  rw [hermH, sq_single_fun, sq_single_fun, vecMulVec_single_single', vecMulVec_single_single']

omit [CharP K 2] in
theorem hermQ_single (k : Fin r) (c : K) : hermQ (Pi.single k c) = single k k (c ^ 3) := by
  rw [hermQ, sq_single_fun, vecMulVec_single_single']
  congr 1
  ring

@[expose] def hermO (i j : Fin r) (u : K) : Matrix (Fin r) (Fin r) K :=
  single i j u + single j i (u ^ 2)

@[expose] def hermD (k : Fin r) : Matrix (Fin r) (Fin r) K :=
  single k k 1

theorem hermO_add (i j : Fin r) (u v : K) : hermO i j (u + v) = hermO i j u + hermO i j v := by
  simp only [hermO, four_sq_add, single_add]
  abel

omit [CharP K 2] in
theorem hermO_zero (i j : Fin r) : hermO i j (0 : K) = 0 := by
  simp [hermO]

omit [CharP K 2] in
theorem hermO_eq_hermH (i j : Fin r) (u : K) :
    hermO i j u = hermH (Pi.single i u) (Pi.single j 1) := by
  rw [hermH_single, one_pow, mul_one, one_mul, hermO]

omit [CharP K 2] in
theorem hermD_eq_hermQ (k : Fin r) : hermD k = hermQ (Pi.single k (1 : K)) := by
  rw [hermQ_single, one_pow, hermD]

omit [CharP K 2] in
theorem hermO_swap (hK : Nat.card K = 4) (i j : Fin r) (u : K) :
    hermO j i u = hermO i j (u ^ 2) := by
  rw [hermO, hermO, ← pow_mul, show 2 * 2 = 4 from rfl, four_pow_four hK, add_comm]

theorem hconj_add (A B : Matrix (Fin r) (Fin r) K) : hconj (A + B) = hconj A + hconj B := by
  ext k l
  simp only [hconj, transpose_apply, Matrix.map_apply, Matrix.add_apply, four_sq_add]

omit [CharP K 2] in
theorem hconj_single (i j : Fin r) (u : K) : hconj (single i j u) = single j i (u ^ 2) := by
  ext k l
  simp only [hconj, transpose_apply, Matrix.map_apply, single_apply]
  by_cases h : i = l ∧ j = k
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2, h'.1⟩]
    ring

theorem hconj_hermO (hK : Nat.card K = 4) (i j : Fin r) (u : K) :
    hconj (hermO i j u) = hermO i j u := by
  rw [hermO, hconj_add, hconj_single, hconj_single, ← pow_mul, show 2 * 2 = 4 from rfl,
    four_pow_four hK, add_comm]

omit [CharP K 2] in
theorem hconj_hermD (k : Fin r) : hconj (hermD k : Matrix (Fin r) (Fin r) K) = hermD k := by
  rw [hermD, hconj_single, one_pow]

end Congruence

section Elementary

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

@[expose] def hElem (a b : Fin r) (t : K) : Matrix (Fin r) (Fin r) K :=
  1 + single a b t

omit [CharP K 2] in
theorem hElem_mulVec (a b : Fin r) (t : K) (v : Fin r → K) :
    hElem a b t *ᵥ v = v + Pi.single a (t * v b) := by
  rw [hElem, add_mulVec, one_mulVec, single_mulVec]
  rfl

omit [CharP K 2] in
theorem hElem_mul {a b : Fin r} (hab : a ≠ b) (t u : K) :
    hElem a b t * hElem a b u = hElem a b (t + u) :=
  transvection_mul_transvection_same a b hab t u

omit [CharP K 2] in
theorem hElem_zero (a b : Fin r) : hElem a b (0 : K) = 1 := by
  rw [hElem, single_zero, add_zero]

theorem hElem_mul_self {a b : Fin r} (hab : a ≠ b) (t : K) : hElem a b t * hElem a b t = 1 := by
  rw [hElem_mul hab, four_add_self, hElem_zero]

theorem hElem_congr_hermO (hK : Nat.card K = 4) (a b : Fin r) (t u : K) {i j : Fin r}
    (hij : i ≠ j) :
    hElem a b t * hermO i j u * hconj (hElem a b t) = hermO i j u +
      (if i = b then hermO a j (t * u) else 0) + (if j = b then hermO i a (u * t ^ 2) else 0) := by
  rw [hermO_eq_hermH, mul_hermH_hconj, hElem_mulVec, hElem_mulVec]
  by_cases hi : i = b
  · subst hi
    have hj : j ≠ i := Ne.symm hij
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hij, mul_zero, Pi.single_zero, add_zero,
      hermH_add_left, ↓reduceIte, ite_eq_right hj]
    rw [← hermO_eq_hermH, ← hermO_eq_hermH]
  · by_cases hj : j = b
    · subst hj
      simp only [Pi.single_eq_of_ne hij.symm, Pi.single_eq_same, mul_zero, mul_one,
        Pi.single_zero, add_zero, hermH_add_right, ite_eq_right hi, ↓reduceIte]
      rw [← hermO_eq_hermH, hermH_single]
      simp only [hermO]
      rw [mul_pow, ← pow_mul, show 2 * 2 = 4 from rfl, four_pow_four hK, mul_comm (u ^ 2) t]
    · simp only [Pi.single_eq_of_ne (Ne.symm hi), Pi.single_eq_of_ne (Ne.symm hj), mul_zero,
        Pi.single_zero, add_zero, ite_eq_right hi, ite_eq_right hj]

theorem hElem_congr_hermD (a b : Fin r) (t : K) (k : Fin r) :
    hElem a b t * hermD k * hconj (hElem a b t) =
      hermD k + if k = b then hermO a k t + single a a (t ^ 3) else 0 := by
  rw [hermD_eq_hermQ, mul_hermQ_hconj, hElem_mulVec, hermQ_add, ← hermD_eq_hermQ, hermQ_single]
  by_cases hk : k = b
  · subst hk
    rw [Pi.single_eq_same, mul_one, ite_eq_left rfl, hermH_single, hermO, one_pow, one_mul,
      mul_one]
    abel
  · simp only [Pi.single_eq_of_ne (Ne.symm hk), mul_zero, ite_eq_right hk, Pi.single_zero,
      hermH_zero_right, add_zero]
    rw [show (0 : K) ^ 3 = 0 by ring, single_zero, add_zero]

omit [CharP K 2] in
theorem diagonal_mul_single' (d : Fin r → K) (a b : Fin r) (t : K) :
    diagonal d * single a b t = single a b (d a * t) := by
  ext k l
  rw [diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · rw [h.1]
  · rw [mul_zero]

omit [CharP K 2] in
theorem single_mul_diagonal' (d : Fin r → K) (a b : Fin r) (t : K) :
    single a b t * diagonal d = single a b (t * d b) := by
  ext k l
  rw [mul_diagonal, single_apply, single_apply]
  split_ifs with h
  · rw [h.2]
  · rw [zero_mul]

omit [CharP K 2] in
theorem diagonal_mul_hElem (d : Fin r → K) {a b : Fin r} (hb : d b ≠ 0) (t : K) :
    diagonal d * hElem a b t = hElem a b (d a * t * (d b)⁻¹) * diagonal d := by
  rw [hElem, hElem, Matrix.mul_add, Matrix.add_mul, mul_one, one_mul, diagonal_mul_single',
    single_mul_diagonal', inv_mul_cancel_right₀ hb]

theorem diagonal_congr_hermO (hK : Nat.card K = 4) (d : Fin r → K) (i j : Fin r) (u : K) :
    diagonal d * hermO i j u * hconj (diagonal d) = hermO i j (d i * d j ^ 2 * u) := by
  rw [hermO_eq_hermH, mul_hermH_hconj, diagonal_mulVec_single, diagonal_mulVec_single,
    hermH_single, hermO, mul_one]
  congr 2
  · ring
  · linear_combination (-(d i ^ 2 * u ^ 2)) * four_pow_four hK (d j)

theorem diagonal_congr_hermD (d : Fin r → K) (k : Fin r) (hk : d k ^ 3 = 1) :
    diagonal d * hermD k * hconj (diagonal d) = hermD k := by
  rw [hermD_eq_hermQ, mul_hermQ_hconj, diagonal_mulVec_single, hermQ_single, hermQ_single,
    mul_one, hk, one_pow]

end Elementary

section GeneralLinear

variable {K : Type*} [Field K] [CharP K 2] {r : ℕ}

omit [CharP K 2] in
theorem hElem_eq_transvection (a b : Fin r) (t : K) : hElem a b t = transvection a b t :=
  rfl

@[expose] def hElemGL {a b : Fin r} (h : a ≠ b) (t : K) : GL (Fin r) K :=
  ⟨hElem a b t, hElem a b (-t), by rw [hElem_mul h, add_neg_cancel, hElem_zero],
    by rw [hElem_mul h, neg_add_cancel, hElem_zero]⟩

omit [CharP K 2] in
@[simp] theorem hElemGL_coe {a b : Fin r} (h : a ≠ b) (t : K) :
    (hElemGL h t : Matrix (Fin r) (Fin r) K) = hElem a b t :=
  rfl

omit [CharP K 2] in
theorem hElemGL_det {a b : Fin r} (h : a ≠ b) (t : K) :
    (hElemGL h t : Matrix (Fin r) (Fin r) K).det = 1 :=
  det_transvection_of_ne a b h t

omit [CharP K 2] in
theorem hElemGL_mul {a b : Fin r} (h : a ≠ b) (t u : K) :
    hElemGL h t * hElemGL h u = hElemGL h (t + u) :=
  Units.ext (hElem_mul h t u)

omit [CharP K 2] in
theorem hElemGL_zero {a b : Fin r} (h : a ≠ b) : hElemGL h (0 : K) = 1 :=
  Units.ext (hElem_zero a b)

theorem hElemGL_inv {a b : Fin r} (h : a ≠ b) (t : K) : (hElemGL h t)⁻¹ = hElemGL h t := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [hElemGL_mul, four_add_self, hElemGL_zero]

omit [CharP K 2] in
theorem commutatorElement_hElemGL {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (s t : K) : ⁅hElemGL hab s, hElemGL hbc t⁆ = hElemGL hac (s * t) := by
  apply Units.ext
  rw [commutatorElement_def]
  simp only [Units.val_mul, Matrix.coe_units_inv, hElemGL_coe, hElem]
  exact CFSG.LinearGroups.elementary_three_index_commutator hac hab hbc.symm s t

@[expose] def hTorusGL (d : Fin r → Kˣ) : GL (Fin r) K :=
  ⟨diagonal fun i => (d i : K), diagonal fun i => ((d i)⁻¹ : Kˣ), by
    rw [diagonal_mul_diagonal]
    simp, by
    rw [diagonal_mul_diagonal]
    simp⟩

omit [CharP K 2] in
@[simp] theorem hTorusGL_coe (d : Fin r → Kˣ) :
    (hTorusGL d : Matrix (Fin r) (Fin r) K) = diagonal fun i => (d i : K) :=
  rfl

omit [CharP K 2] in
theorem hTorusGL_det (d : Fin r → Kˣ) :
    (hTorusGL d : Matrix (Fin r) (Fin r) K).det = ∏ i, (d i : K) := by
  rw [hTorusGL_coe, det_diagonal]

omit [CharP K 2] in
theorem hTorusGL_mul_hElemGL (d : Fin r → Kˣ) {a b : Fin r} (h : a ≠ b) (t : K) :
    hTorusGL d * hElemGL h t = hElemGL h ((d a : K) * t * ((d b : K))⁻¹) * hTorusGL d :=
  Units.ext (diagonal_mul_hElem _ (d b).ne_zero t)

omit [CharP K 2] in
theorem hTorusGL_comm (d e : Fin r → Kˣ) : hTorusGL d * hTorusGL e = hTorusGL e * hTorusGL d :=
  Units.ext (by
    simp only [Units.val_mul, hTorusGL_coe, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _)

omit [CharP K 2] in
theorem hTorusGL_pow_three (hK : Nat.card K = 4) (d : Fin r → Kˣ) : hTorusGL d ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hTorusGL_coe, diagonal_pow, Units.val_one, ← diagonal_one]
  congr 1
  funext i
  exact four_pow_three hK (d i).ne_zero

end GeneralLinear

section TwoPoint

variable {K : Type*} [Field K] {r : ℕ}

@[expose] def twoPoint (a b : Fin r) (u v : Kˣ) : Fin r → Kˣ :=
  fun i => if i = a then u else if i = b then v else 1

theorem twoPoint_apply_left (a b : Fin r) (u v : Kˣ) : twoPoint a b u v a = u := by
  simp [twoPoint]

theorem twoPoint_apply_right {a b : Fin r} (hab : a ≠ b) (u v : Kˣ) : twoPoint a b u v b = v := by
  simp [twoPoint, Ne.symm hab]

theorem twoPoint_apply_of_ne {a b i : Fin r} (hia : i ≠ a) (hib : i ≠ b) (u v : Kˣ) :
    twoPoint a b u v i = 1 := by
  simp [twoPoint, hia, hib]

theorem prod_twoPoint {a b : Fin r} (hab : a ≠ b) (u v : Kˣ) :
    ∏ i, (twoPoint a b u v i : K) = (u : K) * v := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), twoPoint_apply_left,
    ← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩),
    twoPoint_apply_right hab, Finset.prod_eq_one fun i hi => by
      rw [Finset.mem_erase, Finset.mem_erase] at hi
      rw [twoPoint_apply_of_ne hi.2.1 hi.1, Units.val_one], mul_one]

end TwoPoint

section Trace

variable {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]

omit [CharP K 2] in
theorem four_finrank (hK : Nat.card K = 4) : Module.finrank (ZMod 2) K = 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [hK, Nat.card_zmod, show (4 : ℕ) = 2 ^ 2 from rfl] at h
  exact (Nat.pow_right_injective le_rfl h).symm

omit [CharP K 2] in
theorem four_algebraMap_trace (hK : Nat.card K = 4) (u : K) :
    algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K u) = u + u ^ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  rw [FiniteField.algebraMap_trace_eq_sum_pow, four_finrank hK, Nat.card_zmod]
  simp [Finset.sum_range_succ]

theorem four_coord (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) (u : K) :
    u = algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K (ω ^ 2 * u)) +
      algebraMap (ZMod 2) K (Algebra.trace (ZMod 2) K u) * ω := by
  rw [four_algebraMap_trace hK, four_algebraMap_trace hK]
  have hω2 := four_omega_sq hK h0 h1
  have hω4 := four_pow_four hK ω
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (-u) * hω2 + (-u ^ 2) * hω4 + (-(ω * u + ω * u ^ 2)) * h2

theorem four_trace_one (hK : Nat.card K = 4) : Algebra.trace (ZMod 2) K 1 = 0 :=
  (algebraMap (ZMod 2) K).injective (by
    rw [four_algebraMap_trace hK, map_zero, one_pow, four_add_self])

theorem four_trace_omega (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    Algebra.trace (ZMod 2) K ω = 1 :=
  (algebraMap (ZMod 2) K).injective (by
    rw [four_algebraMap_trace hK, map_one, four_omega_sq hK h0 h1, ← add_assoc, four_add_self,
      zero_add])

theorem four_trace_omega_sq (hK : Nat.card K = 4) {ω : K} (h0 : ω ≠ 0) (h1 : ω ≠ 1) :
    Algebra.trace (ZMod 2) K (ω ^ 2) = 1 :=
  (algebraMap (ZMod 2) K).injective (by
    rw [four_algebraMap_trace hK, map_one, ← pow_mul, show 2 * 2 = 4 from rfl,
      four_pow_four hK, four_omega_sq hK h0 h1, add_comm, ← add_assoc, four_add_self,
      zero_add])

end Trace

end MatrixExtension

end CFSG.LocalAnalysis.ComponentInitial
