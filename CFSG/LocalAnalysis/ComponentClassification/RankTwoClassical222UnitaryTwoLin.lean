module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryPair

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix

section Torus

variable {K : Type} [Field K] {ℓ r : ℕ}

@[expose] def adaptedTorus (a : Fin ℓ → K) (b : Fin r → K) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  Matrix.diagonal (Sum.elim a (Sum.elim a b))

theorem adaptedTorus_commute (a : Fin ℓ → K) (b : Fin r → K) :
    Commute (adaptedTorus a b) (sqZeroStd ℓ r) := by
  show adaptedTorus a b * sqZeroStd ℓ r = sqZeroStd ℓ r * adaptedTorus a b
  ext m m'
  simp only [adaptedTorus, Matrix.diagonal_mul, Matrix.mul_diagonal, sqZeroStd_apply]
  rcases m' with c | c | k
  · simp only [Sum.elim_inl]
    split_ifs with h
    · subst h
      simp
    · simp
  · simp
  · simp

theorem adaptedTorus_mul_adaptedTorus (a a' : Fin ℓ → K) (b b' : Fin r → K) :
    adaptedTorus a b * adaptedTorus a' b' = adaptedTorus (a * a') (b * b') := by
  rw [adaptedTorus, adaptedTorus, adaptedTorus, Matrix.diagonal_mul_diagonal]
  congr 1
  ext m
  rcases m with i | i | k <;> rfl

theorem adaptedTorus_one : adaptedTorus (1 : Fin ℓ → K) (1 : Fin r → K) = 1 := by
  rw [adaptedTorus, ← Matrix.diagonal_one]
  congr 1
  ext m
  rcases m with i | i | k <;> rfl

theorem det_adaptedTorus (a : Fin ℓ → K) (b : Fin r → K) :
    (adaptedTorus a b).det = (∏ i, a i) ^ 2 * ∏ k, b k := by
  rw [adaptedTorus, Matrix.det_diagonal, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem adaptedTorus_mul_single (a : Fin ℓ → K) (b : Fin r → K) (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
    (c : K) :
    adaptedTorus a b * Matrix.single p q c = Sum.elim a (Sum.elim a b) p • Matrix.single p q c := by
  ext m m'
  simp only [adaptedTorus, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.1]
  · simp

theorem single_mul_adaptedTorus (a : Fin ℓ → K) (b : Fin r → K) (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
    (c : K) :
    Matrix.single p q c * adaptedTorus a b = Sum.elim a (Sum.elim a b) q • Matrix.single p q c := by
  ext m m'
  simp only [adaptedTorus, Matrix.mul_diagonal, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.2, mul_comm]
  · simp

variable (σ : K →+* K)

theorem adjM_adaptedTorus (a : Fin ℓ → K) (b : Fin r → K) :
    adjM σ (adaptedTorus a b) = adaptedTorus (fun i => σ (a i)) (fun k => σ (b k)) := by
  ext m m'
  simp only [adjM, adaptedTorus, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rcases m with i | i | k <;> rcases m' with j | j | k' <;> simp [eq_comm] <;>
    split_ifs with h <;> simp [h]

theorem adjM_adaptedTorus_mul_unitGram {a : Fin ℓ → K} {b : Fin r → K}
    (ha : ∀ i, σ (a i) * a i = 1) (hb : ∀ k, σ (b k) * b k = 1) :
    adjM σ (adaptedTorus a b) * unitGram K ℓ r * adaptedTorus a b = unitGram K ℓ r := by
  rw [adjM_adaptedTorus]
  ext p q
  simp only [adaptedTorus, Matrix.diagonal_mul, Matrix.mul_diagonal, unitGram, Matrix.of_apply]
  split_ifs with h
  · subst h
    rcases p with i | i | k
    · simpa [swapXW] using ha i
    · simpa [swapXW] using ha i
    · simpa [swapXW] using hb k
  · simp

end Torus

section Conj

variable {K : Type} [Field K] {σ : K →+* K} {ℓ r : ℕ}

theorem adjM_mul_unitGram_mul {X Y : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hX : adjM σ X * unitGram K ℓ r * X = unitGram K ℓ r)
    (hY : adjM σ Y * unitGram K ℓ r * Y = unitGram K ℓ r) :
    adjM σ (X * Y) * unitGram K ℓ r * (X * Y) = unitGram K ℓ r := by
  rw [adjM_mul]
  calc adjM σ Y * adjM σ X * unitGram K ℓ r * (X * Y) =
      adjM σ Y * (adjM σ X * unitGram K ℓ r * X) * Y := by simp only [Matrix.mul_assoc]
    _ = unitGram K ℓ r := by rw [hX, hY]

theorem commute_conj_mul {ι : Type} [Fintype ι] [DecidableEq ι] {V X X' D D' : Matrix ι ι K}
    (hVD' : Commute V D') (hV : Commute V (X * D * X')) : Commute V (X * (D * X' * D')) := by
  have h := hV.mul_right hVD'
  rwa [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc D] at h

end Conj

section Cube

variable {K : Type} [Field K] [CharP K 2] {ω : K}

omit [CharP K 2] in
theorem cube_eq_one_of_cube_root (hω : ω * ω + ω + 1 = 0) : ω * ω * ω = 1 := by
  linear_combination (ω - 1) * hω

theorem commute_of_cube_root {ι : Type} [Fintype ι] [DecidableEq ι] (hω : ω * ω + ω + 1 = 0)
    {V E E' : Matrix ι ι K} (h1 : Commute V (ω • E + (ω * ω) • E'))
    (h2 : Commute V ((ω * ω) • E + ω • E')) : Commute V E ∧ Commute V E' := by
  have h3 := cube_eq_one_of_cube_root hω
  have hE : Commute V E := by
    refine commute_of_eq ((h1.smul_right ω).add_right (h2.smul_right (ω * ω))) ?_
    have c1 : ω * ω + ω * ω * (ω * ω) = 1 := by
      linear_combination (1 + ω * ω - ω) * hω - CharTwo.two_eq_zero (R := K)
    have c2 : ω * (ω * ω) + ω * ω * ω = 0 := by
      linear_combination ω * ω * ω * CharTwo.two_eq_zero (R := K)
    calc ω • (ω • E + (ω * ω) • E') + (ω * ω) • ((ω * ω) • E + ω • E') =
        (ω * ω + ω * ω * (ω * ω)) • E + (ω * (ω * ω) + ω * ω * ω) • E' := by module
      _ = E := by rw [c1, c2, one_smul, zero_smul, add_zero]
  refine ⟨hE, ?_⟩
  refine commute_of_smul_ne_zero (c := ω * ω) ?_ (commute_of_eq (h1.sub_right (hE.smul_right ω))
    (by module))
  intro h0
  rw [mul_self_eq_zero.mp h0] at hω
  simp at hω

end Cube

section RootW

variable {K : Type} [Field K] {σ : K →+* K} {ℓ r : ℕ} {ω : K}

@[expose] def omegaPair (ω : K) (i j : Fin ℓ) : Fin ℓ → K :=
  fun m => (if m = i then ω else 1) * (if m = j then ω * ω else 1)

theorem prod_omegaPair (ω : K) (i j : Fin ℓ) : ∏ m, omegaPair ω i j m = ω * (ω * ω) := by
  simp only [omegaPair, Finset.prod_mul_distrib, Fintype.prod_ite_eq']

theorem omegaPair_mul (ω : K) (hω : ω * ω * ω = 1) {i j : Fin ℓ} (hij : i ≠ j) :
    omegaPair ω i j * omegaPair ω j i = 1 := by
  ext m
  simp only [omegaPair, Pi.mul_apply, Pi.one_apply]
  by_cases hi : m = i
  · subst hi
    simp [hij]
    linear_combination hω
  · by_cases hj : m = j
    · subst hj
      simp [hi]
      linear_combination hω
    · simp [hi, hj]

theorem omegaPair_apply_left (ω : K) {i j : Fin ℓ} (hij : i ≠ j) : omegaPair ω i j i = ω := by
  simp [omegaPair, hij]

theorem omegaPair_apply_right (ω : K) {i j : Fin ℓ} (hij : i ≠ j) :
    omegaPair ω i j j = ω * ω := by
  simp [omegaPair, Ne.symm hij]

theorem omegaPair_cube (ω : K) (hω : ω * ω * ω = 1) (i j : Fin ℓ) :
    omegaPair ω i j * omegaPair ω i j * omegaPair ω i j = 1 := by
  ext m
  simp only [omegaPair, Pi.mul_apply, Pi.one_apply]
  split_ifs <;> first
    | linear_combination hω
    | linear_combination (ω * ω * ω + 1) * hω
    | linear_combination (ω * ω * ω * ω * ω * ω + ω * ω * ω + 1) * hω
    | simp

theorem omegaPair_props (hσω : σ ω = ω * ω) (hω : ω * ω + ω + 1 = 0) (i j : Fin ℓ) :
    adjM σ (adaptedTorus (omegaPair ω i j) (1 : Fin r → K)) * unitGram K ℓ r *
        adaptedTorus (omegaPair ω i j) 1 = unitGram K ℓ r ∧
      (adaptedTorus (omegaPair ω i j) (1 : Fin r → K)).det = 1 ∧
      adaptedTorus (omegaPair ω i j) (1 : Fin r → K) * adaptedTorus (omegaPair ω i j) 1 *
        adaptedTorus (omegaPair ω i j) 1 = 1 := by
  have h3 := cube_eq_one_of_cube_root hω
  have hσω2 : σ (ω * ω) = ω := by
    rw [map_mul, hσω]
    linear_combination ω * h3
  refine ⟨adjM_adaptedTorus_mul_unitGram σ (fun m => ?_) (fun k => by simp), ?_, ?_⟩
  · simp only [omegaPair, map_mul]
    split_ifs <;> simp only [hσω, hσω2, map_one] <;> first
      | linear_combination h3
      | linear_combination (ω * ω * ω + 1) * h3
      | simp
  · rw [det_adaptedTorus, prod_omegaPair]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    linear_combination (ω * ω * ω + 1) * h3
  · rw [adaptedTorus_mul_adaptedTorus, adaptedTorus_mul_adaptedTorus, omegaPair_cube ω h3,
      one_mul, one_mul,
      adaptedTorus_one]

variable [CharP K 2]

omit [CharP K 2] in
theorem conj_one_add_of_mul_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] {D D' : Matrix ι ι K}
    (h : D * D' = 1) (P : Matrix ι ι K) : D * (1 + P) * D' = 1 + D * P * D' := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h]

omit [CharP K 2] in
theorem adaptedTorus_conj_single (a a' : Fin ℓ → K) (b b' : Fin r → K)
    (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    adaptedTorus a b * Matrix.single p q 1 * adaptedTorus a' b' =
      (Sum.elim a (Sum.elim a b) p * Sum.elim a' (Sum.elim a' b') q) • Matrix.single p q 1 := by
  rw [adaptedTorus_mul_single, Matrix.smul_mul, single_mul_adaptedTorus, smul_smul]

theorem commute_single_w_x_of_odd (hσ : ∀ x, σ (σ x) = x) (hω : ω * ω + ω + 1 = 0)
    (hσω : σ ω = ω * ω)
    {V : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hodd : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
      adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
      Commute R (sqZeroStd ℓ r) → R * R * R = 1 → Commute V R)
    {i j : Fin ℓ} (hij : i ≠ j) :
    Commute V (Matrix.single (.inr (.inl i)) (.inl j) 1) ∧
      Commute V (Matrix.single (.inr (.inl j)) (.inl i) 1) := by
  have h3 := cube_eq_one_of_cube_root hω
  set D := adaptedTorus (omegaPair ω i j) (1 : Fin r → K) with hD
  set D' := adaptedTorus (omegaPair ω j i) (1 : Fin r → K) with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', adaptedTorus_mul_adaptedTorus, omegaPair_mul ω h3 hij, mul_one, adaptedTorus_one]
  obtain ⟨hDJ, hDdet, hD3⟩ := omegaPair_props (r := r) hσω hω i j
  obtain ⟨hD'J, hD'det, hD'3⟩ := omegaPair_props (r := r) hσω hω j i
  have hVD' : Commute V D' := hodd D' hD'J hD'det (adaptedTorus_commute _ _) hD'3
  have key : ∀ s : K, Commute V ((ω * s) • Matrix.single (.inr (.inl i)) (.inl j) 1 +
      (ω * ω * σ s) • Matrix.single (.inr (.inl j)) (.inl i) 1) := by
    intro s
    obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
        P = s • Matrix.single (.inr (.inl i)) (.inl j) 1 +
          σ s • Matrix.single (.inr (.inl j)) (.inl i) 1 := ⟨_, rfl⟩
    have hPe : P = symP σ (s • Pi.single (.inr (.inl i)) 1) (Pi.single (.inr (.inl j)) 1 :
        Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) := by rw [hP, symP_w_w]
    have hP2 : P * P = 0 := by rw [hPe]; exact symP_w_w_mul_self i j s
    have hPJ : adjM σ P * unitGram K ℓ r = unitGram K ℓ r * P := by
      rw [hPe]; exact symP_adj hσ _ _
    have hPS : Commute P (sqZeroStd ℓ r) := by rw [hPe]; exact symP_w_w_commute i j s
    have hxJ : adjM σ (1 + P) * unitGram K ℓ r * (1 + P) = unitGram K ℓ r := by
      have h := adjM_one_add_smul_mul_unitGram hPJ hP2 (map_one σ)
      rwa [one_smul] at h
    have hxx : (1 + P) * (1 + P) = 1 := by
      calc (1 + P) * (1 + P) = 1 + (P + P) + P * P := by noncomm_ring
        _ = 1 := by rw [matrix_add_self, hP2, add_zero, add_zero]
    have hxx' : ∀ X, (1 + P) * ((1 + P) * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hxx, Matrix.one_mul]
    have hD3' : ∀ X, D * (D * (D * X)) = X := fun X => by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD3, Matrix.one_mul]
    have hxS : Commute (1 + P) (sqZeroStd ℓ r) := (Commute.one_left _).add_left hPS
    have hR := hodd ((1 + P) * D * (1 + P))
      (adjM_mul_unitGram_mul (adjM_mul_unitGram_mul hxJ hDJ) hxJ)
      (by rw [Matrix.det_mul, Matrix.det_mul, hDdet, mul_one, ← Matrix.det_mul, hxx,
        Matrix.det_one])
      ((hxS.mul_left (adaptedTorus_commute _ _)).mul_left hxS)
      (by simp only [Matrix.mul_assoc, hxx', hD3', hxx])
    have hc := commute_conj_mul hVD' hR
    have hDPD : D * P * D' = (ω * ω * s) • Matrix.single (.inr (.inl i)) (.inl j) 1 +
        (ω * ω * (ω * ω) * σ s) • Matrix.single (.inr (.inl j)) (.inl i) 1 := by
      rw [hP, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.smul_mul, hD, hD', adaptedTorus_conj_single, adaptedTorus_conj_single, smul_smul,
        smul_smul]
      simp only [Sum.elim_inr, Sum.elim_inl, omegaPair_apply_left ω hij,
        omegaPair_apply_left ω (Ne.symm hij), omegaPair_apply_right ω hij,
        omegaPair_apply_right ω (Ne.symm hij)]
      congr 1 <;> congr 1 <;> ring
    have hsing : ∀ a b c d : Fin ℓ, Matrix.single (Sum.inr (Sum.inl a) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
        (Sum.inl b : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K) *
          Matrix.single (Sum.inr (Sum.inl c) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
            (Sum.inl d : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) 1 = 0 := fun a b c d =>
      Matrix.single_mul_single_of_ne (1 : K) _ _ _ (by simp) 1
    have hPDPD : P * (D * P * D') = 0 := by
      rw [hDPD, hP]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hsing,
        smul_zero, add_zero]
    have e : (1 + P) * (D * (1 + P) * D') =
        1 + ((ω * s) • Matrix.single (.inr (.inl i)) (.inl j) 1 +
          (ω * ω * σ s) • Matrix.single (.inr (.inl j)) (.inl i) 1) := by
      rw [conj_one_add_of_mul_eq_one hDD', Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
        Matrix.one_mul,
        Matrix.mul_one, Matrix.one_mul, hPDPD, add_zero, hDPD, hP]
      linear_combination (norm := module)
        (s * hω - ω * s * CharTwo.two_eq_zero (R := K)) •
          Matrix.single (Sum.inr (Sum.inl i) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Sum.inl j) (1 : K) +
        (σ s * (ω * ω - ω + 1) * hω - ω * ω * σ s * CharTwo.two_eq_zero (R := K)) •
          Matrix.single (Sum.inr (Sum.inl j) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Sum.inl i) (1 : K)
    rw [e] at hc
    have h := hc.sub_right (Commute.one_right V)
    rwa [add_sub_cancel_left] at h
  have h1 : Commute V (ω • Matrix.single (.inr (.inl i)) (.inl j) 1 +
      (ω * ω) • Matrix.single (.inr (.inl j)) (.inl i) 1) :=
    commute_of_eq (key 1) (by rw [map_one, mul_one, mul_one])
  have h2 : Commute V ((ω * ω) • Matrix.single (.inr (.inl i)) (.inl j) 1 +
      ω • Matrix.single (.inr (.inl j)) (.inl i) 1) :=
    commute_of_eq (key ω) (by rw [hσω, show ω * ω * (ω * ω) = ω by linear_combination ω * h3])
  exact commute_of_cube_root hω h1 h2

end RootW

section RootY

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {ℓ r : ℕ} {ω : K}

omit [CharP K 2] in
theorem adaptedTorus_props (hσω : σ ω = ω * ω) (hω : ω * ω + ω + 1 = 0) {a : Fin ℓ → K}
    {b : Fin r → K} (ha : ∀ m, a m = 1 ∨ a m = ω ∨ a m = ω * ω)
    (hb : ∀ k, b k = 1 ∨ b k = ω ∨ b k = ω * ω) (hdet : (∏ m, a m) ^ 2 * ∏ k, b k = 1) :
    adjM σ (adaptedTorus a b) * unitGram K ℓ r * adaptedTorus a b = unitGram K ℓ r ∧
      (adaptedTorus a b).det = 1 ∧ adaptedTorus a b * adaptedTorus a b * adaptedTorus a b = 1 := by
  have h3 := cube_eq_one_of_cube_root hω
  have hσω2 : σ (ω * ω) = ω := by
    rw [map_mul, hσω]
    linear_combination ω * h3
  have hn : ∀ x : K, (x = 1 ∨ x = ω ∨ x = ω * ω) → σ x * x = 1 ∧ x * x * x = 1 := by
    rintro x (rfl | rfl | rfl)
    · simp
    · rw [hσω]
      exact ⟨by linear_combination h3, h3⟩
    · rw [hσω2]
      exact ⟨by linear_combination h3, by linear_combination (ω * ω * ω + 1) * h3⟩
  refine ⟨adjM_adaptedTorus_mul_unitGram σ (fun m => (hn _ (ha m)).1) (fun k => (hn _ (hb k)).1),
    by rw [det_adaptedTorus, hdet], ?_⟩
  rw [adaptedTorus_mul_adaptedTorus, adaptedTorus_mul_adaptedTorus]
  have e1 : a * a * a = 1 := funext fun m => (hn _ (ha m)).2
  have e2 : b * b * b = 1 := funext fun k => (hn _ (hb k)).2
  rw [e1, e2, adaptedTorus_one]

theorem commute_single_y_of_odd (hσ : ∀ x, σ (σ x) = x) (hω : ω * ω + ω + 1 = 0)
    (hσω : σ ω = ω * ω)
    {V : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hodd : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
      adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
      Commute R (sqZeroStd ℓ r) → R * R * R = 1 → Commute V R)
    (j : Fin ℓ) (k : Fin r) {a a' : Fin ℓ → K} {b b' : Fin r → K}
    (ha : ∀ m, a m = 1 ∨ a m = ω ∨ a m = ω * ω) (hb : ∀ m, b m = 1 ∨ b m = ω ∨ b m = ω * ω)
    (ha' : ∀ m, a' m = 1 ∨ a' m = ω ∨ a' m = ω * ω)
    (hb' : ∀ m, b' m = 1 ∨ b' m = ω ∨ b' m = ω * ω)
    (hdet : (∏ m, a m) ^ 2 * ∏ m, b m = 1) (hdet' : (∏ m, a' m) ^ 2 * ∏ m, b' m = 1)
    (hDD : adaptedTorus a b * adaptedTorus a' b' = 1)
    (hD'D : adaptedTorus a' b' * adaptedTorus a b = 1)
    (hχ : b k * a' j = ω) (hχ' : a j * b' k = ω * ω) (h1 : a j * a' j = 1)
    (hχ2 : b' k * a j = ω * ω) (hχ2' : a' j * b k = ω) (h12 : a' j * a j = 1) :
    Commute V (Matrix.single (.inr (.inr k)) (.inl j) 1) ∧
      Commute V (Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
  have h3 := cube_eq_one_of_cube_root hω
  have hσω2 : σ (ω * ω) = ω := by
    rw [map_mul, hσω]
    linear_combination ω * h3
  have two := CharTwo.two_eq_zero (R := K)
  have hzY0 : zY σ j k 0 0 = 0 := by rw [zY_eq]; simp
  have step : ∀ (a₀ a₀' : Fin ℓ → K) (b₀ b₀' : Fin r → K) (χ : K),
      (∀ m, a₀ m = 1 ∨ a₀ m = ω ∨ a₀ m = ω * ω) → (∀ m, b₀ m = 1 ∨ b₀ m = ω ∨ b₀ m = ω * ω) →
      (∀ m, a₀' m = 1 ∨ a₀' m = ω ∨ a₀' m = ω * ω) →
      (∀ m, b₀' m = 1 ∨ b₀' m = ω ∨ b₀' m = ω * ω) →
      (∏ m, a₀ m) ^ 2 * ∏ m, b₀ m = 1 → (∏ m, a₀' m) ^ 2 * ∏ m, b₀' m = 1 →
      adaptedTorus a₀ b₀ * adaptedTorus a₀' b₀' = 1 →
      (∀ t c, adaptedTorus a₀ b₀ * zY σ j k t c * adaptedTorus a₀' b₀' = zY σ j k (χ * t) c) →
      ∀ t, σ t * t = 1 → Commute V (zY σ j k ((1 + χ) * t) (1 + χ)) := by
    intro a₀ a₀' b₀ b₀' χ ha₀ hb₀ ha₀' hb₀' hd₀ hd₀' hDD' hconj t ht
    obtain ⟨hDJ, hDdet, hD3⟩ := adaptedTorus_props hσω hω ha₀ hb₀ hd₀
    obtain ⟨hD'J, hD'det, hD'3⟩ := adaptedTorus_props hσω hω ha₀' hb₀' hd₀'
    have hVD' := hodd _ hD'J hD'det (adaptedTorus_commute _ _) hD'3
    have hc1 : ω + σ ω = σ t * t := by rw [hσω, ht]; linear_combination hω - two
    have hc2 : ω * ω + σ (ω * ω) = σ t * t := by rw [hσω2, ht]; linear_combination hω - two
    have hXX : (1 + zY σ j k t ω) * (1 + zY σ j k t (ω * ω)) = 1 := by
      rw [one_add_zY_mul, show t + t = 0 by linear_combination t * two,
        show ω + ω * ω + σ t * t = 0 by rw [ht]; exact (by linear_combination hω), hzY0, add_zero]
    have hXX' : (1 + zY σ j k t (ω * ω)) * (1 + zY σ j k t ω) = 1 := by
      rw [one_add_zY_mul, show t + t = 0 by linear_combination t * two,
        show ω * ω + ω + σ t * t = 0 by rw [ht]; exact hω, hzY0, add_zero]
    have hXJ := adjM_one_add_zY hσ j k hc1
    have hX'J := adjM_one_add_zY hσ j k hc2
    have hXS : Commute (1 + zY σ j k t ω) (sqZeroStd ℓ r) :=
      (Commute.one_left _).add_left (zY_commute j k t ω)
    have hX'S : Commute (1 + zY σ j k t (ω * ω)) (sqZeroStd ℓ r) :=
      (Commute.one_left _).add_left (zY_commute j k t (ω * ω))
    have hD3' : ∀ X, adaptedTorus a₀ b₀ * (adaptedTorus a₀ b₀ * (adaptedTorus a₀ b₀ * X)) = X := by
      intro X
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hD3, Matrix.one_mul]
    have hXX'' : ∀ X, (1 + zY σ j k t (ω * ω)) * ((1 + zY σ j k t ω) * X) = X := fun X => by
      rw [← Matrix.mul_assoc, hXX', Matrix.one_mul]
    have hR := hodd ((1 + zY σ j k t ω) * adaptedTorus a₀ b₀ * (1 + zY σ j k t (ω * ω)))
      (adjM_mul_unitGram_mul (adjM_mul_unitGram_mul hXJ hDJ) hX'J)
      (by rw [Matrix.det_mul, Matrix.det_mul, hDdet, mul_one, ← Matrix.det_mul, hXX,
        Matrix.det_one])
      ((hXS.mul_left (adaptedTorus_commute _ _)).mul_left hX'S)
      (by simp only [Matrix.mul_assoc, hXX'', hD3', hXX])
    have hc := commute_conj_mul hVD' hR
    rw [conj_one_add_of_mul_eq_one hDD', hconj, one_add_zY_mul,
      show t + χ * t = (1 + χ) * t by ring,
      show ω + ω * ω + σ t * (χ * t) = 1 + χ by
        rw [show σ t * (χ * t) = χ * (σ t * t) by ring, ht]
        linear_combination hω - two] at hc
    have h := hc.sub_right (Commute.one_right V)
    rwa [add_sub_cancel_left] at h
  have hA := step a a' b b' ω ha hb ha' hb' hdet hdet' hDD (fun t c => by
    rw [zY_eq, zY_eq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      adaptedTorus_conj_single, smul_smul, Sum.elim_inr, Sum.elim_inl, hχ, hχ', h1, map_mul, hσω]
    congr 1
    · congr 1 <;> congr 1 <;> ring
    · ring_nf)
  have hB := step a' a b' b (ω * ω) ha' hb' ha hb hdet' hdet hD'D (fun t c => by
    rw [zY_eq, zY_eq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      adaptedTorus_conj_single, smul_smul, Sum.elim_inr, Sum.elim_inl, hχ2, hχ2', h12, map_mul,
      hσω2]
    congr 1
    · congr 1 <;> congr 1 <;> ring
    · ring_nf)
  have hn1 : σ ω * ω = 1 := by rw [hσω]; exact h3
  have hn2 : σ (ω * ω) * (ω * ω) = 1 := by rw [hσω2]; linear_combination h3
  have hW1 : Commute V (zY σ j k 1 (ω * ω)) := commute_of_eq (hA ω hn1) (by
    congr 1
    · linear_combination hω - two
    · linear_combination hω - ω * ω * two)
  have hW2 : Commute V (zY σ j k 1 ω) := commute_of_eq (hB (ω * ω) hn2) (by
    congr 1
    · linear_combination hω - two + ω * h3
    · linear_combination hω - ω * two)
  have hW3 : Commute V (zY σ j k ω (ω * ω)) := commute_of_eq (hA (ω * ω) hn2) (by
    congr 1
    · linear_combination h3 + hω - ω * two
    · linear_combination hω - ω * ω * two)
  have hWX : Commute V (Matrix.single (.inr (.inl j)) (.inl j) 1) :=
    commute_of_eq (hW1.sub_right hW2) (by
      rw [zY_eq, zY_eq]
      linear_combination (norm := module) (hω - (ω + 1) * two) •
        Matrix.single (Sum.inr (Sum.inl j) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
          (Sum.inl j : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K))
  have hY1 : Commute V (Matrix.single (.inr (.inr k)) (.inl j) 1 +
      Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) :=
    commute_of_eq (hW1.sub_right (hWX.smul_right (ω * ω))) (by
      rw [zY_eq, map_one]
      module)
  have hY2 : Commute V (ω • Matrix.single (.inr (.inr k)) (.inl j) 1 +
      (ω * ω) • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) :=
    commute_of_eq (hW3.sub_right (hWX.smul_right (ω * ω))) (by
      rw [zY_eq, hσω]
      module)
  have hWY : Commute V (Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) :=
    commute_of_eq ((hY1.smul_right ω).add_right hY2) (by
      linear_combination (norm := module) (ω * two) •
          Matrix.single (Sum.inr (Sum.inr k) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
            (Sum.inl j : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K) +
        (hω - two) • Matrix.single (Sum.inr (Sum.inl j) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))
          (Sum.inr (Sum.inr k) : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (1 : K))
  exact ⟨commute_of_eq (hY1.sub_right hWY) (by module), hWY⟩

end RootY

section Singles

variable {K : Type} [Field K] {ℓ r : ℕ}

theorem eq_of_commute_singles (hℓ0 : ℓ ≠ 0) (hr0 : r = 0 → 2 ≤ ℓ)
    {B : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hBN : B * sqZeroStd ℓ r = sqZeroStd ℓ r * B)
    (hC1 : ∀ i j : Fin ℓ, i ≠ j →
      B * Matrix.single (.inr (.inl i)) (.inl j) 1 =
        Matrix.single (.inr (.inl i)) (.inl j) 1 * B)
    (hC2 : ∀ (k : Fin r) (j : Fin ℓ),
      B * Matrix.single (.inr (.inr k)) (.inl j) 1 =
        Matrix.single (.inr (.inr k)) (.inl j) 1 * B)
    (hC3 : ∀ (i : Fin ℓ) (k : Fin r),
      B * Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 =
        Matrix.single (.inr (.inl i)) (.inr (.inr k)) 1 * B) :
    ∃ lam : K, ∀ m m', (∀ a c : Fin ℓ, ¬ (m = .inr (.inl a) ∧ m' = .inl c)) →
      B m m' = if m = m' then lam else 0 := by
  have hC0 : ∀ a : Fin ℓ, B (.inr (.inl a)) (.inr (.inl a)) = B (.inl a) (.inl a) := by
    intro a
    have h := congrFun (congrFun hBN (.inr (.inl a))) (.inl a)
    rw [Matrix.mul_apply, Matrix.mul_apply] at h
    rw [Fintype.sum_eq_single (.inr (.inl a)) (fun k hk => by
        rw [sqZeroStd_apply, Sum.elim_inl, ite_eq_right hk, mul_zero])] at h
    rw [Fintype.sum_eq_single (.inl a) (fun k hk => by
        rw [sqZeroStd_apply]
        rcases k with c | c
        · rw [Sum.elim_inl, ite_eq_right (by intro h'; apply hk; simpa [eq_comm] using h'),
            zero_mul]
        · rw [Sum.elim_inr, zero_mul])] at h
    simpa [sqZeroStd_apply] using h
  have hℓ1 : 0 < ℓ := Nat.pos_of_ne_zero hℓ0
  set j₀ : Fin ℓ := ⟨0, hℓ1⟩ with hj₀
  have hother : 2 ≤ ℓ → ∀ i : Fin ℓ, ∃ j : Fin ℓ, j ≠ i := by
    intro h2 i
    by_cases hi : i.val = 0
    · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hi; simp at hi⟩
    · exact ⟨⟨0, by omega⟩, fun h => hi (by rw [← h])⟩
  set lam := B (.inl j₀) (.inl j₀) with hlam
  have hRowX : ∀ (a : Fin ℓ) m', m' ≠ .inl a → B (.inl a) m' = 0 := by
    intro a m' hm'
    rcases Nat.eq_zero_or_pos r with hr | hr
    · obtain ⟨i, hi⟩ := hother (hr0 hr) a
      exact (entries_of_commute_single (hC1 i a hi)).2.1 m' hm'
    · exact (entries_of_commute_single (hC2 ⟨0, hr⟩ a)).2.1 m' hm'
  have hRowY : ∀ (k : Fin r) m', m' ≠ .inr (.inr k) → B (.inr (.inr k)) m' = 0 :=
    fun k m' hm' => (entries_of_commute_single (hC3 j₀ k)).2.1 m' hm'
  have hColW : ∀ (c : Fin ℓ) m, m ≠ .inr (.inl c) → B m (.inr (.inl c)) = 0 := by
    intro c m hm
    rcases Nat.eq_zero_or_pos r with hr | hr
    · obtain ⟨j, hj⟩ := hother (hr0 hr) c
      exact (entries_of_commute_single (hC1 c j (Ne.symm hj))).1 m hm
    · exact (entries_of_commute_single (hC3 c ⟨0, hr⟩)).1 m hm
  have hColY : ∀ (k : Fin r) m, m ≠ .inr (.inr k) → B m (.inr (.inr k)) = 0 :=
    fun k m hm => (entries_of_commute_single (hC2 k j₀)).1 m hm
  have hDiagX : ∀ a : Fin ℓ, B (.inl a) (.inl a) = lam := by
    intro a
    rcases Nat.eq_zero_or_pos r with hr | hr
    · by_cases ha : a = j₀
      · rw [ha]
      · have h1 := (entries_of_commute_single (hC1 j₀ a (Ne.symm ha))).2.2
        rw [← h1, hC0]
    · rw [← (entries_of_commute_single (hC2 ⟨0, hr⟩ a)).2.2,
        (entries_of_commute_single (hC2 ⟨0, hr⟩ j₀)).2.2]
  have hDiag : ∀ k, B k k = lam := by
    intro k
    rcases k with a | a | k
    · exact hDiagX a
    · rw [hC0]
      exact hDiagX a
    · rw [(entries_of_commute_single (hC2 k j₀)).2.2]
  refine ⟨lam, fun m m' hmm' => ?_⟩
  by_cases hm : m = m'
  · subst hm
    rw [ite_eq_left rfl, hDiag]
  rw [ite_eq_right hm]
  rcases m' with c | c | k
  · rcases m with a | a | k
    · exact hRowX a _ (fun h => hm (by rw [h]))
    · exact absurd ⟨rfl, rfl⟩ (hmm' a c)
    · exact hRowY k _ (by simp)
  · exact hColW c m hm
  · exact hColY k m hm

end Singles

section Perm

variable {K : Type} [Field K] {ℓ r : ℕ}

@[expose] def xwBlockPerm (π : Equiv.Perm (Fin ℓ)) : Equiv.Perm (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :=
  Equiv.sumCongr π (Equiv.sumCongr π (Equiv.refl _))

@[expose] def swapXWPerm : Equiv.Perm (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :=
  ⟨swapXW, swapXW, swapXW_swapXW, swapXW_swapXW⟩

theorem unitGram_eq_permMatrix :
    unitGram K ℓ r = (swapXWPerm (ℓ := ℓ) (r := r)).permMatrix K := by
  ext p q
  simp only [unitGram, Matrix.of_apply, swapXWPerm, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Equiv.coe_fn_mk, Option.mem_def, Option.some.injEq]
  simp only [eq_comm]

theorem xwBlockPerm_mul_swapXWPerm (π : Equiv.Perm (Fin ℓ)) :
    xwBlockPerm (r := r) π * swapXWPerm = swapXWPerm * xwBlockPerm π := by
  ext p
  rcases p with i | i | k <;> rfl

theorem adjM_permMatrix (σ : K →+* K) (τ : Equiv.Perm (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r))) :
    adjM σ (τ.permMatrix K) = (τ⁻¹).permMatrix K := by
  rw [adjM, ← Matrix.transpose_permMatrix]
  congr 1
  ext p q
  simp only [Matrix.map_apply, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem adjM_xwBlockPerm_mul_unitGram (σ : K →+* K) (π : Equiv.Perm (Fin ℓ)) :
    adjM σ ((xwBlockPerm (r := r) π).permMatrix K) * unitGram K ℓ r *
      (xwBlockPerm π).permMatrix K = unitGram K ℓ r := by
  rw [adjM_permMatrix, unitGram_eq_permMatrix, ← Matrix.permMatrix_mul,
    ← Matrix.permMatrix_mul]
  congr 1
  rw [← mul_assoc, xwBlockPerm_mul_swapXWPerm, mul_assoc, mul_inv_cancel, mul_one]

theorem det_xwBlockPerm (π : Equiv.Perm (Fin ℓ)) :
    ((xwBlockPerm (r := r) π).permMatrix K).det = 1 := by
  rw [Matrix.det_permutation, xwBlockPerm, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr,
    Equiv.Perm.sign_refl, mul_one, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem xwBlockPerm_commute (π : Equiv.Perm (Fin ℓ)) :
    Commute ((xwBlockPerm (r := r) π).permMatrix K) (sqZeroStd ℓ r) := by
  show (xwBlockPerm (r := r) π).permMatrix K * sqZeroStd ℓ r =
    sqZeroStd ℓ r * (xwBlockPerm π).permMatrix K
  ext p q
  simp only [Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [← Equiv.eq_symm_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rcases q with c | c | k <;> rcases p with a | a | k' <;>
    simp [xwBlockPerm, sqZeroStd_apply, Equiv.eq_symm_apply]

theorem xwBlockPerm_cube {π : Equiv.Perm (Fin ℓ)} (hπ : π * π * π = 1) :
    (xwBlockPerm (r := r) π).permMatrix K * (xwBlockPerm π).permMatrix K *
      (xwBlockPerm π).permMatrix K = 1 := by
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  have h : xwBlockPerm (r := r) π * (xwBlockPerm π * xwBlockPerm π) = 1 := by
    ext p
    have hi : ∀ i, π (π (π i)) = i := fun i => by
      have := congrArg (fun τ : Equiv.Perm (Fin ℓ) => τ i) hπ
      simpa [Equiv.Perm.mul_apply] using this
    rcases p with i | i | k <;> simp [xwBlockPerm, hi]
  rw [h, Matrix.permMatrix_one]

theorem apply_xwBlockPerm_of_commute
    {V : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K} {π : Equiv.Perm (Fin ℓ)}
    (h : Commute V ((xwBlockPerm (r := r) π).permMatrix K)) (p q : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) :
    V (xwBlockPerm π p) (xwBlockPerm π q) = V p q := by
  have h1 := congrFun (congrFun h.eq p) (xwBlockPerm π q)
  simp only [Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, EmbeddingLike.apply_eq_iff_eq,
    Finset.sum_ite_eq'] at h1
  exact h1.symm

theorem exists_threeCycle_apply_eq {a b c : Fin ℓ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ π : Equiv.Perm (Fin ℓ), π * π * π = 1 ∧ π a = b := by
  refine ⟨Equiv.swap b a * Equiv.swap b c, ?_, ?_⟩
  · have h := (Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hbc hac).orderOf
    have h3 := pow_orderOf_eq_one (Equiv.swap b a * Equiv.swap b c)
    rw [h, pow_three, ← mul_assoc] at h3
    exact h3
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab hac, Equiv.swap_apply_right]

end Perm

section Commutant

variable {K : Type} [Field K] [CharP K 2] {σ : K →+* K} {ℓ r : ℕ} {ω : K}

omit [CharP K 2] in
theorem sqZeroStd_eq_sum :
    sqZeroStd (K := K) ℓ r = ∑ i : Fin ℓ, Matrix.single (.inr (.inl i)) (.inl i) 1 := by
  ext m m'
  rw [sqZeroStd_apply, Matrix.sum_apply]
  rcases m' with c | c | k
  · rw [Sum.elim_inl, Fintype.sum_eq_single c (fun i hi => by
      rw [Matrix.single_apply, ite_eq_right (fun h => hi (Sum.inl_injective h.2))])]
    rw [Matrix.single_apply]
    simp [eq_comm]
  · simp
  · simp

theorem commutant_odd_unitary (hσ : ∀ x, σ (σ x) = x) (hω : ω * ω + ω + 1 = 0)
    (hσω : σ ω = ω * ω) (hcard : 4 ≤ 2 * ℓ + r) (hℓ0 : ℓ ≠ 0)
    {V : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hodd : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
      adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
      Commute R (sqZeroStd ℓ r) → R * R * R = 1 → Commute V R)
    (hVS : Commute V (sqZeroStd ℓ r)) :
    ∃ (lam : K) (β : Fin ℓ → K),
      V = lam • 1 + ∑ i, β i • Matrix.single (.inr (.inl i)) (.inl i) 1 ∧
        (ℓ ≠ 2 → ∀ i j, β i = β j) := by
  have h3 := cube_eq_one_of_cube_root hω
  have hω0 : ω ≠ 0 := fun h => by rw [h] at hω; simp at hω
  have hC1 : ∀ i j : Fin ℓ, i ≠ j → V * Matrix.single (.inr (.inl i)) (.inl j) 1 =
      Matrix.single (.inr (.inl i)) (.inl j) 1 * V := fun i j hij =>
    (commute_single_w_x_of_odd hσ hω hσω hodd hij).1.eq
  have hY : ∀ (j : Fin ℓ) (k : Fin r), Commute V (Matrix.single (.inr (.inr k)) (.inl j) 1) ∧
      Commute V (Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
    intro j k
    have htri : ∀ x : K, x = ω * (ω * ω) ∨ x = ω * 1 ∨ x = 1 * (ω * ω) ∨ x = 1 * 1 →
        x = 1 ∨ x = ω ∨ x = ω * ω := by
      rintro x (rfl | rfl | rfl | rfl)
      · exact Or.inl (by linear_combination h3)
      · exact Or.inr (Or.inl (mul_one ω))
      · exact Or.inr (Or.inr (one_mul _))
      · exact Or.inl (one_mul 1)
    by_cases hr : 2 ≤ r
    · obtain ⟨k', hk'⟩ : ∃ k' : Fin r, k' ≠ k := by
        by_cases hk : k.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hk; simp at hk⟩
        · exact ⟨⟨0, by omega⟩, fun h => hk (by rw [← h])⟩
      have hpt : ∀ (k₁ k₂ : Fin r) m, omegaPair ω k₁ k₂ m = 1 ∨ omegaPair ω k₁ k₂ m = ω ∨
          omegaPair ω k₁ k₂ m = ω * ω := by
        intro k₁ k₂ m
        apply htri
        simp only [omegaPair]
        split_ifs <;> simp
      have hdt : ∀ k₁ k₂ : Fin r, (∏ m : Fin ℓ, (1 : Fin ℓ → K) m) ^ 2 *
          ∏ m, omegaPair ω k₁ k₂ m = 1 := fun k₁ k₂ => by
        rw [prod_omegaPair]
        simp only [Pi.one_apply, Finset.prod_const_one, one_pow, one_mul]
        linear_combination h3
      exact commute_single_y_of_odd hσ hω hσω hodd j k (a := 1) (a' := 1)
        (b := omegaPair ω k k') (b' := omegaPair ω k' k) (fun _ => Or.inl rfl) (hpt k k')
        (fun _ => Or.inl rfl) (hpt k' k) (hdt k k') (hdt k' k)
        (by rw [adaptedTorus_mul_adaptedTorus, mul_one, omegaPair_mul ω h3 (Ne.symm hk'),
          adaptedTorus_one])
        (by rw [adaptedTorus_mul_adaptedTorus, mul_one, omegaPair_mul ω h3 hk', adaptedTorus_one])
        (by rw [omegaPair_apply_left ω (Ne.symm hk'), Pi.one_apply, mul_one])
        (by rw [Pi.one_apply, one_mul, omegaPair_apply_right ω hk']) (by simp)
        (by rw [omegaPair_apply_right ω hk', Pi.one_apply, mul_one])
        (by rw [Pi.one_apply, one_mul, omegaPair_apply_left ω (Ne.symm hk')]) (by simp)
    · have hr1 : r = 1 := by have := k.2; omega
      have hℓ2 : 2 ≤ ℓ := by omega
      obtain ⟨e, he⟩ : ∃ e : Fin ℓ, e ≠ j := by
        by_cases hj : j.val = 0
        · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hj; simp at hj⟩
        · exact ⟨⟨0, by omega⟩, fun h => hj (by rw [← h])⟩
      have hs : ∀ (z : K), z = ω ∨ z = ω * ω → ∀ {n : ℕ} (e₀ : Fin n) m,
          (if m = e₀ then z else 1) = 1 ∨ (if m = e₀ then z else 1) = ω ∨
            (if m = e₀ then z else 1) = ω * ω := by
        rintro z hz n e₀ m
        split_ifs
        · rcases hz with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        · exact Or.inl rfl
      have hω6 : ω * ω * (ω * ω) * (ω * ω) = 1 := by
        linear_combination (ω * ω * ω + 1) * h3
      exact commute_single_y_of_odd hσ hω hσω hodd j k
        (a := fun m => if m = e then ω else 1) (a' := fun m => if m = e then ω * ω else 1)
        (b := fun m => if m = k then ω else 1) (b' := fun m => if m = k then ω * ω else 1)
        (hs ω (Or.inl rfl) e) (hs ω (Or.inl rfl) k) (hs (ω * ω) (Or.inr rfl) e)
        (hs (ω * ω) (Or.inr rfl) k)
        (by simp only [Fintype.prod_ite_eq']; linear_combination h3)
        (by simp only [Fintype.prod_ite_eq']; linear_combination hω6)
        (by
          rw [adaptedTorus_mul_adaptedTorus, ← adaptedTorus_one]
          congr 1 <;> ext m <;> simp only [Pi.mul_apply, Pi.one_apply] <;> split_ifs <;>
            first | linear_combination h3 | simp)
        (by
          rw [adaptedTorus_mul_adaptedTorus, ← adaptedTorus_one]
          congr 1 <;> ext m <;> simp only [Pi.mul_apply, Pi.one_apply] <;> split_ifs <;>
            first | linear_combination h3 | simp)
        (by simp [Ne.symm he]) (by simp [Ne.symm he]) (by simp [Ne.symm he])
        (by simp [Ne.symm he]) (by simp [Ne.symm he]) (by simp [Ne.symm he])
  obtain ⟨lam, hlam⟩ := eq_of_commute_singles hℓ0 (fun hr => by omega) hVS.eq hC1
    (fun k j => (hY j k).1.eq) (fun i k => (hY i k).2.eq)
  have hoff : ∀ a c : Fin ℓ, a ≠ c → V (.inr (.inl a)) (.inl c) = 0 := by
    intro a c hac
    obtain ⟨hDJ, hDdet, hD3⟩ := omegaPair_props (r := r) hσω hω a c
    have h := (hodd _ hDJ hDdet (adaptedTorus_commute _ _) hD3).eq
    have h1 := congrFun (congrFun h (.inr (.inl a))) (.inl c)
    simp only [adaptedTorus, Matrix.mul_diagonal, Matrix.diagonal_mul, Sum.elim_inl, Sum.elim_inr,
      omegaPair_apply_left ω hac, omegaPair_apply_right ω hac] at h1
    have hne : ω * ω - ω ≠ 0 := by
      intro h0
      have h5 : ω * (ω - 1) = 0 := by linear_combination h0
      rcases mul_eq_zero.mp h5 with h' | h'
      · exact hω0 h'
      · rw [sub_eq_zero.mp h'] at hω
        exact one_ne_zero (by linear_combination hω - CharTwo.two_eq_zero (R := K))
    exact (mul_eq_zero.mp (show (ω * ω - ω) * V (.inr (.inl a)) (.inl c) = 0 by
      linear_combination h1)).resolve_left hne
  refine ⟨lam, fun i => V (.inr (.inl i)) (.inl i), ?_, ?_⟩
  · ext m m'
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sum_apply, smul_eq_mul]
    simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hwx : ∃ a c : Fin ℓ, m = .inr (.inl a) ∧ m' = .inl c
    · obtain ⟨a, c, rfl, rfl⟩ := hwx
      by_cases hac : a = c
      · subst hac
        simp
      · rw [hoff a c hac, Finset.sum_eq_zero (fun i _ => by
          rw [ite_eq_right (fun h => hac (by
            have h1 : i = a := Sum.inl_injective (Sum.inr_injective h.1)
            have h2 : i = c := Sum.inl_injective h.2
            rw [← h1, h2])), mul_zero])]
        simp
    · push Not at hwx
      rw [hlam m m' (fun a c h => hwx a c h.1 h.2), Finset.sum_eq_zero (fun i _ => by
        rw [ite_eq_right (fun h => hwx i i h.1.symm h.2.symm), mul_zero]), add_zero]
      split_ifs <;> simp
  · intro hℓ2 i j
    by_cases hij : i = j
    · rw [hij]
    have hℓ3 : 3 ≤ ℓ := by
      have h2 : 2 ≤ ℓ := by
        by_contra h
        exact hij (Fin.ext (by have := i.2; have := j.2; omega))
      omega
    obtain ⟨c, hci, hcj⟩ : ∃ c : Fin ℓ, c ≠ i ∧ c ≠ j := by
      by_contra h
      push Not at h
      have key : ∀ c : Fin ℓ, c = i ∨ c = j := fun c => by
        by_cases hc : c = i
        · exact Or.inl hc
        · exact Or.inr (h c hc)
      rcases key ⟨0, by omega⟩ with h0 | h0 <;> rcases key ⟨1, by omega⟩ with h1 | h1 <;>
        rcases key ⟨2, by omega⟩ with h2 | h2 <;>
        simp only [Fin.ext_iff] at h0 h1 h2 <;> omega
    obtain ⟨π, hπ3, hπ⟩ := exists_threeCycle_apply_eq hij (Ne.symm hci) (Ne.symm hcj)
    have hP := hodd _ (adjM_xwBlockPerm_mul_unitGram σ π) (det_xwBlockPerm π)
      (xwBlockPerm_commute π)
      (xwBlockPerm_cube hπ3)
    have h := apply_xwBlockPerm_of_commute hP (.inr (.inl i)) (.inl i)
    simp only [xwBlockPerm, Equiv.sumCongr_apply, Sum.map_inr, Sum.map_inl, hπ] at h
    exact h.symm

end Commutant

section Sandwich

variable {K : Type} [Field K]

@[expose] def SandwichScalar {ι : Type} [Fintype ι] (E : Matrix ι ι K) : Prop :=
  ∀ Y : Matrix ι ι K, ∃ c : K, E * Y * E = c • E

theorem SandwichScalar.map {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {E : Matrix ι ι K} (h : SandwichScalar E) (φ : Matrix ι ι K ≃ₐ[K] Matrix κ κ K) :
    SandwichScalar (φ E) := by
  intro Y
  obtain ⟨c, hc⟩ := h (φ.symm Y)
  refine ⟨c, ?_⟩
  have h1 := congrArg φ hc
  rwa [map_mul, map_mul, AlgEquiv.apply_symm_apply, map_smul] at h1

theorem sandwichScalar_single {ι : Type} [Fintype ι] [DecidableEq ι] (p q : ι) :
    SandwichScalar (Matrix.single p q (1 : K)) := by
  intro Y
  refine ⟨Y q p, ?_⟩
  rw [Matrix.single_mul_mul_single, one_mul, mul_one, Matrix.smul_single, smul_eq_mul, mul_one]

theorem le_one_of_sandwichScalar {ℓ r : ℕ} (h : SandwichScalar (sqZeroStd (K := K) ℓ r)) :
    ℓ ≤ 1 := by
  by_contra hℓ
  push Not at hℓ
  obtain ⟨c, hc⟩ := h (Matrix.single (.inl ⟨0, by omega⟩) (.inr (.inl ⟨1, hℓ⟩)) 1)
  have h1 := congrFun (congrFun hc (.inr (.inl ⟨0, by omega⟩))) (.inl ⟨1, hℓ⟩)
  simp [Matrix.mul_apply, sqZeroStd_apply, Matrix.single_apply] at h1

end Sandwich

end CFSG.ComponentClassification.RankTwoClassical
