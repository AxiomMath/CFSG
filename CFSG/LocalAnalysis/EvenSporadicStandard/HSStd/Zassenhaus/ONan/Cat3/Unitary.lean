module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3.Basic
public import CFSG.Open.StatedCenterThree
public import CFSG.LinearAlgebra.LinearGroups.QuadraticFrobenius

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Open Matrix

variable {K : Type} [Field K]

private abbrev ones3 : Matrix (Fin 3) (Fin 3) K := fun _ _ => 1

private abbrev M3 (b : K) : Matrix (Fin 3) (Fin 3) K := 1 + b • ones3

private lemma M3_mul (b b' : K) : M3 b * M3 b' = M3 (b + b' + 3 * b * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3, ones3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private lemma M3_det (b : K) : (M3 b).det = 1 + 3 * b := by
  rw [Matrix.det_fin_three]
  simp [M3, ones3]
  ring

private lemma M3_transpose (b : K) : (M3 b)ᵀ = M3 b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3, ones3, Matrix.transpose_apply]

private lemma M3_one : M3 (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3, ones3]

private lemma M3_map (σ : K →+* K) (b : K) : (M3 b).map σ = M3 (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M3, ones3, Matrix.map_apply, map_add]

private abbrev Dm {m : ℕ} (d : Fin m → K) : Matrix (Fin m) (Fin m) K := diagonal d

private lemma Dm_mul {m : ℕ} (d e : Fin m → K) :
    Dm d * Dm e = Dm (fun j => d j * e j) := by
  show diagonal d * diagonal e = diagonal (fun j => d j * e j)
  rw [diagonal_mul_diagonal]

private lemma Dm_transpose {m : ℕ} (d : Fin m → K) : (Dm d)ᵀ = Dm d := by
  show (diagonal d)ᵀ = diagonal d
  rw [diagonal_transpose]

private lemma Dm_map (σ : K →+* K) {m : ℕ} (d : Fin m → K) :
    (Dm d).map σ = Dm (fun j => σ (d j)) := by
  show (diagonal d).map σ = diagonal (fun j => σ (d j))
  rw [diagonal_map (map_zero σ)]

private lemma Dm_pow {m : ℕ} (d : Fin m → K) (k : ℕ) :
    (Dm d) ^ k = Dm (fun j => d j ^ k) := by
  show (diagonal d) ^ k = diagonal (fun j => d j ^ k)
  rw [Matrix.diagonal_pow]
  rfl

private abbrev blockDiag {m : ℕ} (A : Matrix (Fin 3) (Fin 3) K) (d : Fin m → K) :
    Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K :=
  fromBlocks A 0 0 (Dm d)

private lemma blockDiag_transpose {m : ℕ} (A : Matrix (Fin 3) (Fin 3) K) (d : Fin m → K) :
    (blockDiag A d)ᵀ = blockDiag Aᵀ d := by
  simp only [blockDiag, fromBlocks_transpose, Dm_transpose, transpose_zero]

private lemma blockDiag_mul {m : ℕ} (A A' : Matrix (Fin 3) (Fin 3) K) (d d' : Fin m → K) :
    blockDiag A d * blockDiag A' d' = blockDiag (A * A') (fun j => d j * d' j) := by
  simp [blockDiag, fromBlocks_multiply, Dm_mul]

private lemma blockDiag_pow {m : ℕ} (A : Matrix (Fin 3) (Fin 3) K) (d : Fin m → K) (k : ℕ) :
    (blockDiag A d) ^ k = blockDiag (A ^ k) (fun j => d j ^ k) := by
  simp only [blockDiag, Matrix.fromBlocks_diagonal_pow, Dm_pow]

private lemma blockDiag_map (σ : K →+* K) {m : ℕ} (A : Matrix (Fin 3) (Fin 3) K)
    (d : Fin m → K) : (blockDiag A d).map σ = blockDiag (A.map σ) (fun j => σ (d j)) := by
  simp only [blockDiag, fromBlocks_map, Dm_map, Matrix.map_zero, map_zero]

private def bseq (b : K) : ℕ → K
  | 0 => 0
  | k + 1 => bseq b k + b + 3 * bseq b k * b

private lemma bseq_succ (b : K) (k : ℕ) :
    bseq b (k + 1) = bseq b k + b + 3 * bseq b k * b := rfl

private lemma M3_pow (b : K) (k : ℕ) : (M3 b) ^ k = M3 (bseq b k) := by
  induction k with
  | zero => rw [pow_zero, bseq]; exact M3_one.symm
  | succ k ih => rw [pow_succ, ih, M3_mul, bseq_succ]

private lemma one_add_three_bseq (b : K) (k : ℕ) :
    1 + 3 * bseq b k = (1 + 3 * b) ^ k := by
  induction k with
  | zero => simp [bseq]
  | succ k ih => rw [bseq_succ, pow_succ, ← ih]; ring

private theorem exists_prime_pow_card_eq_sq [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ q = p ^ k := by
  letI := Fintype.ofFinite K
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  have hK' : Fintype.card K = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  have hq2 : 2 ≤ q := StatedCenterThree.two_le_of_card_eq_sq hK
  have hq0 : q ≠ 0 := by omega
  have hdvd : ∀ {d : ℕ}, d.Prime → d ∣ q → d = ringChar K := by
    intro d hd hdq
    have hdq2 : d ∣ q ^ 2 := by rw [pow_two]; exact dvd_mul_of_dvd_left hdq q
    rw [← hK', hcard] at hdq2
    exact (Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow hdq2)
  have hpow : q = (ringChar K) ^ q.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hq0 (fun hd hdvd' => hdvd hd hdvd')
  refine ⟨ringChar K, q.primeFactorsList.length, hp, ?_, hpow⟩
  by_contra h
  have h0 : q.primeFactorsList.length = 0 := by omega
  have : q = 1 := by rw [hpow, h0, pow_zero]
  omega

private theorem exists_frobenius_of_card_sq [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ σ : K ≃+* K, ∀ x : K, σ x = x ^ q := by
  obtain ⟨p, k, hp, hk1, hqk⟩ := exists_prime_pow_card_eq_sq hK
  have hKq : Nat.card K = (p ^ k) ^ 2 := by rw [hqk] at hK; exact hK
  obtain ⟨σ, hσ, -⟩ := CFSG.LinearGroups.finite_field_quadratic_frobenius (K := K) hp hk1 hKq
  exact ⟨σ, fun x => by rw [hσ x, hqk]⟩

section Block

variable (m : ℕ) [NeZero m]

private abbrev dOf (c : Kˣ) : Fin m → K :=
  fun j => if j = 0 then ((c⁻¹ : Kˣ) : K) else 1

private abbrev gmat (b : K) (c : Kˣ) : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K :=
  blockDiag (M3 b) (dOf m c)

private lemma prod_dOf (c : Kˣ) : ∏ j : Fin m, dOf m c j = ((c⁻¹ : Kˣ) : K) := by
  rw [show dOf m c = fun j : Fin m => if j = 0 then ((c⁻¹ : Kˣ) : K) else 1 from rfl]
  exact Fintype.prod_ite_eq' 0 (fun _ => ((c⁻¹ : Kˣ) : K))

private lemma gmat_det (b : K) (c : Kˣ) :
    (gmat m b c).det = (1 + 3 * b) * ((c⁻¹ : Kˣ) : K) := by
  rw [gmat, blockDiag, Matrix.det_fromBlocks_zero₂₁, M3_det, Dm, Matrix.det_diagonal,
    prod_dOf]

private lemma gmat_unitary {q : ℕ} {σ : K →+* K} (hσ : ∀ x : K, σ x = x ^ q)
    {c : Kˣ} (hc : c ^ (q + 1) = 1) {b : K} (hb : 1 + 3 * b = (c : K)) (h3 : (3 : K) ≠ 0) :
    ((gmat m b c).map (· ^ q))ᵀ * (gmat m b c) = 1 := by
  have hcK : (c : K) ^ (q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
  have hbpow : (1 + 3 * b) ^ (q + 1) = 1 := by rw [hb]; exact hcK
  have h1 : (1 + 3 * b) ^ q = 1 + 3 * b ^ q := by
    rw [← hσ (1 + 3 * b)]
    simp only [map_add, map_mul, map_one, map_ofNat, hσ b]
  have h2 : (1 + 3 * b) * (1 + 3 * b ^ q) = 1 := by
    rw [← h1, mul_comm, ← pow_succ, hbpow]
  have hbq : b + b ^ q + 3 * b * b ^ q = 0 := by
    have hlin : (1 + 3 * b) * (1 + 3 * b ^ q) = 1 + 3 * (b + b ^ q + 3 * b * b ^ q) := by
      ring
    have h4 : (1 : K) + 3 * (b + b ^ q + 3 * b * b ^ q) = 1 := by rw [← hlin]; exact h2
    have h5 : (3 : K) * (b + b ^ q + 3 * b * b ^ q) = 0 := by
      have h4' : (1 : K) + 3 * (b + b ^ q + 3 * b * b ^ q) = 1 + 0 := by simpa using h4
      exact add_left_cancel h4'
    exact (mul_eq_zero.mp h5).resolve_left h3
  have hmap : (gmat m b c).map (· ^ q) =
      blockDiag (M3 (b ^ q)) (fun j => (dOf m c j) ^ q) := by
    rw [show (fun x : K => x ^ q) = ⇑σ from funext fun x => (hσ x).symm]
    simp only [gmat, blockDiag_map, M3_map, hσ]
  have hdq : ∀ j : Fin m, (dOf m c j) ^ q * dOf m c j = 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [show dOf m c 0 = ((c⁻¹ : Kˣ) : K) from rfl,
        show ((c⁻¹ : Kˣ) : K) = ((c : K))⁻¹ from by simp, inv_pow, ← _root_.mul_inv_rev,
        mul_comm ((c : K)) ((c : K) ^ q), ← pow_succ, hcK, inv_one]
    · rw [show dOf m c j = (1 : K) from by rw [dOf]; simp [hj]]
      simp
  rw [hmap, blockDiag_transpose, M3_transpose, blockDiag_mul]
  rw [show M3 (b ^ q) * M3 b = M3 (b ^ q + b + 3 * b ^ q * b) from M3_mul _ _]
  rw [show b ^ q + b + 3 * b ^ q * b = b + b ^ q + 3 * b * b ^ q from by ring, hbq]
  simp only [M3_one]
  rw [show (fun j : Fin m => (dOf m c j) ^ q * dOf m c j) = fun _ => (1 : K) from
    funext fun j => hdq j]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [blockDiag, Dm, Matrix.one_apply]

private lemma cyc3_det : (StatedCenterThree.cyc3 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [StatedCenterThree.cyc3]

private lemma cyc3_pow_three : (StatedCenterThree.cyc3 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  rw [pow_three']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [StatedCenterThree.cyc3, Matrix.mul_apply, Fin.sum_univ_three]

private lemma ones3_mul_cyc3 :
    (ones3 : Matrix (Fin 3) (Fin 3) K) * StatedCenterThree.cyc3 = ones3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ones3, StatedCenterThree.cyc3, Matrix.mul_apply, Fin.sum_univ_three]

private lemma cyc3_mul_ones3 :
    StatedCenterThree.cyc3 * (ones3 : Matrix (Fin 3) (Fin 3) K) = ones3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ones3, StatedCenterThree.cyc3, Matrix.mul_apply, Fin.sum_univ_three]

private lemma M3_mul_cyc3 (b : K) :
    M3 b * StatedCenterThree.cyc3 = StatedCenterThree.cyc3 * M3 b := by
  simp only [M3, add_mul, mul_add, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    cyc3_mul_ones3, ones3_mul_cyc3]

private abbrev xmat : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K :=
  blockDiag (m := m) StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K))

private lemma xmat_det : (xmat (K := K) m).det = 1 := by
  change (blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K))).det = 1
  rw [blockDiag, Matrix.det_fromBlocks_zero₂₁, cyc3_det, Dm, Matrix.det_diagonal]
  simp

private lemma xmat_pow_three : (xmat (K := K) m) ^ 3 = 1 := by
  change (blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K))) ^ 3 = 1
  rw [blockDiag_pow, cyc3_pow_three]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [blockDiag, Dm, Matrix.one_apply]

private lemma map_cyc3 (σ : K →+* K) :
    (StatedCenterThree.cyc3 : Matrix (Fin 3) (Fin 3) K).map ⇑σ = StatedCenterThree.cyc3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [StatedCenterThree.cyc3, Matrix.map_apply]

private lemma xmat_unitary (σ : K →+* K) :
    ((xmat (K := K) m).map ⇑σ)ᵀ * (xmat (K := K) m) = 1 := by
  change ((blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K))).map ⇑σ)ᵀ *
    blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K)) = 1
  rw [blockDiag_map, map_cyc3, blockDiag_transpose, blockDiag_mul,
    StatedCenterThree.transpose_mul_cyc3]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [blockDiag, Dm, Matrix.one_apply, map_one]

private lemma val_mkOfDetNeZero {A : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K}
    (h : A.det ≠ 0) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero A h :
      Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) = A := by
  rw [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk']
  rfl

private noncomputable abbrev xGL : GL (Fin 3 ⊕ Fin m) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (xmat (K := K) m) (by rw [xmat_det]; exact one_ne_zero)

private lemma xGL_pow_three : (xGL (K := K) m) ^ 3 = 1 := by
  apply Units.ext
  change (xmat (K := K) m) ^ 3 = (1 : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)
  rw [xmat_pow_three]

private lemma xmat_offdiag : (xmat (K := K) m) (Sum.inl 0) (Sum.inl 1) = 1 := by
  change blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K))
    (Sum.inl 0) (Sum.inl 1) = 1
  simp [blockDiag, StatedCenterThree.cyc3]

private lemma xGL_not_scalar : (xGL (K := K) m) ∉ StatedScalars (Fin 3 ⊕ Fin m) K := by
  rintro ⟨u, hu⟩
  have h := congrFun (congrFun (congrArg (fun g : GL (Fin 3 ⊕ Fin m) K =>
    (g : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)) hu) (Sum.inl 0)) (Sum.inl 1)
  have hzero : (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
      Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) (Sum.inl 0) (Sum.inl 1) = 0 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne]
    simp
  rw [hzero, val_mkOfDetNeZero, xmat_offdiag] at h
  exact one_ne_zero h.symm

private lemma xGL_mem {q : ℕ} {σ : K →+* K} (hσ : ∀ x : K, σ x = x ^ q) :
    xGL (K := K) m ∈ CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q := by
  apply Subgroup.subset_closure
  simp only [Set.mem_ofPred_eq, val_mkOfDetNeZero]
  exact ⟨xmat_det m, by
    rw [show (fun x : K => x ^ q) = ⇑σ from funext fun x => (hσ x).symm, xmat_unitary]⟩

private noncomputable abbrev gGL (b : K) (c : Kˣ) (hb : 1 + 3 * b = (c : K)) :
    GL (Fin 3 ⊕ Fin m) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (gmat m b c) (by
    rw [gmat_det, hb]
    exact mul_ne_zero (Units.ne_zero c) (by simp))

private lemma gGL_mem {q : ℕ} {σ : K →+* K} (hσ : ∀ x : K, σ x = x ^ q)
    {c : Kˣ} (hc : c ^ (q + 1) = 1) {b : K} (hb : 1 + 3 * b = (c : K))
    (h3 : (3 : K) ≠ 0) :
    gGL m b c hb ∈ CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q := by
  apply Subgroup.subset_closure
  simp only [Set.mem_ofPred_eq, val_mkOfDetNeZero]
  refine ⟨?_, ?_⟩
  · rw [gmat_det, hb]
    simp
  · exact gmat_unitary m hσ hc hb h3

private lemma gmat_pow_apply (b : K) (c : Kˣ) (k : ℕ) :
    ((gmat m b c) ^ k) (Sum.inl 0) (Sum.inl 1) = bseq b k := by
  change ((blockDiag (M3 b) (dOf m c)) ^ k) (Sum.inl 0) (Sum.inl 1) = bseq b k
  rw [blockDiag_pow, M3_pow]
  simp [blockDiag, M3, ones3, Matrix.one_apply]

private lemma gmat_pow_eq_one_of {b : K} {c : Kˣ} (hb : 1 + 3 * b = (c : K))
    (h3 : (3 : K) ≠ 0) {k : ℕ} (hk : c ^ k = 1) : (gmat m b c) ^ k = 1 := by
  have hbseq : bseq b k = 0 := by
    have h := one_add_three_bseq b k
    rw [hb, ← Units.val_pow_eq_pow_val, hk, Units.val_one] at h
    have h5 : (3 : K) * bseq b k = 0 := by
      have h' : (1 : K) + 3 * bseq b k = 1 + 0 := by simpa using h
      exact add_left_cancel h'
    exact (mul_eq_zero.mp h5).resolve_left h3
  change (blockDiag (M3 b) (dOf m c)) ^ k = 1
  rw [blockDiag_pow, M3_pow, hbseq, M3_one]
  have hd : (fun j : Fin m => (dOf m c j) ^ k) = fun _ => (1 : K) := by
    funext j
    by_cases hj : j = 0
    · subst hj
      rw [show dOf m c 0 = ((c⁻¹ : Kˣ) : K) from rfl,
        show ((c⁻¹ : Kˣ) : K) = ((c : K))⁻¹ from by simp, inv_pow,
        ← Units.val_pow_eq_pow_val, hk, Units.val_one, inv_one]
    · rw [show dOf m c j = (1 : K) from by simp only [dOf]; simp [hj]]
      simp
  rw [hd]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [blockDiag, Dm, Matrix.one_apply]

private lemma gGL_pow_scalars_iff {b : K} {c : Kˣ} (hb : 1 + 3 * b = (c : K))
    (h3 : (3 : K) ≠ 0) (k : ℕ) :
    (gGL m b c hb) ^ k ∈ StatedScalars (Fin 3 ⊕ Fin m) K ↔ c ^ k = 1 := by
  constructor
  · intro hmem
    obtain ⟨u, hu⟩ := hmem
    have hzero : (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
        Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) (Sum.inl 0) (Sum.inl 1) = 0 := by
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne]
      simp
    have hbk : bseq b k = 0 := by
      have hmat := congrArg (fun g : GL (Fin 3 ⊕ Fin m) K =>
        (g : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)) hu
      have he := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inl 1)
      rw [hzero] at he
      rw [Units.val_pow_eq_pow_val] at he
      change 0 = (gmat m b c ^ k) (Sum.inl 0) (Sum.inl 1) at he
      rw [gmat_pow_apply] at he
      exact he.symm
    have hcK : (c : K) ^ k = 1 := by
      calc (c : K) ^ k = (1 + 3 * b) ^ k := by rw [hb]
        _ = 1 + 3 * bseq b k := (one_add_three_bseq b k).symm
        _ = 1 := by rw [hbk]; ring
    exact Units.ext hcK
  · intro hk
    have hpow1 : (gmat m b c) ^ k = 1 := gmat_pow_eq_one_of (m := m) hb h3 hk
    refine ⟨1, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_one]
    change (1 : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) = (gmat m b c) ^ k
    rw [hpow1]

private lemma gmat_mul_xmat (b : K) (c : Kˣ) :
    gmat m b c * xmat (K := K) m = xmat (K := K) m * gmat m b c := by
  change blockDiag (M3 b) (dOf m c) * blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K)) =
    blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K)) * blockDiag (M3 b) (dOf m c)
  rw [blockDiag_mul, blockDiag_mul, M3_mul_cyc3 b]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [blockDiag, Dm, dOf]

private abbrev scal3 (a : K) : Matrix (Fin 3) (Fin 3) K := diagonal (fun _ : Fin 3 => a)

private lemma scal3_pow (a : K) (k : ℕ) : (scal3 a) ^ k = scal3 (a ^ k) := by
  show (diagonal (fun _ : Fin 3 => a)) ^ k = diagonal (fun _ : Fin 3 => a ^ k)
  rw [Matrix.diagonal_pow]
  rfl

private lemma scal3_transpose (a : K) : (scal3 a)ᵀ = scal3 a := by
  show (diagonal (fun _ : Fin 3 => a))ᵀ = diagonal (fun _ : Fin 3 => a)
  rw [diagonal_transpose]

private lemma scal3_map (σ : K →+* K) (a : K) : (scal3 a).map ⇑σ = scal3 (σ a) := by
  show (diagonal (fun _ : Fin 3 => a)).map ⇑σ = diagonal (fun _ : Fin 3 => σ a)
  rw [diagonal_map (map_zero σ)]

private lemma scal3_mul (a b : K) : scal3 a * scal3 b = scal3 (a * b) := by
  show diagonal (fun _ : Fin 3 => a) * diagonal (fun _ : Fin 3 => b) =
    diagonal (fun _ : Fin 3 => a * b)
  rw [diagonal_mul_diagonal]

private lemma scal3_one : scal3 (1 : K) = 1 := by
  show diagonal (fun _ : Fin 3 => (1 : K)) = 1
  rw [diagonal_one]

private lemma scal3_det (a : K) : (scal3 a).det = a ^ 3 := by
  show (diagonal (fun _ : Fin 3 => a)).det = a ^ 3
  rw [Matrix.det_diagonal, Fin.prod_univ_three]
  ring

private abbrev dOfH (a : Kˣ) : Fin m → K :=
  fun j => if j = 0 then (((a⁻¹ : Kˣ) : K)) ^ 3 else 1

private abbrev hmat (a : Kˣ) : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K :=
  blockDiag (scal3 (a : K)) (dOfH m a)

private lemma prod_dOfH (a : Kˣ) : ∏ j : Fin m, dOfH m a j = (((a⁻¹ : Kˣ) : K)) ^ 3 := by
  rw [show dOfH m a = fun j : Fin m => if j = 0 then (((a⁻¹ : Kˣ) : K)) ^ 3 else 1 from rfl]
  exact Fintype.prod_ite_eq' 0 (fun _ => (((a⁻¹ : Kˣ) : K)) ^ 3)

private lemma hmat_det (a : Kˣ) : (hmat m a).det = 1 := by
  change (blockDiag (scal3 (a : K)) (dOfH m a)).det = 1
  rw [blockDiag, Matrix.det_fromBlocks_zero₂₁, scal3_det, Dm, Matrix.det_diagonal, prod_dOfH,
    show (((a⁻¹ : Kˣ) : K)) = ((a : K))⁻¹ from by simp, inv_pow,
    mul_inv_cancel₀ (pow_ne_zero 3 (Units.ne_zero a))]

private lemma hmat_unitary {q : ℕ} {σ : K →+* K} (hσ : ∀ x : K, σ x = x ^ q)
    {a : Kˣ} (ha : a ^ (q + 1) = 1) :
    ((hmat m a).map ⇑σ)ᵀ * (hmat m a) = 1 := by
  have haK : (a : K) ^ (q + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ha, Units.val_one]
  have hdq : ∀ j : Fin m, (dOfH m a j) ^ q * dOfH m a j = 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      rw [show dOfH m a 0 = (((a : K))⁻¹) ^ 3 from by simp [dOfH]]
      rw [← pow_succ]
      rw [← pow_mul, show 3 * (q + 1) = (q + 1) * 3 from by ring, pow_mul,
        show (((a : K))⁻¹) ^ (q + 1) = 1 from by rw [inv_pow, haK, inv_one], one_pow]
    · rw [show dOfH m a j = (1 : K) from by simp only [dOfH]; simp [hj]]
      simp
  change ((blockDiag (scal3 (a : K)) (dOfH m a)).map ⇑σ)ᵀ *
    blockDiag (scal3 (a : K)) (dOfH m a) = 1
  rw [blockDiag_map, scal3_map, blockDiag_transpose, scal3_transpose, blockDiag_mul,
    scal3_mul, show σ (a : K) = (a : K) ^ q from hσ _,
    show (a : K) ^ q * (a : K) = 1 from by rw [← pow_succ, haK], scal3_one]
  rw [show (fun j : Fin m => σ (dOfH m a j) * dOfH m a j) = fun _ => (1 : K) from
    funext fun j => by rw [hσ, hdq j]]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [blockDiag, Dm, Matrix.one_apply]

private lemma hmat_pow (a : Kˣ) (k : ℕ) :
    (hmat m a) ^ k = blockDiag (scal3 ((a : K) ^ k)) (fun j => (dOfH m a j) ^ k) := by
  change (blockDiag (scal3 (a : K)) (dOfH m a)) ^ k = _
  rw [blockDiag_pow, scal3_pow]

private lemma hmat_pow_eq_one_of {a : Kˣ} {k : ℕ} (hak : a ^ k = 1) : (hmat m a) ^ k = 1 := by
  have hakK : (a : K) ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hak, Units.val_one]
  rw [hmat_pow, hakK, scal3_one]
  have hd : (fun j : Fin m => (dOfH m a j) ^ k) = fun _ => (1 : K) := by
    funext j
    by_cases hj : j = 0
    · subst hj
      rw [show dOfH m a 0 = (((a : K))⁻¹) ^ 3 from by simp [dOfH]]
      rw [show ((((a : K))⁻¹) ^ 3) ^ k = ((((a : K)) ^ k)⁻¹) ^ 3 from by
        rw [← pow_mul, inv_pow, inv_pow, ← pow_mul]
        congr 1
        ring]
      rw [hakK]
      simp
    · rw [show dOfH m a j = (1 : K) from by simp only [dOfH]; simp [hj]]; simp
  rw [hd]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [blockDiag, Dm, Matrix.one_apply]

private noncomputable abbrev hGL (a : Kˣ) : GL (Fin 3 ⊕ Fin m) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (hmat m a) (by rw [hmat_det]; exact one_ne_zero)

private lemma hGL_mem {q : ℕ} {σ : K →+* K} (hσ : ∀ x : K, σ x = x ^ q)
    {a : Kˣ} (ha : a ^ (q + 1) = 1) :
    hGL m a ∈ CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q := by
  apply Subgroup.subset_closure
  simp only [Set.mem_ofPred_eq, val_mkOfDetNeZero]
  refine ⟨hmat_det m a, ?_⟩
  rw [show (fun x : K => x ^ q) = ⇑σ from funext fun x => (hσ x).symm]
  exact hmat_unitary m hσ ha

private lemma gmat_pow_mul_hmat_pow_offdiag (b : K) (c a : Kˣ) (p q : ℕ) :
    ((gmat m b c) ^ p * (hmat m a) ^ q) (Sum.inl 0) (Sum.inl 1) = (a : K) ^ q * bseq b p := by
  change ((blockDiag (M3 b) (dOf m c)) ^ p * (blockDiag (scal3 (a : K)) (dOfH m a)) ^ q)
    (Sum.inl 0) (Sum.inl 1) = (a : K) ^ q * bseq b p
  rw [blockDiag_pow, blockDiag_pow, M3_pow, scal3_pow, blockDiag_mul]
  show (∑ k : Fin 3, (M3 (bseq b p)) 0 k * (scal3 ((a : K) ^ q)) k 1) =
    (a : K) ^ q * bseq b p
  rw [Fin.sum_univ_three]
  simp [M3, ones3, scal3, Matrix.diagonal_apply]
  ring

private lemma gmat_pow_mul_hmat_pow_scalar_one {b : K} {c a : Kˣ}
    (hb : 1 + 3 * b = (c : K)) (h3 : (3 : K) ≠ 0) (haord : orderOf a = 5) {p q : ℕ}
    (hscal : ∃ u : Kˣ, (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
      Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) =
        (gmat m b c) ^ p * (hmat m a) ^ q) :
    (gmat m b c) ^ p = 1 ∧ (hmat m a) ^ q = 1 := by
  obtain ⟨u, hu⟩ := hscal
  have hoff := congrFun (congrFun hu (Sum.inl 0)) (Sum.inl 1)
  have hzero : (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
      Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) (Sum.inl 0) (Sum.inl 1) = 0 := by
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne]
    simp
  rw [hzero, gmat_pow_mul_hmat_pow_offdiag] at hoff
  have hbseq : bseq b p = 0 :=
    (mul_eq_zero.mp hoff.symm).resolve_left (pow_ne_zero _ (Units.ne_zero a))
  have hgp : (gmat m b c) ^ p = 1 := by
    apply gmat_pow_eq_one_of (m := m) hb h3
    have hcK : (c : K) ^ p = 1 := by
      calc (c : K) ^ p = (1 + 3 * b) ^ p := by rw [hb]
        _ = 1 + 3 * bseq b p := (one_add_three_bseq b p).symm
        _ = 1 := by rw [hbseq]; ring
    exact Units.ext hcK
  refine ⟨hgp, ?_⟩
  rw [hgp, one_mul] at hu
  have hdiag := congrFun (congrFun hu (Sum.inl 0)) (Sum.inl 0)
  have hdiag2 := congrFun (congrFun hu (Sum.inr 0)) (Sum.inr 0)
  rw [hmat_pow] at hdiag hdiag2
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_apply_eq] at hdiag hdiag2
  change (u : K) = (blockDiag (scal3 ((a : K) ^ q)) (fun j => (dOfH m a j) ^ q))
    (Sum.inl 0) (Sum.inl 0) at hdiag
  change (u : K) = (blockDiag (scal3 ((a : K) ^ q)) (fun j => (dOfH m a j) ^ q))
    (Sum.inr 0) (Sum.inr 0) at hdiag2
  rw [show (blockDiag (scal3 ((a : K) ^ q)) (fun j => (dOfH m a j) ^ q))
      (Sum.inl 0) (Sum.inl 0) = (a : K) ^ q from by
        simp [blockDiag, scal3, Matrix.diagonal_apply]] at hdiag
  rw [show (blockDiag (scal3 ((a : K) ^ q)) (fun j => (dOfH m a j) ^ q))
      (Sum.inr 0) (Sum.inr 0) = (((a : K))⁻¹) ^ (3 * q) from by
        simp [blockDiag, Dm, dOfH, Matrix.diagonal_apply, inv_pow, pow_mul]] at hdiag2
  have heq : (a : K) ^ q = (((a : K))⁻¹) ^ (3 * q) := hdiag.symm.trans hdiag2
  have haq : a ^ q = 1 := by
    have h4 : (a : K) ^ (4 * q) = 1 := by
      have hsplit : (4 : ℕ) * q = q + 3 * q := by ring
      rw [hsplit, pow_add, heq, ← mul_pow, inv_mul_cancel₀ (Units.ne_zero a), one_pow]
    have h4u : a ^ (4 * q) = 1 := Units.ext h4
    have hdvd : orderOf a ∣ 4 * q := orderOf_dvd_of_pow_eq_one h4u
    rw [haord] at hdvd
    have h5q : 5 ∣ q :=
      (Nat.Coprime.dvd_of_dvd_mul_right (by decide : Nat.Coprime 5 4))
        (by rwa [mul_comm] at hdvd)
    exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [haord]; exact h5q)
  rw [hmat_pow_eq_one_of (m := m) haq]
private lemma M3_mul_scal3 (b a : K) : M3 b * scal3 a = scal3 a * M3 b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M3, ones3, scal3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

private lemma gmat_mul_hmat (b : K) (c a : Kˣ) :
    gmat m b c * hmat m a = hmat m a * gmat m b c := by
  change blockDiag (M3 b) (dOf m c) * blockDiag (scal3 (a : K)) (dOfH m a) =
    blockDiag (scal3 (a : K)) (dOfH m a) * blockDiag (M3 b) (dOf m c)
  rw [blockDiag_mul, blockDiag_mul, M3_mul_scal3]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [blockDiag, Dm, dOf, dOfH, mul_comm]

private lemma gmat_offdiag (b : K) (c : Kˣ) :
    (gmat m b c) (Sum.inl 0) (Sum.inl 1) = b := by
  have := gmat_pow_apply m b c 1
  simpa [bseq] using this

private lemma hmat_diag_zero (a : Kˣ) :
    (hmat m a) (Sum.inl 0) (Sum.inl 0) = (a : K) := by
  change (blockDiag (scal3 (a : K)) (dOfH m a)) (Sum.inl 0) (Sum.inl 0) = (a : K)
  simp [blockDiag, scal3, Matrix.diagonal_apply]

private lemma gGL_pow_five {b : K} {c : Kˣ} (hb : 1 + 3 * b = (c : K)) (h3 : (3 : K) ≠ 0)
    (hc5 : c ^ 5 = 1) : (gGL m b c hb) ^ 5 = 1 := by
  apply Units.ext
  change (gmat m b c) ^ 5 = (1 : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)
  exact gmat_pow_eq_one_of (m := m) hb h3 hc5

private lemma gGL_ne_one {b : K} {c : Kˣ} (hb : 1 + 3 * b = (c : K)) (hbne : b ≠ 0) :
    gGL m b c hb ≠ 1 := by
  intro h
  have hmat : (gmat m b c) (Sum.inl 0) (Sum.inl 1) = 0 := by
    have := congrArg (fun z : GL (Fin 3 ⊕ Fin m) K =>
      (z : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) (Sum.inl 0) (Sum.inl 1)) h
    rw [val_mkOfDetNeZero (K := K)] at this
    simpa using this
  rw [gmat_offdiag] at hmat
  exact hbne hmat

private lemma hGL_pow_five {a : Kˣ} (ha5 : a ^ 5 = 1) : (hGL m a) ^ 5 = 1 := by
  apply Units.ext
  change (hmat m a) ^ 5 = (1 : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)
  exact hmat_pow_eq_one_of (m := m) ha5

private lemma hGL_ne_one {a : Kˣ} (ha1 : a ≠ 1) : hGL m a ≠ 1 := by
  intro h
  have hmat := congrArg (fun z : GL (Fin 3 ⊕ Fin m) K =>
    (z : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) (Sum.inl 0) (Sum.inl 0)) h
  rw [val_mkOfDetNeZero (K := K), hmat_diag_zero] at hmat
  exact ha1 (Units.ext (by simpa using hmat))
private lemma scal3_mul_cyc3 (a : K) :
    scal3 a * StatedCenterThree.cyc3 = StatedCenterThree.cyc3 * scal3 a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scal3, StatedCenterThree.cyc3, Matrix.mul_apply, Fin.sum_univ_three]

private lemma hmat_mul_xmat (a : Kˣ) :
    hmat m a * xmat (K := K) m = xmat (K := K) m * hmat m a := by
  change blockDiag (scal3 (a : K)) (dOfH m a) *
      blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K)) =
    blockDiag StatedCenterThree.cyc3 (fun _ : Fin m => (1 : K)) *
      blockDiag (scal3 (a : K)) (dOfH m a)
  rw [blockDiag_mul, blockDiag_mul, scal3_mul_cyc3]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [blockDiag, Dm, dOfH]

end Block

private theorem three_ne_zero_of_card_eq_sq {K : Type} [Field K] [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : q % 3 = 1) : (3 : K) ≠ 0 := by
  intro h0
  letI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : ringChar K = 3 := by
    have hdvd : ringChar K ∣ 3 := (CharP.cast_eq_zero_iff K (ringChar K) 3).mp h0
    exact (Nat.prime_dvd_prime_iff_eq (CharP.prime_ringChar (R := K)) Nat.prime_three).mp hdvd
  have h3card : (3 : ℕ) ∣ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    exact (prime_dvd_char_iff_dvd_card (R := K) 3).mp (by rw [hchar])
  have h3q : 3 ∣ q := by
    have h := h3card
    rw [hK] at h
    exact Nat.prime_three.dvd_of_dvd_pow h
  have hmod := Nat.dvd_iff_mod_eq_zero.mp h3q
  omega

private lemma commute_of_mem_zpowers {G : Type} [Group G] {g h : G} (hgh : Commute g h)
    {u v : G} (hu : u ∈ Subgroup.zpowers g) (hv : v ∈ Subgroup.zpowers h) : Commute u v := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  exact hgh.zpow_zpow m n

private theorem false_of_proj_unitaryCore {K : Type} [Field K] [Finite K] (m : ℕ) (hm : 1 ≤ m)
    {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : q % 3 = 1)
    (hC : CentHyp (StatedProj (CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q))) : False := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨σ, hσ⟩ := exists_frobenius_of_card_sq hK
  let σR : K →+* K := σ
  have hσR : ∀ x : K, σR x = x ^ q := hσ
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_card_eq_sq hK hq
  obtain ⟨c, hcorder⟩ := StatedCenterThree.exists_orderOf_eq hK
  have hc : c ^ (q + 1) = 1 := hcorder ▸ pow_orderOf_eq_one c
  let b : K := ((c : K) - 1) / 3
  have hb : 1 + 3 * b = (c : K) := by
    have h3 : (3 : K) ≠ 0 := h3K
    dsimp only [b]
    field_simp
    ring_nf
  let H := CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q
  let gH : H := ⟨gGL m b c hb, gGL_mem m hσR hc hb h3K⟩
  let xH : H := ⟨xGL (K := K) m, xGL_mem m hσR⟩
  have hx : orderOf (QuotientGroup.mk xH : StatedProj H) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_mk_eq_prime xH ?_ ?_
    · have h3 : (xH : GL (Fin 3 ⊕ Fin m) K) ^ 3 = 1 := by
        rw [show (xH : GL (Fin 3 ⊕ Fin m) K) = xGL (K := K) m from rfl, xGL_pow_three]
      rw [h3]
      exact ⟨1, map_one (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m))⟩
    · intro hmem
      exact xGL_not_scalar m (by
        rwa [show (xH : GL (Fin 3 ⊕ Fin m) K) = xGL (K := K) m from rfl] at hmem)
  have hg : orderOf (QuotientGroup.mk gH : StatedProj H) = q + 1 := by
    refine orderOf_mk_eq gH (q + 1) ?_
    intro k
    rw [show (gH : GL (Fin 3 ⊕ Fin m) K) = gGL m b c hb from rfl]
    rw [gGL_pow_scalars_iff m hb h3K k, ← orderOf_dvd_iff_pow_eq_one, hcorder]
  have hgx : gH * xH = xH * gH := by
    apply Subtype.ext
    apply Units.ext
    change (gmat m b c) * (xmat (K := K) m) = (xmat (K := K) m) * (gmat m b c)
    exact gmat_mul_xmat m b c
  have hcomm : (QuotientGroup.mk gH : StatedProj H) * (QuotientGroup.mk xH) =
      (QuotientGroup.mk xH) * (QuotientGroup.mk gH) := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hgx]
  have hmem := CentHyp.orderOf_mem hC hx hcomm
  rw [hg] at hmem
  have hq4 : q = 4 := by
    have h2 : 2 ≤ q := StatedCenterThree.two_le_of_card_eq_sq hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  by_cases h4 : q = 4
  · subst h4
    have hc5 : c ^ 5 = 1 := by simpa using hc
    have hc1 : c ≠ 1 := by
      intro hc1
      rw [hc1, orderOf_one] at hcorder
      omega
    have hbne : b ≠ 0 := by
      intro hb0
      apply hc1
      apply Units.ext
      change (c : K) = 1
      rw [← hb, hb0]
      ring
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hgordGL : orderOf (gGL m b c hb) = 5 :=
      orderOf_eq_prime (gGL_pow_five m hb h3K hc5) (gGL_ne_one m hb hbne)
    have hhordGL : orderOf (hGL m c) = 5 :=
      orderOf_eq_prime (hGL_pow_five m hc5) (hGL_ne_one m hc1)
    have haord : orderOf c = 5 := by simpa using hcorder
    let hEl : H := ⟨hGL m c, hGL_mem m hσR hc⟩
    have hgord : orderOf gH = 5 := by
      rw [← orderOf_coe gH, show (gH : GL (Fin 3 ⊕ Fin m) K) = gGL m b c hb from rfl]
      exact hgordGL
    have hhord : orderOf hEl = 5 := by
      rw [← orderOf_coe hEl, show (hEl : GL (Fin 3 ⊕ Fin m) K) = hGL m c from rfl]
      exact hhordGL
    have hxg : Commute gH xH := hgx
    have hgh : Commute gH hEl := by
      apply Subtype.ext
      apply Units.ext
      change (gmat m b c) * (hmat m c) = (hmat m c) * (gmat m b c)
      exact gmat_mul_hmat m b c c
    have hxh : Commute hEl xH := by
      apply Subtype.ext
      apply Units.ext
      change (hmat m c) * (xmat (K := K) m) = (xmat (K := K) m) * (hmat m c)
      exact hmat_mul_xmat m c
    have hmatprod : ∀ p q : ℕ, ((gH ^ p * hEl ^ q : H) : GL (Fin 3 ⊕ Fin m) K) =
        (gGL m b c hb) ^ p * (hGL m c) ^ q := by
      intro p q
      rw [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow]
    have hmatprod2 : ∀ p q : ℕ,
        ((((gGL m b c hb) ^ p * (hGL m c) ^ q : GL (Fin 3 ⊕ Fin m) K)) :
          Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) =
        (gmat m b c) ^ p * (hmat m c) ^ q := by
      intro p q
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        val_mkOfDetNeZero (K := K), val_mkOfDetNeZero (K := K)]
    have hnat_g : ∀ w : H, w ∈ Subgroup.zpowers gH → ∃ p : ℕ, w = gH ^ p := by
      intro w hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
      refine ⟨(i % 5).toNat, ?_⟩
      rw [← hi, ← zpow_mod_orderOf, hgord, ← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))).symm
    have hnat_h : ∀ w : H, w ∈ Subgroup.zpowers hEl → ∃ p : ℕ, w = hEl ^ p := by
      intro w hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hw
      refine ⟨(i % 5).toNat, ?_⟩
      rw [← hi, ← zpow_mod_orderOf, hhord, ← zpow_natCast]
      congr 1
      exact (Int.toNat_of_nonneg (Int.emod_nonneg i (by norm_num))).symm
    have hker_s : ∀ p q : ℕ, (∃ u : Kˣ, (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
        Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) =
          (gmat m b c) ^ p * (hmat m c) ^ q) → gH ^ p = 1 ∧ hEl ^ q = 1 := by
      intro p q hscal
      obtain ⟨hgp, hhq⟩ := gmat_pow_mul_hmat_pow_scalar_one (m := m) hb h3K haord hscal
      constructor
      · apply Subtype.ext; apply Units.ext
        change (gmat m b c) ^ p = (1 : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)
        exact hgp
      · apply Subtype.ext; apply Units.ext
        change (hmat m c) ^ q = (1 : Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)
        exact hhq
    have hker : ∀ p q : ℕ, gH ^ p * hEl ^ q = 1 → gH ^ p = 1 ∧ hEl ^ q = 1 := by
      intro p q h1
      apply hker_s p q
      refine ⟨1, ?_⟩
      rw [map_one]
      have hmat1 : (gmat m b c) ^ p * (hmat m c) ^ q = 1 := by
        have := congrArg (fun z : H => ((z : GL (Fin 3 ⊕ Fin m) K) :
          Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K)) h1
        rwa [hmatprod p q, hmatprod2 p q] at this
      exact hmat1.symm
    have hcommf : ∀ u v, Commute ((Subgroup.zpowers gH).subtype u) ((Subgroup.zpowers hEl).subtype v) :=
      fun u v => commute_of_mem_zpowers hgh u.2 v.2
    let Φ : ↥(Subgroup.zpowers gH) × ↥(Subgroup.zpowers hEl) →* H :=
      MonoidHom.noncommCoprod (Subgroup.zpowers gH).subtype (Subgroup.zpowers hEl).subtype hcommf
    let A : Subgroup H := Φ.range
    have hΦapp : ∀ u v, Φ (u, v) = (u : H) * (v : H) := fun u v => rfl
    have hinj : Function.Injective Φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      obtain ⟨p, hp⟩ := hnat_g x.1 x.1.2
      obtain ⟨q, hq⟩ := hnat_h x.2 x.2.2
      have h1 : gH ^ p * hEl ^ q = 1 := by
        rw [← hp, ← hq, ← hΦapp]
        exact hx
      obtain ⟨hgp, hhq⟩ := hker p q h1
      rw [Subgroup.mem_bot]
      exact Prod.ext (Subtype.ext (hp.trans hgp)) (Subtype.ext (hq.trans hhq))
    have hcard : Nat.card A = 25 := by
      rw [show A = Φ.range from rfl, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      rw [Nat.card_prod, Nat.card_zpowers, hgord, Nat.card_zpowers, hhord]
    have hAx : ∀ a ∈ A, a * xH = xH * a := by
      intro a ha
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨p, hp⟩ := hnat_g x.1 x.1.2
      obtain ⟨q, hq⟩ := hnat_h x.2 x.2.2
      have haeq : Φ x = gH ^ p * hEl ^ q := by rw [hΦapp, hp, hq]
      rw [haeq]
      exact ((hxg.pow_left p).mul_left (hxh.pow_left q)).eq
    have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
      intro a ha b hb
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      obtain ⟨p, hp⟩ := hnat_g x.1 x.1.2
      obtain ⟨q, hq⟩ := hnat_h x.2 x.2.2
      obtain ⟨r, hr⟩ := hnat_g y.1 y.1.2
      obtain ⟨s, hs⟩ := hnat_h y.2 y.2.2
      have hx : Φ x = gH ^ p * hEl ^ q := by rw [hΦapp, hp, hq]
      have hy : Φ y = gH ^ r * hEl ^ s := by rw [hΦapp, hr, hs]
      rw [hx, hy]
      have h1 : Commute (gH ^ p * hEl ^ q) (gH ^ r * hEl ^ s) :=
        ((Commute.pow_pow_self gH p r).mul_left (hgh.symm.pow_pow q r)).mul_right
          ((hgh.pow_pow p s).mul_left (Commute.pow_pow_self hEl q s))
      exact h1.eq
    have hAZ : ∀ a ∈ A, (a : GL (Fin 3 ⊕ Fin m) K) ∈ StatedScalars (Fin 3 ⊕ Fin m) K →
        a = 1 := by
      intro a ha hscal
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨p, hp⟩ := hnat_g x.1 x.1.2
      obtain ⟨q, hq⟩ := hnat_h x.2 x.2.2
      have haeq : Φ x = gH ^ p * hEl ^ q := by rw [hΦapp, hp, hq]
      rw [haeq] at hscal
      have hgl : (gGL m b c hb) ^ p * (hGL m c) ^ q ∈ StatedScalars (Fin 3 ⊕ Fin m) K := by
        rw [← hmatprod p q]
        exact hscal
      obtain ⟨u, hu⟩ := hgl
      have hscal' : ∃ u : Kˣ, (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
          Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) =
            (gmat m b c) ^ p * (hmat m c) ^ q := by
        refine ⟨u, ?_⟩
        rw [show (Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u :
          Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) =
            (((Matrix.GeneralLinearGroup.scalar (Fin 3 ⊕ Fin m) u : GL (Fin 3 ⊕ Fin m) K)) :
              Matrix (Fin 3 ⊕ Fin m) (Fin 3 ⊕ Fin m) K) from rfl]
        rw [hu, hmatprod2 p q]
      obtain ⟨hgp, hhq⟩ := hker_s p q hscal'
      rw [haeq, show gH ^ p * hEl ^ q = 1 from by rw [hgp, hhq, one_mul]]
    have hle := CentHyp.card_le_of_proj hC hx hAx hAab hAZ
    rw [hcard] at hle
    omega
  · exact h4 hq4

private lemma reindex_map_apply {ι κ : Type} [Fintype ι] (e : ι ≃ κ) (f : K → K)
    (A : Matrix ι ι K) :
    (Matrix.reindex e e A).map f = Matrix.reindex e e (A.map f) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.map_apply]

private noncomputable abbrev reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) : GL ι K ≃* GL κ K :=
  Units.mapEquiv (Matrix.reindexRingEquiv K e).toMulEquiv

private lemma reindexGL_val {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) :
    (reindexGL e g : Matrix κ κ K) = Matrix.reindex e e (g : Matrix ι ι K) := rfl

private lemma reindexGL_scalar {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (c : Kˣ) :
    reindexGL e (Matrix.GeneralLinearGroup.scalar ι c) =
      Matrix.GeneralLinearGroup.scalar κ c := by
  apply Units.ext
  rw [reindexGL_val]
  change Matrix.reindex e e (Matrix.scalar ι (c : K)) = Matrix.scalar κ (c : K)
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  change (diagonal (fun _ : ι => (c : K))).submatrix e.symm e.symm =
    diagonal (fun _ : κ => (c : K))
  rw [Matrix.submatrix_diagonal (fun _ : ι => (c : K)) e.symm e.symm.injective]
  rfl

private lemma reindex_cond_fwd {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) {q : ℕ} {A : GL ι K}
    (hA : (A : Matrix ι ι K).det = 1 ∧
      (((A : Matrix ι ι K).map (· ^ q))ᵀ * (A : Matrix ι ι K) = 1)) :
    (reindexGL e A : Matrix κ κ K).det = 1 ∧
      ((((reindexGL e A : GL κ K) : Matrix κ κ K).map (· ^ q))ᵀ *
        (reindexGL e A : Matrix κ κ K) = 1) := by
  constructor
  · rw [reindexGL_val, Matrix.det_reindex_self]
    exact hA.1
  · have h := congrArg (Matrix.reindexRingEquiv K e) hA.2
    rw [map_mul, map_one] at h
    rw [reindexGL_val]
    change ((Matrix.reindex e e (A : Matrix ι ι K)).map (· ^ q))ᵀ *
      Matrix.reindex e e (A : Matrix ι ι K) = 1
    rw [reindex_map_apply, Matrix.transpose_reindex]
    exact h

private theorem map_unitaryCore_reindex_gen {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (q : ℕ) :
    (CFSG.MatrixModel.unitaryCore ι K q).map (reindexGL e).toMonoidHom =
      CFSG.MatrixModel.unitaryCore κ K q := by
  rw [CFSG.MatrixModel.unitaryCore, CFSG.MatrixModel.unitaryCore, MonoidHom.map_closure]
  congr 1
  ext B
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact reindex_cond_fwd e hA
  · intro hB
    refine ⟨(reindexGL e).symm B, ?_, ?_⟩
    · rw [Units.mapEquiv_symm]
      exact reindex_cond_fwd e.symm hB
    · exact MulEquiv.apply_symm_apply (reindexGL e) B

private theorem map_statedScalars_reindex_gen {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) :
    (StatedScalars ι K).map (reindexGL e).toMonoidHom = StatedScalars κ K := by
  rw [StatedScalars, StatedScalars, MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro c
  exact reindexGL_scalar e c

private noncomputable def proj_unitaryCore_reindex (m : ℕ) (q : ℕ) :
    StatedProj (StatedSU (3 + m) q K) ≃*
      StatedProj (CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q) := by
  let e : Fin (3 + m) ≃ Fin 3 ⊕ Fin m := (finSumFinEquiv (m := 3) (n := m)).symm
  let eSU : StatedSU (3 + m) q K ≃*
      CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q :=
    (reindexGL e).subgroupMap (StatedSU (3 + m) q K) |>.trans
      (MulEquiv.subgroupCongr (map_unitaryCore_reindex_gen (K := K) e q))
  have hcoe : ∀ y : StatedSU (3 + m) q K,
      (eSU y : GL (Fin 3 ⊕ Fin m) K) = reindexGL e (y : GL (Fin (3 + m)) K) := by
    intro y
    rfl
  have hSZ : ((StatedScalars (Fin (3 + m)) K).subgroupOf (StatedSU (3 + m) q K)).map eSU =
      (StatedScalars (Fin 3 ⊕ Fin m) K).subgroupOf
        (CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hmap : reindexGL e (y : GL (Fin (3 + m)) K) ∈
          (StatedScalars (Fin (3 + m)) K).map (reindexGL e).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rw [map_statedScalars_reindex_gen (K := K) e] at hmap
      change reindexGL e (y : GL (Fin (3 + m)) K) ∈ StatedScalars (Fin 3 ⊕ Fin m) K
      exact hmap
    · intro hx
      have hxU : (x : GL (Fin 3 ⊕ Fin m) K) ∈
          CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q := x.2
      have hxu : reindexGL e.symm (x : GL (Fin 3 ⊕ Fin m) K) ∈
          CFSG.MatrixModel.unitaryCore (Fin (3 + m)) K q := by
        have hmap := Subgroup.mem_map_of_mem (reindexGL e.symm).toMonoidHom hxU
        rwa [map_unitaryCore_reindex_gen (K := K) e.symm q] at hmap
      have hxs : reindexGL e.symm (x : GL (Fin 3 ⊕ Fin m) K) ∈
          StatedScalars (Fin (3 + m)) K := by
        have hmap := Subgroup.mem_map_of_mem (reindexGL e.symm).toMonoidHom hx
        rwa [map_statedScalars_reindex_gen (K := K) e.symm] at hmap
      refine ⟨⟨reindexGL e.symm (x : GL (Fin 3 ⊕ Fin m) K), ?_⟩, hxs, ?_⟩
      · change reindexGL e.symm (x : GL (Fin 3 ⊕ Fin m) K) ∈
          CFSG.MatrixModel.unitaryCore (Fin (3 + m)) K q
        exact hxu
      · apply Subtype.ext
        show (eSU ⟨reindexGL e.symm (x : GL (Fin 3 ⊕ Fin m) K), _⟩ :
          GL (Fin 3 ⊕ Fin m) K) = (x : GL (Fin 3 ⊕ Fin m) K)
        rw [hcoe]
        exact MulEquiv.apply_symm_apply _ _
  exact QuotientGroup.congr
    (G' := (StatedScalars (Fin (3 + m)) K).subgroupOf (StatedSU (3 + m) q K))
    (H' := (StatedScalars (Fin 3 ⊕ Fin m) K).subgroupOf
      (CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q)) eSU hSZ

private theorem false_of_proj_unitaryCore_of_standard (m : ℕ) (hm : 1 ≤ m)
    {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hq : q % 3 = 1)
    (hC : CentHyp (StatedProj (StatedSU (3 + m) q K))) : False := by
  have hC' : CentHyp (StatedProj (CFSG.MatrixModel.unitaryCore (Fin 3 ⊕ Fin m) K q)) :=
    CentHyp.of_mulEquiv (proj_unitaryCore_reindex (K := K) m q).symm hC
  exact false_of_proj_unitaryCore m hm hK hq hC'

theorem false_of_psu_four {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : q % 3 = 1) (hC : CentHyp (StatedProj (StatedSU 4 q K))) : False :=
  false_of_proj_unitaryCore_of_standard 1 (by norm_num) hK hq hC

theorem false_of_psu_five {K : Type} [Field K] [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2)
    (hq : q % 3 = 1) (hC : CentHyp (StatedProj (StatedSU 5 q K))) : False :=
  false_of_proj_unitaryCore_of_standard 2 (by norm_num) hK hq hC

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
