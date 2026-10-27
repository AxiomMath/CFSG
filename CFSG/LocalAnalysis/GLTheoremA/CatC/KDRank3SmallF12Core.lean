module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Mat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Core

open Matrix Module CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Mat

variable {K : Type} [Field K]

noncomputable def colMat (b : Basis (Fin 3) K (Fin 3 → K)) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => b j i

theorem colMat_isUnit (b : Basis (Fin 3) K (Fin 3 → K)) : IsUnit (colMat b).det := by
  have h : colMat b = (Pi.basisFun K (Fin 3)).toMatrix b := by
    ext i j
    simp [colMat, Basis.toMatrix_apply]
  rw [h, ← Basis.det_apply]
  exact (Pi.basisFun K (Fin 3)).isUnit_det b

@[expose] def signD (s : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal fun i : Fin 3 => if i = 0 then s else -s

theorem mul_colMat_eq {B : Matrix (Fin 3) (Fin 3) K} {s : K} (b : Basis (Fin 3) K (Fin 3 → K))
    (hpat : ∀ i : Fin 3, B *ᵥ b i = (if i = 0 then s else -s) • b i) :
    B * colMat b = colMat b * signD s := by
  ext i j
  have hj : (B *ᵥ b j) i = (if j = 0 then s else -s) * b j i := by
    rw [hpat j]
    simp [Pi.smul_apply, smul_eq_mul]
  have hL : (B * colMat b) i j = (B *ᵥ b j) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, colMat]
  have hR : (colMat b * signD s) i j = (if j = 0 then s else -s) * b j i := by
    simp [Matrix.mul_apply, signD, colMat, Matrix.diagonal_apply, mul_comm]
  rw [hL, hj, hR]

theorem zeros_of_comm_signD {s : K} (hs : s ≠ 0) (h2 : (2 : K) ≠ 0)
    {X : Matrix (Fin 3) (Fin 3) K} (hX : X * signD s = signD s * X) :
    X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 1 0 = 0 ∧ X 2 0 = 0 := by
  have e01 : X 0 1 * (-s) = s * X 0 1 := by
    have := congrFun (congrFun hX 0) 1
    simpa [Matrix.mul_apply, signD, Matrix.diagonal_apply, Fin.sum_univ_three] using this
  have e02 : X 0 2 * (-s) = s * X 0 2 := by
    have := congrFun (congrFun hX 0) 2
    simpa [Matrix.mul_apply, signD, Matrix.diagonal_apply, Fin.sum_univ_three] using this
  have e10 : X 1 0 * s = -s * X 1 0 := by
    have := congrFun (congrFun hX 1) 0
    simpa [Matrix.mul_apply, signD, Matrix.diagonal_apply, Fin.sum_univ_three] using this
  have e20 : X 2 0 * s = -s * X 2 0 := by
    have := congrFun (congrFun hX 2) 0
    simpa [Matrix.mul_apply, signD, Matrix.diagonal_apply, Fin.sum_univ_three] using this
  have hne : (2 * s : K) ≠ 0 := mul_ne_zero h2 hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (2 * s) * X 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.1 this).resolve_left hne
  · have : (2 * s) * X 0 2 = 0 := by linear_combination -e02
    exact (mul_eq_zero.1 this).resolve_left hne
  · have : (2 * s) * X 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_left hne
  · have : (2 * s) * X 2 0 = 0 := by linear_combination e20
    exact (mul_eq_zero.1 this).resolve_left hne

@[expose] def IsBlk (X : Matrix (Fin 3) (Fin 3) K) : Prop :=
  X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 1 0 = 0 ∧ X 2 0 = 0

@[expose] def blk (N : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 2) (Fin 2) K :=
  !![N 1 1, N 1 2; N 2 1, N 2 2]

theorem blk_mul {X Y : Matrix (Fin 3) (Fin 3) K} (hX : IsBlk X) (hY : IsBlk Y) :
    blk (X * Y) = blk X * blk Y := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  obtain ⟨y1, y2, y3, y4⟩ := hY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, x1, x2, x3, x4, y1, y2, y3, y4]

theorem isBlk_mul {X Y : Matrix (Fin 3) (Fin 3) K} (hX : IsBlk X) (hY : IsBlk Y) :
    IsBlk (X * Y) := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  obtain ⟨y1, y2, y3, y4⟩ := hY
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, x1, x2, x3, x4, y1, y2, y3, y4]

theorem isBlk_one : IsBlk (1 : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.one_apply]

theorem blk_one : blk (1 : Matrix (Fin 3) (Fin 3) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.one_apply]

theorem isBlk_sub_one {X : Matrix (Fin 3) (Fin 3) K} (hX : IsBlk X) : IsBlk (X - 1) := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Matrix.one_apply, x1, x2, x3, x4]

theorem blk_sub_one (N : Matrix (Fin 3) (Fin 3) K) : blk (N - 1) = blk N - 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk, Matrix.one_apply]

theorem eq_of_isBlk {X Y : Matrix (Fin 3) (Fin 3) K} (hX : IsBlk X) (hY : IsBlk Y)
    (h00 : X 0 0 = Y 0 0) (hb : blk X = blk Y) : X = Y := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  obtain ⟨y1, y2, y3, y4⟩ := hY
  have hb00 := congrFun (congrFun hb 0) 0
  have hb01 := congrFun (congrFun hb 0) 1
  have hb10 := congrFun (congrFun hb 1) 0
  have hb11 := congrFun (congrFun hb 1) 1
  simp only [blk, of_apply, cons_val', cons_val_zero, cons_val_one, head_cons, empty_val',
    cons_val_fin_one] at hb00 hb01 hb10 hb11
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact x1.trans y1.symm
  · exact x2.trans y2.symm
  · exact x3.trans y3.symm
  · exact hb00
  · exact hb01
  · exact x4.trans y4.symm
  · exact hb10
  · exact hb11

theorem three_matrix_eq_zero {n : Type} [Fintype n] [DecidableEq n] (h3 : (3 : K) = 0) :
    (3 : Matrix n n K) = 0 := by
  have : (3 : Matrix n n K) = (3 : K) • (1 : Matrix n n K) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply, Matrix.ofNat_apply]
    · simp [Matrix.one_apply, hij, Matrix.ofNat_apply]
  rw [this, h3, zero_smul]


theorem sub_one_pow3 {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n K) (h3 : (3 : K) = 0) :
    (X - 1) ^ 3 = X ^ 3 - 1 := by
  have e : (3 : Matrix n n K) = 0 := three_matrix_eq_zero h3
  calc (X - 1) ^ 3 = X ^ 3 - 3 * X ^ 2 + 3 * X - 1 := by noncomm_ring
    _ = X ^ 3 - 1 := by rw [e]; simp

theorem eq_one_of_pow_three {x : K} (h3 : (3 : K) = 0) (hx : x ^ 3 = 1) : x = 1 := by
  have : (x - 1) ^ 3 = 0 := by
    have : (x - 1) ^ 3 = x ^ 3 - 3 * x ^ 2 + 3 * x - 1 := by ring
    rw [this, hx, h3]
    ring
  have := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 this
  exact sub_eq_zero.1 this

theorem comm_block_scalar {M G : Matrix (Fin 2) (Fin 2) K} (h2 : (2 : K) ≠ 0) (hG0 : G ≠ 0)
    (hGtr : G 0 0 + G 1 1 = 0) (hMG : M * G = G * M) (hMtr : M 0 0 + M 1 1 = 0) :
    ∃ β : K, M = β • G := by
  have hG : G = !![G 0 0, G 0 1; G 1 0, G 1 1] := Matrix.eta_fin_two G
  have hnon : G 0 1 ≠ 0 ∨ G 1 0 ≠ 0 ∨ G 0 0 ≠ G 1 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hq, hr, hp⟩ := hcon
    apply hG0
    have hp0 : G 0 0 = 0 := by
      have : (2 : K) * G 0 0 = 0 := by linear_combination hGtr + hp
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [hG, hp0, hq, hr, ← hp]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hp0, hq, hr]
  have hMG' : M * !![G 0 0, G 0 1; G 1 0, G 1 1] = !![G 0 0, G 0 1; G 1 0, G 1 1] * M := by
    rw [← hG]; exact hMG
  obtain ⟨α, β, hab⟩ := comm2_mem_span hnon hMG'
  have htr := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0 + A 1 1) hab
  simp at htr
  have hα : α = 0 := by
    have : (2 : K) * α = 0 := by linear_combination hMtr - htr - β * hGtr
    exact (mul_eq_zero.1 this).resolve_left h2
  refine ⟨β, ?_⟩
  rw [hab, hα, zero_smul, zero_add, ← hG]


theorem blk_zero : blk (0 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem blk_smul (c : K) (N : Matrix (Fin 3) (Fin 3) K) : blk (c • N) = c • blk N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem isBlk_smul (c : K) {N : Matrix (Fin 3) (Fin 3) K} (hN : IsBlk N) : IsBlk (c • N) := by
  obtain ⟨x1, x2, x3, x4⟩ := hN
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [x1, x2, x3, x4]

theorem isBlk_zero : IsBlk (0 : Matrix (Fin 3) (Fin 3) K) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem pow3_entry00 {X : Matrix (Fin 3) (Fin 3) K} (hX : IsBlk X) :
    (X ^ 3) 0 0 = X 0 0 ^ 3 := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, x1, x2, x3, x4]

theorem cayley2 (X : Matrix (Fin 2) (Fin 2) K) :
    X * X = (X 0 0 + X 1 1) • X - (X 0 0 * X 1 1 - X 0 1 * X 1 0) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem frame_block {B : Matrix (Fin 3) (Fin 3) K} (hK : ringChar K ≠ 2) (hB : B * B = 1)
    (hB1 : B ≠ 1) (hBm : B ≠ -1) :
    ∃ Q Qi : Matrix (Fin 3) (Fin 3) K, ∃ s : K, Q * Qi = 1 ∧ Qi * Q = 1 ∧ s * s = 1 ∧
      Qi * B * Q = signD s ∧ ∀ x : Matrix (Fin 3) (Fin 3) K, x * B = B * x → IsBlk (Qi * x * Q) := by
  classical
  obtain ⟨b, s, hs, hpat⟩ := eigen_pattern hK hB hB1 hBm
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_mul] at hs; exact zero_ne_one hs
  have hQu := colMat_isUnit b
  have hBQ := mul_colMat_eq b hpat
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  set Q := colMat b with hQdef
  have hQQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hQiQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  set Qi := Q⁻¹ with hQidef
  have hQiBQ : Qi * B * Q = signD s := by
    calc Qi * B * Q = Qi * (B * Q) := by simp only [mul_assoc]
      _ = Qi * (Q * signD s) := by rw [hBQ]
      _ = (Qi * Q) * signD s := by simp only [mul_assoc]
      _ = signD s := by rw [hQiQ, one_mul]
  refine ⟨Q, Qi, s, hQQi, hQiQ, hs, hQiBQ, ?_⟩
  intro x hx
  have hQiB : Qi * B = signD s * Qi := by
    calc Qi * B = Qi * B * (Q * Qi) := by rw [hQQi, mul_one]
      _ = (Qi * B * Q) * Qi := by simp only [mul_assoc]
      _ = signD s * Qi := by rw [hQiBQ]
  have hXcomm : (Qi * x * Q) * signD s = signD s * (Qi * x * Q) := by
    calc (Qi * x * Q) * signD s = Qi * x * (Q * signD s) := by simp only [mul_assoc]
      _ = Qi * x * (B * Q) := by rw [hBQ]
      _ = Qi * (x * B) * Q := by simp only [mul_assoc]
      _ = Qi * (B * x) * Q := by rw [hx]
      _ = (Qi * B) * x * Q := by simp only [mul_assoc]
      _ = (signD s * Qi) * x * Q := by rw [hQiB]
      _ = signD s * (Qi * x * Q) := by simp only [mul_assoc]
  obtain ⟨z1, z2, z3, z4⟩ := zeros_of_comm_signD hs0 h2 hXcomm
  exact ⟨z1, z2, z3, z4⟩

theorem det_of_isBlk {X : Matrix (Fin 3) (Fin 3) K} (hX : IsBlk X) :
    X.det = X 0 0 * (X 1 1 * X 2 2 - X 1 2 * X 2 1) := by
  obtain ⟨x1, x2, x3, x4⟩ := hX
  rw [Matrix.det_fin_three, x1, x2, x3, x4]
  ring


theorem blk_cube {M : Matrix (Fin 3) (Fin 3) K} (hM : IsBlk M) :
    blk (M * M * M) = blk M * blk M * blk M := by
  rw [blk_mul (isBlk_mul hM hM) hM, blk_mul hM hM]


theorem f2_core (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0) (F₀ : Subfield K)
    (hF₀ : Nat.card F₀ = 3) (P : Finset (Matrix (Fin 3) (Fin 3) K))
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPF : ∀ x ∈ P, ∀ i j, x i j ∈ F₀) (hPcard : 3 < P.card)
    (B : Matrix (Fin 3) (Fin 3) K) (hB : B * B = 1) (hB1 : B ≠ 1) (hBm : B ≠ -1)
    (hBP : ∀ x ∈ P, B * x = x * B) : False := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨b, s, hs, hpat⟩ := eigen_pattern hK hB hB1 hBm
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_mul] at hs; exact zero_ne_one hs
  have hQu := colMat_isUnit b
  have hBQ := mul_colMat_eq b hpat
  set Q := colMat b with hQdef
  set D := signD s with hDdef
  have hQQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hQiQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  set Qi := Q⁻¹ with hQidef
  have hconj_mul : ∀ y z : Matrix (Fin 3) (Fin 3) K,
      (Qi * y * Q) * (Qi * z * Q) = Qi * (y * z) * Q := by
    intro y z
    calc (Qi * y * Q) * (Qi * z * Q) = Qi * y * (Q * Qi) * z * Q := by simp only [mul_assoc]
      _ = Qi * (y * z) * Q := by rw [hQQi]; simp only [mul_one, mul_assoc]
  have hconj_pow : ∀ (x : Matrix (Fin 3) (Fin 3) K) (n : ℕ),
      (Qi * x * Q) ^ (n + 1) = Qi * x ^ (n + 1) * Q := by
    intro x n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ (Qi * x * Q) (k + 1), ih, hconj_mul, pow_succ x (k + 1)]
  have hconj_sub : ∀ y : Matrix (Fin 3) (Fin 3) K, Q * (Qi * y * Q - 1) * Qi = y - 1 := by
    intro y
    calc Q * (Qi * y * Q - 1) * Qi = Q * (Qi * y * Q) * Qi - Q * Qi := by
          rw [mul_sub, sub_mul, mul_one]
      _ = (Q * Qi) * y * (Q * Qi) - Q * Qi := by simp only [mul_assoc]
      _ = y - 1 := by rw [hQQi, one_mul, mul_one]
  have hQiB : Qi * B = D * Qi := by
    calc Qi * B = Qi * B * (Q * Qi) := by rw [hQQi, mul_one]
      _ = Qi * (B * Q) * Qi := by simp only [mul_assoc]
      _ = Qi * (Q * D) * Qi := by rw [hBQ]
      _ = (Qi * Q) * D * Qi := by simp only [mul_assoc]
      _ = D * Qi := by rw [hQiQ, one_mul]
  have hXcomm : ∀ x ∈ P, (Qi * x * Q) * D = D * (Qi * x * Q) := by
    intro x hx
    have hxB : x * B = B * x := (hBP x hx).symm
    calc (Qi * x * Q) * D = Qi * x * (Q * D) := by simp only [mul_assoc]
      _ = Qi * x * (B * Q) := by rw [hBQ]
      _ = Qi * (x * B) * Q := by simp only [mul_assoc]
      _ = Qi * (B * x) * Q := by rw [hxB]
      _ = (Qi * B) * x * Q := by simp only [mul_assoc]
      _ = (D * Qi) * x * Q := by rw [hQiB]
      _ = D * (Qi * x * Q) := by simp only [mul_assoc]
  have hXblk : ∀ x ∈ P, IsBlk (Qi * x * Q) := fun x hx => zeros_of_comm_signD hs0 h2 (hXcomm x hx)
  have hXpow : ∀ x ∈ P, (Qi * x * Q) ^ 3 = 1 := by
    intro x hx
    calc (Qi * x * Q) ^ 3 = (Qi * x * Q) ^ (2 + 1) := rfl
      _ = Qi * x ^ (2 + 1) * Q := hconj_pow x 2
      _ = Qi * 1 * Q := by rw [show x ^ (2 + 1) = x ^ 3 from rfl, hP3 x hx]
      _ = 1 := by rw [mul_one, hQiQ]
  have hXdiag : ∀ x ∈ P, (Qi * x * Q) 0 0 = 1 := by
    intro x hx
    apply eq_one_of_pow_three h3
    rw [← pow3_entry00 (hXblk x hx), hXpow x hx]
    simp
  have hNblk : ∀ x ∈ P, IsBlk (Qi * x * Q - 1) := fun x hx => isBlk_sub_one (hXblk x hx)
  have hN00 : ∀ x ∈ P, (Qi * x * Q - 1) 0 0 = 0 := fun x hx => by
    rw [Matrix.sub_apply, hXdiag x hx, Matrix.one_apply_eq, sub_self]
  have hNpow : ∀ x ∈ P, (Qi * x * Q - 1) ^ 3 = 0 := fun x hx => by
    rw [sub_one_pow3 _ h3, hXpow x hx, sub_self]
  have hblk3 : ∀ N : Matrix (Fin 3) (Fin 3) K, IsBlk N →
      blk (N * N * N) = blk N * blk N * blk N := fun N hN => by
    rw [blk_mul (isBlk_mul hN hN) hN, blk_mul hN hN]
  have hNtr : ∀ x ∈ P, blk (Qi * x * Q - 1) 0 0 + blk (Qi * x * Q - 1) 1 1 = 0 := fun x hx => by
    have h3' : blk (Qi * x * Q - 1) * blk (Qi * x * Q - 1) * blk (Qi * x * Q - 1) = 0 := by
      rw [← hblk3 _ (hNblk x hx), ← pow_three', hNpow x hx, blk_zero]
    exact trace2_of_pow3_eq_zero h3'
  obtain ⟨h₁, hh₁P, hh₁1⟩ : ∃ h ∈ P, h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : P ⊆ {1} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hN₁ne : blk (Qi * h₁ * Q - 1) ≠ 0 := by
    intro h0
    apply hh₁1
    have hN₁ : Qi * h₁ * Q - 1 = 0 := by
      apply eq_of_isBlk (hNblk h₁ hh₁P) isBlk_zero
      · rw [hN00 h₁ hh₁P]; simp
      · rw [h0, blk_zero]
    have hq : Qi * h₁ * Q = 1 := sub_eq_zero.1 hN₁
    calc h₁ = Q * (Qi * h₁ * Q) * Qi := by
          calc h₁ = (Q * Qi) * h₁ * (Q * Qi) := by rw [hQQi, one_mul, mul_one]
            _ = Q * (Qi * h₁ * Q) * Qi := by simp only [mul_assoc]
      _ = 1 := by rw [hq, mul_one, hQQi]
  have hcomm_blk : ∀ x ∈ P,
      blk (Qi * x * Q - 1) * blk (Qi * h₁ * Q - 1) = blk (Qi * h₁ * Q - 1) * blk (Qi * x * Q - 1) := by
    intro x hx
    have hcx : (Qi * x * Q - 1) * (Qi * h₁ * Q - 1) = (Qi * h₁ * Q - 1) * (Qi * x * Q - 1) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hconj_mul]
      rw [hPc x hx h₁ hh₁P]
      abel
    have := congrArg blk hcx
    rwa [blk_mul (hNblk x hx) (hNblk h₁ hh₁P), blk_mul (hNblk h₁ hh₁P) (hNblk x hx)] at this
  have key : ∀ x ∈ P, ∃ β : K, x - 1 = β • (h₁ - 1) := by
    intro x hx
    obtain ⟨β, hβ⟩ := comm_block_scalar h2 hN₁ne (hNtr h₁ hh₁P) (hcomm_blk x hx) (hNtr x hx)
    refine ⟨β, ?_⟩
    have hNx : Qi * x * Q - 1 = β • (Qi * h₁ * Q - 1) := by
      apply eq_of_isBlk (hNblk x hx) (isBlk_smul β (hNblk h₁ hh₁P))
      · rw [hN00 x hx, Matrix.smul_apply, hN00 h₁ hh₁P]; simp
      · rw [blk_smul]; exact hβ
    calc x - 1 = Q * (Qi * x * Q - 1) * Qi := (hconj_sub x).symm
      _ = Q * (β • (Qi * h₁ * Q - 1)) * Qi := by rw [hNx]
      _ = β • (Q * (Qi * h₁ * Q - 1) * Qi) := by simp [Matrix.mul_smul, Matrix.smul_mul]
      _ = β • (h₁ - 1) := by rw [hconj_sub h₁]
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, (h₁ - 1) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hh₁1
    have : h₁ - 1 = 0 := by
      ext i j
      exact hcon i j
    exact sub_eq_zero.1 this
  have hF1 : ∀ x ∈ P, (x - 1) i₀ j₀ ∈ F₀ := fun x hx => by
    rw [Matrix.sub_apply]
    apply F₀.sub_mem (hPF x hx i₀ j₀)
    rw [Matrix.one_apply]
    split_ifs
    · exact F₀.one_mem
    · exact F₀.zero_mem
  have hinj : Set.InjOn (fun x : Matrix (Fin 3) (Fin 3) K => (x - 1) i₀ j₀) P := by
    intro x hx y hy hxy
    obtain ⟨βx, hβx⟩ := key x hx
    obtain ⟨βy, hβy⟩ := key y hy
    have e1 : (x - 1) i₀ j₀ = βx * (h₁ - 1) i₀ j₀ := by rw [hβx]; simp
    have e2 : (y - 1) i₀ j₀ = βy * (h₁ - 1) i₀ j₀ := by rw [hβy]; simp
    have hβ : βx = βy := by
      have : βx * (h₁ - 1) i₀ j₀ = βy * (h₁ - 1) i₀ j₀ := by
        rw [← e1, ← e2]
        exact hxy
      exact mul_right_cancel₀ hij this
    have hxy' : x - 1 = y - 1 := by rw [hβx, hβy, hβ]
    exact sub_left_injective hxy'
  haveI : Finite F₀ := Nat.finite_of_card_ne_zero (by rw [hF₀]; norm_num)
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  have hT : (Finset.univ.image (fun a : F₀ => (a : K))).card = 3 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      Fintype.card_eq_nat_card, hF₀]
  have hmem : ∀ x ∈ P, (x - 1) i₀ j₀ ∈ Finset.univ.image (fun a : F₀ => (a : K)) := fun x hx => by
    rw [Finset.mem_image]
    exact ⟨⟨_, hF1 x hx⟩, Finset.mem_univ _, rfl⟩
  have hle := Finset.card_le_card_of_injOn (s := P) (t := Finset.univ.image (fun a : F₀ => (a : K)))
    (fun x : Matrix (Fin 3) (Fin 3) K => (x - 1) i₀ j₀) hmem hinj
  omega

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Core
