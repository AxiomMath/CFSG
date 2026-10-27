module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallF12Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Mat

open Matrix CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Mat
  CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallF12Core

variable {K : Type} [Field K]

theorem key_block (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0)
    (P : Finset (Matrix (Fin 3) (Fin 3) K))
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    {B : Matrix (Fin 3) (Fin 3) K} (hB : B * B = 1) (hB1 : B ≠ 1) (hBm : B ≠ -1)
    (hBP : ∀ x ∈ P, B * x = x * B) {h₁ : Matrix (Fin 3) (Fin 3) K} (hh₁P : h₁ ∈ P)
    (hh₁1 : h₁ ≠ 1) :
    ∀ x ∈ P, ∃ β : K, x - 1 = β • (h₁ - 1) := by
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
      blk (Qi * x * Q - 1) * blk (Qi * h₁ * Q - 1) =
        blk (Qi * h₁ * Q - 1) * blk (Qi * x * Q - 1) := by
    intro x hx
    have hcx : (Qi * x * Q - 1) * (Qi * h₁ * Q - 1) = (Qi * h₁ * Q - 1) * (Qi * x * Q - 1) := by
      simp only [sub_mul, mul_sub, one_mul, mul_one, hconj_mul]
      rw [hPc x hx h₁ hh₁P]
      abel
    have := congrArg blk hcx
    rwa [blk_mul (hNblk x hx) (hNblk h₁ hh₁P), blk_mul (hNblk h₁ hh₁P) (hNblk x hx)] at this
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

theorem expand_unit (M N : Matrix (Fin 3) (Fin 3) K) (r a : K)
    (hU : (1 + r • N) * (1 + a • M) = 1) : a • M + r • N + (r * a) • (N * M) = 0 := by
  have e : (1 + r • N) * (1 + a • M) = 1 + (a • M + r • N + (r * a) • (N * M)) := by
    simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_comm a r]
    abel
  rw [e] at hU
  exact add_eq_left.1 hU

theorem map_transpose_one_add_smul (bar : K →+* K) (r : K) (M : Matrix (Fin 3) (Fin 3) K) :
    ((1 + r • M).map bar)ᵀ = 1 + bar r • (M.map bar)ᵀ := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply, map_add, map_mul, map_one, Matrix.transpose_apply, Matrix.map_apply]
  · simp [Matrix.one_apply, h, Ne.symm h, Matrix.transpose_apply, Matrix.map_apply]

theorem no_involution_of_F9 (hK : ringChar K ≠ 2) (h3 : (3 : K) = 0)
    (bar : K →+* K) (F₀ : Subfield K) (hF₀ : Nat.card F₀ = 9) (hbarF : ∃ c ∈ F₀, bar c ≠ c)
    (P : Finset (Matrix (Fin 3) (Fin 3) K)) (hPcard : P.card = 9)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hP3 : ∀ x ∈ P, x ^ 3 = 1)
    (hPF : ∀ x ∈ P, ∀ i j, x i j ∈ F₀) (hPU : ∀ x ∈ P, (x.map bar)ᵀ * x = 1)
    {B : Matrix (Fin 3) (Fin 3) K} (hB : B * B = 1) (hB1 : B ≠ 1) (hBm : B ≠ -1)
    (hBP : ∀ x ∈ P, B * x = x * B) : False := by
  classical
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  obtain ⟨h₁, hh₁P, hh₁1⟩ : ∃ h ∈ P, h ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : P ⊆ {1} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have key := key_block hK h3 P hPc hP3 hB hB1 hBm hBP hh₁P hh₁1
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, (h₁ - 1) i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hh₁1
    have : h₁ - 1 = 0 := by
      ext i j
      exact hcon i j
    exact sub_eq_zero.1 this
  set M := h₁ - 1 with hMdef
  set m := M i₀ j₀ with hmdef
  have hm0 : m ≠ 0 := hij
  let φ : Matrix (Fin 3) (Fin 3) K → K := fun x => (x - 1) i₀ j₀
  have hφcoef : ∀ x ∈ P, ∃ β : K, x - 1 = β • M ∧ φ x = β * m := by
    intro x hx
    obtain ⟨β, hβ⟩ := key x hx
    exact ⟨β, hβ, by simp only [φ, hβ, Matrix.smul_apply, smul_eq_mul, hmdef]⟩
  haveI : Finite F₀ := Nat.finite_of_card_ne_zero (by rw [hF₀]; norm_num)
  haveI : Fintype F₀ := Fintype.ofFinite F₀
  have hT : (Finset.univ.image (fun a : F₀ => (a : K))).card = 9 := by
    rw [Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_univ,
      Fintype.card_eq_nat_card, hF₀]
  have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := P)
    (t := Finset.univ.image (fun a : F₀ => (a : K)))
    (fun x _ => φ x)
    (by
      intro x hx
      obtain ⟨β, -, hφx⟩ := hφcoef x hx
      rw [Finset.mem_image]
      refine ⟨⟨φ x, ?_⟩, Finset.mem_univ _, rfl⟩
      simp only [φ, Matrix.sub_apply]
      have hx1 := hPF x hx i₀ j₀
      have h1 : (1 : Matrix (Fin 3) (Fin 3) K) i₀ j₀ ∈ F₀ := by
        rw [Matrix.one_apply]
        split_ifs
        · exact F₀.one_mem
        · exact F₀.zero_mem
      exact F₀.sub_mem hx1 h1)
    (by
      intro x₁ x₂ hx₁ hx₂ hxeq
      obtain ⟨β₁, hβ₁, hφ₁⟩ := hφcoef x₁ hx₁
      obtain ⟨β₂, hβ₂, hφ₂⟩ := hφcoef x₂ hx₂
      have hββ : β₁ = β₂ := by
        have : β₁ * m = β₂ * m := by rw [← hφ₁, ← hφ₂]; exact hxeq
        exact mul_right_cancel₀ hm0 this
      have : x₁ - 1 = x₂ - 1 := by rw [hβ₁, hβ₂, hββ]
      exact sub_left_injective this)
    (by rw [hT, hPcard])
  set M' := m⁻¹ • M with hM'def
  have hcover : ∀ a ∈ F₀, ∃ x ∈ P, x - 1 = a • M' := by
    intro a ha
    have haT : a ∈ Finset.univ.image (fun a : F₀ => (a : K)) :=
      Finset.mem_image.2 ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hsurj a haT
    obtain ⟨β, hβ, hφx⟩ := hφcoef x hx
    refine ⟨x, hx, ?_⟩
    have hβa : β = a * m⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hm0, ← hφx]
      exact hxa.symm
    rw [hβ, hM'def, smul_smul, hβa]
  set N := (M'.map bar)ᵀ with hNdef
  have hE : ∀ a ∈ F₀, a • M' + bar a • N + (bar a * a) • (N * M') = 0 := by
    intro a ha
    obtain ⟨x, hx, hxa⟩ := hcover a ha
    have hx' : x = 1 + a • M' := by rw [← hxa]; abel
    have hU := hPU x hx
    rw [hx', map_transpose_one_add_smul] at hU
    exact expand_unit M' N (bar a) a hU
  obtain ⟨c, hcF, hbc⟩ := hbarF
  have E1 : M' + N + N * M' = 0 := by simpa using hE 1 F₀.one_mem
  have E2 : -M' + -N + N * M' = 0 := by simpa using hE (-1) (F₀.neg_mem F₀.one_mem)
  have hC2 : (2 : K) • (N * M') = 0 := by
    rw [two_smul]
    calc N * M' + N * M' = (M' + N + N * M') + (-M' + -N + N * M') := by abel
      _ = 0 := by rw [E1, E2, add_zero]
  have hC0 : N * M' = 0 := (smul_eq_zero.1 hC2).resolve_left h2
  have hAB2 : (2 : K) • (M' + N) = 0 := by
    rw [two_smul]
    calc (M' + N) + (M' + N) = (M' + N + N * M') - (-M' + -N + N * M') := by abel
      _ = 0 := by rw [E1, E2, sub_self]
  have hBA : N = -M' := by
    have h0 : M' + N = 0 := (smul_eq_zero.1 hAB2).resolve_left h2
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  have Ec := hE c hcF
  rw [hC0, smul_zero, add_zero, hBA, smul_neg] at Ec
  have hdiff : (c - bar c) • M' = 0 := by
    rw [sub_smul, sub_eq_add_neg]
    exact Ec
  have hM'0 : M' = 0 := (smul_eq_zero.1 hdiff).resolve_left (sub_ne_zero.2 (Ne.symm hbc))
  have hM0 : M = m • M' := by rw [hM'def, smul_smul, mul_inv_cancel₀ hm0, one_smul]
  rw [hM'0, smul_zero] at hM0
  rw [hMdef] at hM0
  exact hh₁1 (sub_eq_zero.1 hM0)

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallU3Mat

end
