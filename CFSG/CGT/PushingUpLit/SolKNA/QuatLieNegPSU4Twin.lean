module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSU4Block

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open Matrix

@[expose] def psu4Delta (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 1 0 0 (-1)

section Blocks

variable {K : Type} [Field K]

theorem psu4Delta_eq : psu4Delta K = fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 (-1) := rfl

theorem psu4Delta_mul_self : psu4Delta K * psu4Delta K = 1 := by
  rw [psu4Delta_eq, fromBlocks_multiply]
  simp

theorem psu4Twin_cj (P Q R S : Matrix (Fin 2) (Fin 2) K) :
    ((fromBlocks P Q R S).map (· ^ 3))ᵀ = fromBlocks (P.map (· ^ 3))ᵀ (R.map (· ^ 3))ᵀ
      (Q.map (· ^ 3))ᵀ (S.map (· ^ 3))ᵀ := by
  rw [fromBlocks_map, fromBlocks_transpose]

theorem psu4Twin_cj_diag (P S : Matrix (Fin 2) (Fin 2) K) :
    ((fromBlocks P 0 0 S).map (· ^ 3))ᵀ = fromBlocks (P.map (· ^ 3))ᵀ 0 0 (S.map (· ^ 3))ᵀ := by
  rw [psu4Twin_cj]
  simp

theorem psu4Twin_diag_mul (P S P' S' : Matrix (Fin 2) (Fin 2) K) :
    fromBlocks P 0 0 S * fromBlocks P' 0 0 S' = fromBlocks (P * P') 0 0 (S * S') := by
  rw [fromBlocks_multiply]
  simp

theorem psu4Twin_two_ne_zero [Finite K] (hK : Nat.card K = 9) : (2 : K) ≠ 0 := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]
  refine Ring.two_ne_zero fun h => ?_
  have := (FiniteField.even_card_iff_char_two (F := K)).mp h
  omega

theorem psu4Twin_smul_one_inj {x y : K} (h : x • (1 : Matrix (Fin 2) (Fin 2) K) = y • 1) :
    x = y := by
  have := congrFun (congrFun h 0) 0
  simpa using this

theorem psu4Twin_smul_one_mul (x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K)) * (y • 1) = (x * y) • 1 := by
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]

theorem psu4Twin_smul_one_cj (x : K) :
    ((x • (1 : Matrix (Fin 2) (Fin 2) K)).map (· ^ 3))ᵀ = (x ^ 3) • 1 := by
  refine Matrix.ext fun i j => ?_
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, h.symm]

theorem psu4Twin_diag_delta (P S : Matrix (Fin 2) (Fin 2) K) :
    fromBlocks P 0 0 S * psu4Delta K = fromBlocks P 0 0 (-S) := by
  rw [psu4Delta_eq, psu4Twin_diag_mul]
  simp

theorem psu4Twin_conj_diag (w₁ w₂ P S : Matrix (Fin 2) (Fin 2) K) :
    fromBlocks w₁ 0 0 w₂ * fromBlocks P 0 0 S * ((fromBlocks w₁ 0 0 w₂).map (· ^ 3))ᵀ =
      fromBlocks (w₁ * P * (w₁.map (· ^ 3))ᵀ) 0 0 (w₂ * S * (w₂.map (· ^ 3))ᵀ) := by
  rw [psu4Twin_cj_diag, psu4Twin_diag_mul, psu4Twin_diag_mul]

theorem psu4Twin_diag_eq_smul {P S P' S' : Matrix (Fin 2) (Fin 2) K} {c : K}
    (h : fromBlocks P' 0 0 S' = c • fromBlocks P 0 0 S) : P' = c • P ∧ S' = c • S := by
  rw [fromBlocks_smul, smul_zero, fromBlocks_inj] at h
  exact ⟨h.1, h.2.2.2⟩

theorem psu4Twin_eq_zero_of_neg_eq (h2 : (2 : K) ≠ 0) {Q : Matrix (Fin 2) (Fin 2) K}
    (h : -Q = Q) : Q = 0 := by
  refine Matrix.ext fun i j => ?_
  have h1 : -Q i j = Q i j := by simpa using congrFun (congrFun h i) j
  have h3 : (2 : K) * Q i j = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h3).resolve_left h2

abbrev Psu4Twin (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) : Prop :=
  ∃ G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
    (G.map (· ^ 3))ᵀ * G = 1 ∧ G.det = 1 ∧
    (∃ r' : K, G * psu4Delta K = r' • (psu4Delta K * G)) ∧
    (∃ ε : K, (G * A * (G.map (· ^ 3))ᵀ) * A = ε • (A * (G * A * (G.map (· ^ 3))ᵀ))) ∧
    (∀ c : K, G * A * (G.map (· ^ 3))ᵀ ≠ c • A) ∧
    (∀ c : K, G * A * (G.map (· ^ 3))ᵀ ≠ c • (A * psu4Delta K))

theorem psu4Twin_not_both_scalar [Finite K] (hK : Nat.card K = 9)
    (P S : Matrix (Fin 2) (Fin 2) K) (s : K) (hPu : (P.map (· ^ 3))ᵀ * P = 1)
    (hdet : P.det * S.det = 1) (hPP : P * P = s • (1 : Matrix (Fin 2) (Fin 2) K))
    (hSS : S * S = (-s) • (1 : Matrix (Fin 2) (Fin 2) K)) (x y : K)
    (hx : P = x • 1) (hy : S = y • 1) : False := by
  have h2 := psu4Twin_two_ne_zero hK
  subst hx hy
  rw [psu4Twin_smul_one_cj, psu4Twin_smul_one_mul] at hPu
  rw [psu4Twin_smul_one_mul] at hPP hSS
  have h1 : x ^ 3 * x = 1 := psu4Twin_smul_one_inj (hPu.trans (one_smul K _).symm)
  have h3 : x * x = s := psu4Twin_smul_one_inj hPP
  have h4 : y * y = -s := psu4Twin_smul_one_inj hSS
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at hdet
  have h5 : (2 : K) = 0 := by
    linear_combination (-1 : K) * hdet + (x * x) * h4 + (x * x) * h3 - h1
  exact h2 h5

@[expose] def psu4W (K : Type) [Field K] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks 0 1 (-1) 0

theorem psu4W_eq : psu4W K = fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 := rfl

theorem psu4Twin_map_cube_zero : (0 : Matrix (Fin 2) (Fin 2) K).map (· ^ 3) = 0 := by
  refine Matrix.ext fun i j => ?_
  simp

theorem psu4Twin_map_cube_one : (1 : Matrix (Fin 2) (Fin 2) K).map (· ^ 3) = 1 := by
  refine Matrix.ext fun i j => ?_
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

theorem psu4Twin_map_cube_neg_one : (-1 : Matrix (Fin 2) (Fin 2) K).map (· ^ 3) = -1 := by
  refine Matrix.ext fun i j => ?_
  rcases eq_or_ne i j with rfl | h
  · simp
    ring
  · simp [h]

theorem psu4W_cj : ((psu4W K).map (· ^ 3))ᵀ =
    fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) (-1) 1 0 := by
  rw [psu4W_eq, psu4Twin_cj, psu4Twin_map_cube_zero, psu4Twin_map_cube_one,
    psu4Twin_map_cube_neg_one]
  simp

theorem psu4W_unitary : ((psu4W K).map (· ^ 3))ᵀ * psu4W K = 1 := by
  rw [psu4W_cj, psu4W_eq, fromBlocks_multiply]
  simp

theorem psu4W_det : (psu4W K).det = 1 := by
  have h : psu4W K = fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 1 0 1 *
      fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 (-1) 1 *
      fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 1 0 1 := by
    rw [psu4W_eq]
    simp [fromBlocks_multiply]
  rw [h, Matrix.det_mul, Matrix.det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂]
  simp

theorem psu4W_delta : psu4W K * psu4Delta K = (-1 : K) • (psu4Delta K * psu4W K) := by
  rw [psu4Delta_eq, psu4W_eq, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  simp

theorem psu4W_conj (P S : Matrix (Fin 2) (Fin 2) K) :
    psu4W K * fromBlocks P 0 0 S * ((psu4W K).map (· ^ 3))ᵀ = fromBlocks S 0 0 P := by
  rw [psu4W_cj, psu4W_eq]
  simp [fromBlocks_multiply]

theorem psu4Twin_comm_of_scalar {P S : Matrix (Fin 2) (Fin 2) K}
    (hcase : (∃ x : K, P = x • (1 : Matrix (Fin 2) (Fin 2) K)) ∨
      ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K)) : S * P = P * S := by
  rcases hcase with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;> simp

theorem psu4Twin_both_scalar {P S : Matrix (Fin 2) (Fin 2) K} {a b : K}
    (hcase : (∃ x : K, P = x • (1 : Matrix (Fin 2) (Fin 2) K)) ∨
      ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K))
    (h1 : S = a • P) (h2 : P = b • S) :
    (∃ x : K, P = x • (1 : Matrix (Fin 2) (Fin 2) K)) ∧
      ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rcases hcase with ⟨x, hx⟩ | ⟨y, hy⟩
  · exact ⟨⟨x, hx⟩, a * x, by rw [h1, hx, smul_smul]⟩
  · exact ⟨⟨b * y, by rw [h2, hy, smul_smul]⟩, y, hy⟩

theorem psu4Twin_swap (P S : Matrix (Fin 2) (Fin 2) K)
    (hcase : (∃ x : K, P = x • (1 : Matrix (Fin 2) (Fin 2) K)) ∨
      ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K))
    (hboth : ¬ ((∃ x : K, P = x • (1 : Matrix (Fin 2) (Fin 2) K)) ∧
      ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K))) :
    Psu4Twin (fromBlocks P 0 0 S) := by
  refine ⟨psu4W K, psu4W_unitary, psu4W_det, ⟨-1, psu4W_delta⟩, ⟨1, ?_⟩, ?_, ?_⟩
  · rw [psu4W_conj, one_smul, psu4Twin_diag_mul, psu4Twin_diag_mul,
      psu4Twin_comm_of_scalar hcase]
  · intro c h
    rw [psu4W_conj] at h
    obtain ⟨h1, h2⟩ := psu4Twin_diag_eq_smul h
    exact hboth (psu4Twin_both_scalar hcase h1 h2)
  · intro c h
    rw [psu4W_conj, psu4Twin_diag_delta] at h
    obtain ⟨h1, h2⟩ := psu4Twin_diag_eq_smul h
    rw [smul_neg, ← neg_smul] at h2
    exact hboth (psu4Twin_both_scalar hcase h1 h2)

theorem psu4Twin_not_multiple (h2 : (2 : K) ≠ 0) (P w : Matrix (Fin 2) (Fin 2) K) (s : K)
    (hs0 : s ≠ 0) (hPP : P * P = s • (1 : Matrix (Fin 2) (Fin 2) K))
    (hwu : (w.map (· ^ 3))ᵀ * w = 1)
    (hanti : (w * P * (w.map (· ^ 3))ᵀ) * P = -(P * (w * P * (w.map (· ^ 3))ᵀ))) (c : K)
    (hc : w * P * (w.map (· ^ 3))ᵀ = c • P) : False := by
  have hc' := hc
  rw [hc, Matrix.smul_mul, Matrix.mul_smul, hPP, smul_smul] at hanti
  have h1 : c * s = -(c * s) := psu4Twin_smul_one_inj (by rw [neg_smul]; exact hanti)
  have h3 : (2 : K) * (c * s) = 0 := by linear_combination h1
  have hcs : c * s = 0 := (mul_eq_zero.mp h3).resolve_left h2
  have hc0 : c = 0 := (mul_eq_zero.mp hcs).resolve_right hs0
  rw [hc0, zero_smul] at hc'
  have hP0 : P = 0 := by
    calc P = ((w.map (· ^ 3))ᵀ * w) * P * ((w.map (· ^ 3))ᵀ * w) := by
          rw [hwu, Matrix.one_mul, Matrix.mul_one]
      _ = (w.map (· ^ 3))ᵀ * (w * P * (w.map (· ^ 3))ᵀ) * w := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hc', Matrix.mul_zero, Matrix.zero_mul]
  rw [hP0, Matrix.zero_mul] at hPP
  exact hs0 (psu4Twin_smul_one_inj (hPP.symm.trans (zero_smul K _).symm))

theorem psu4Twin_anticomm [Finite K] (hK : Nat.card K = 9) (P S : Matrix (Fin 2) (Fin 2) K)
    (s : K) (hs0 : s ≠ 0) (hPu : (P.map (· ^ 3))ᵀ * P = 1) (hSu : (S.map (· ^ 3))ᵀ * S = 1)
    (hPP : P * P = s • (1 : Matrix (Fin 2) (Fin 2) K))
    (hSS : S * S = (-s) • (1 : Matrix (Fin 2) (Fin 2) K))
    (hPn : ∀ x : K, P ≠ x • (1 : Matrix (Fin 2) (Fin 2) K))
    (hSn : ∀ y : K, S ≠ y • (1 : Matrix (Fin 2) (Fin 2) K)) :
    Psu4Twin (fromBlocks P 0 0 S) := by
  have h2 := psu4Twin_two_ne_zero hK
  obtain ⟨w₁, hw₁d, hw₁u, hw₁a⟩ := exists_anticommuting_conjugate hK P hPu hPn ⟨s, hPP⟩
  obtain ⟨w₂, hw₂d, hw₂u, hw₂a⟩ := exists_anticommuting_conjugate hK S hSu hSn ⟨-s, hSS⟩
  have hconj := psu4Twin_conj_diag w₁ w₂ P S
  refine ⟨fromBlocks w₁ 0 0 w₂, ?_, ?_, ⟨1, ?_⟩, ⟨-1, ?_⟩, ?_, ?_⟩
  · rw [psu4Twin_cj_diag, psu4Twin_diag_mul, hw₁u, hw₂u, fromBlocks_one]
  · rw [det_fromBlocks_zero₂₁, hw₁d, hw₂d, mul_one]
  · rw [psu4Delta_eq, psu4Twin_diag_mul, psu4Twin_diag_mul, one_smul]
    simp
  · rw [hconj, psu4Twin_diag_mul, psu4Twin_diag_mul, fromBlocks_smul, hw₁a, hw₂a]
    simp
  · intro c h
    rw [hconj] at h
    exact psu4Twin_not_multiple h2 P w₁ s hs0 hPP hw₁u hw₁a c (psu4Twin_diag_eq_smul h).1
  · intro c h
    rw [hconj, psu4Twin_diag_delta] at h
    exact psu4Twin_not_multiple h2 P w₁ s hs0 hPP hw₁u hw₁a c (psu4Twin_diag_eq_smul h).1

end Blocks

theorem psu4_block_twin {K : Type} [Field K] [Finite K] (hK : Nat.card K = 9)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    (hAu : (A.map (· ^ 3))ᵀ * A = 1) (hAd : A.det = 1) (r s : K)
    (hr : A * psu4Delta K = r • (psu4Delta K * A)) (hs : A * A = s • psu4Delta K) :
    ∃ G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K,
      (G.map (· ^ 3))ᵀ * G = 1 ∧ G.det = 1 ∧
      (∃ r' : K, G * psu4Delta K = r' • (psu4Delta K * G)) ∧
      (∃ ε : K, (G * A * (G.map (· ^ 3))ᵀ) * A = ε • (A * (G * A * (G.map (· ^ 3))ᵀ))) ∧
      (∀ c : K, G * A * (G.map (· ^ 3))ᵀ ≠ c • A) ∧
      (∀ c : K, G * A * (G.map (· ^ 3))ᵀ ≠ c • (A * psu4Delta K)) := by
  have h2 := psu4Twin_two_ne_zero hK
  have : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h1 := congrArg Matrix.det hs
    rw [Matrix.det_mul, hAd, zero_smul, Matrix.det_zero] at h1
    simp at h1
  have hr1 : r = 1 := by
    have h3 : (s * r) • (psu4Delta K * A) = s • (psu4Delta K * A) := by
      calc (s * r) • (psu4Delta K * A) = s • (A * psu4Delta K) := by rw [← smul_smul, ← hr]
        _ = A * (A * A) := by rw [hs, Matrix.mul_smul]
        _ = (A * A) * A := (Matrix.mul_assoc A A A).symm
        _ = s • (psu4Delta K * A) := by rw [hs, Matrix.smul_mul]
    have h4 : (s * r) • A = s • A := by
      have h5 := congrArg (fun M => psu4Delta K * M) h3
      simp only [Matrix.mul_smul, ← Matrix.mul_assoc, psu4Delta_mul_self, Matrix.one_mul] at h5
      exact h5
    have h6 : (s * (r - 1)) • A = 0 := by
      rw [mul_sub, mul_one, sub_smul, h4, sub_self]
    rcases smul_eq_zero.mp h6 with h | h
    · exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hs0)
    · rw [h, Matrix.det_zero] at hAd
      exact absurd hAd zero_ne_one
  subst hr1
  obtain ⟨P, Q, R, S, rfl⟩ : ∃ P Q R S : Matrix (Fin 2) (Fin 2) K, A = fromBlocks P Q R S :=
    ⟨_, _, _, _, (fromBlocks_toBlocks A).symm⟩
  have hQR : Q = 0 ∧ R = 0 := by
    rw [psu4Delta_eq, fromBlocks_multiply, fromBlocks_multiply, one_smul] at hr
    have h12 := (fromBlocks_inj.mp hr).2.1
    have h21 := (fromBlocks_inj.mp hr).2.2.1
    refine ⟨psu4Twin_eq_zero_of_neg_eq h2 ?_, psu4Twin_eq_zero_of_neg_eq h2 ?_⟩
    · simpa using h12
    · simpa using h21.symm
  obtain ⟨rfl, rfl⟩ := hQR
  rw [psu4Twin_cj_diag, psu4Twin_diag_mul] at hAu
  obtain ⟨hPu, -, -, hSu⟩ := fromBlocks_inj.mp (hAu.trans fromBlocks_one.symm)
  rw [psu4Twin_diag_mul, psu4Delta_eq, fromBlocks_smul, smul_zero] at hs
  obtain ⟨hPP, -, -, hSS'⟩ := fromBlocks_inj.mp hs
  have hSS : S * S = (-s) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [hSS', smul_neg, neg_smul]
  rw [det_fromBlocks_zero₂₁] at hAd
  by_cases hPs : ∃ x : K, P = x • (1 : Matrix (Fin 2) (Fin 2) K)
  · by_cases hSs : ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K)
    · obtain ⟨x, hx⟩ := hPs
      obtain ⟨y, hy⟩ := hSs
      exact (psu4Twin_not_both_scalar hK P S s hPu hAd hPP hSS x y hx hy).elim
    · exact psu4Twin_swap P S (Or.inl hPs) fun h => hSs h.2
  · by_cases hSs : ∃ y : K, S = y • (1 : Matrix (Fin 2) (Fin 2) K)
    · exact psu4Twin_swap P S (Or.inr hSs) fun h => hPs h.1
    · exact psu4Twin_anticomm hK P S s hs0 hPu hSu hPP hSS (fun x hx => hPs ⟨x, hx⟩)
        (fun y hy => hSs ⟨y, hy⟩)

end CFSG.CGT.PushingUpLit.SolKNA
