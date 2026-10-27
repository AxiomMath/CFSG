module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FUHerm
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2L33C2FURed

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo

open CFSG Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

@[expose] def hp (x y : Fin n → K) : Matrix (Fin n) (Fin n) K := rk h x y + rk h y x

theorem hf_swap_eq_one {x y : Fin n → K} (hxy : hf h x y = 1) : hf h y x = 1 := by
  rw [← hf_comm, hxy, map_one]

theorem hp_mul_self {x y : Fin n → K} (hxx : hf h x x = 0) (hyy : hf h y y = 0)
    (hxy : hf h x y = 1) : hp h x y * hp h x y = hp h x y := by
  simp only [hp, Matrix.add_mul, Matrix.mul_add, rk_mul_rk, hxx, hyy, hxy, hf_swap_eq_one h hxy,
    one_smul, zero_smul, add_zero, zero_add]

theorem adj_hp (x y : Fin n → K) : adj h (hp h x y) = hp h x y := by
  rw [hp, adj_add, adj_rk, adj_rk, add_comm]

theorem hp_mulVec_left {x y : Fin n → K} (hxx : hf h x x = 0) (hxy : hf h x y = 1) :
    hp h x y *ᵥ x = x := by
  rw [hp, add_mulVec, rk_mulVec, rk_mulVec, hf_swap_eq_one h hxy, hxx, one_smul, zero_smul,
    add_zero]

theorem hp_mulVec_right {x y : Fin n → K} (hyy : hf h y y = 0) (hxy : hf h x y = 1) :
    hp h x y *ᵥ y = y := by
  rw [hp, add_mulVec, rk_mulVec, rk_mulVec, hyy, hxy, zero_smul, one_smul, zero_add]

theorem det_one_add_smul_hp {x y : Fin n → K} (hyy : hf h y y = 0) (hxy : hf h x y = 1)
    (c : K) : (1 + c • hp h x y).det = (1 + c) ^ 2 := by
  have hAB : rk h x y * rk h y x = 0 := by rw [rk_mul_rk, hyy, zero_smul]
  have e : (1 + c • rk h x y) * (1 + c • rk h y x) = 1 + c • hp h x y := by
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hAB, smul_zero, smul_zero, add_zero, hp, smul_add]
    abel
  rw [← e, det_mul, det_one_add_smul_rk, det_one_add_smul_rk, hf_swap_eq_one h hxy, hxy,
    mul_one, sq]

theorem det_one_add_smul_rk_self {w : Fin n → K} (hww : hf h w w = 1) (c : K) :
    (1 + c • rk h w w).det = 1 + c := by
  rw [det_one_add_smul_rk, hww, mul_one]

@[expose] def blk (P₁ P₂ : Matrix (Fin n) (Fin n) K) (a b : K) : Matrix (Fin n) (Fin n) K :=
  1 + (a - 1) • P₁ + (b - 1) • P₂

section Blk

variable {P₁ P₂ : Matrix (Fin n) (Fin n) K}

theorem blk_one_one : blk P₁ P₂ (1 : K) 1 = 1 := by
  simp [blk]

theorem blk_mul (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h12 : P₁ * P₂ = 0)
    (h21 : P₂ * P₁ = 0) (a b c d : K) :
    blk P₁ P₂ a b * blk P₁ P₂ c d = blk P₁ P₂ (a * c) (b * d) := by
  simp only [blk, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, h1, h2, h12, h21, smul_zero]
  module

theorem blk_pow (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂) (h12 : P₁ * P₂ = 0)
    (h21 : P₂ * P₁ = 0) (a b : K) (m : ℕ) :
    blk P₁ P₂ a b ^ m = blk P₁ P₂ (a ^ m) (b ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_zero, blk_one_one]
  | succ m ih => rw [pow_succ, ih, blk_mul h1 h2 h12 h21, ← pow_succ, ← pow_succ]

theorem adj_blk (hP₁ : adj h P₁ = P₁) (hP₂ : adj h P₂ = P₂) (a b : K) :
    adj h (blk P₁ P₂ a b) = blk P₁ P₂ (h.bar a) (h.bar b) := by
  rw [blk, blk, adj_add, adj_add, adj_one, adj_smul, adj_smul, hP₁, hP₂, map_sub, map_sub,
    map_one]

theorem det_blk (h12 : P₁ * P₂ = 0) (a b : K) :
    (blk P₁ P₂ a b).det = (1 + (a - 1) • P₁).det * (1 + (b - 1) • P₂).det := by
  have e : blk P₁ P₂ a b = (1 + (a - 1) • P₁) * (1 + (b - 1) • P₂) := by
    rw [blk, Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, h12, smul_zero, smul_zero, add_zero]
    abel
  rw [e, det_mul]

theorem blk_mulVec (a b : K) (v : Fin n → K) :
    blk P₁ P₂ a b *ᵥ v = v + (a - 1) • (P₁ *ᵥ v) + (b - 1) • (P₂ *ᵥ v) := by
  rw [blk, add_mulVec, add_mulVec, one_mulVec, smul_mulVec, smul_mulVec]

theorem blk_commute {N : Matrix (Fin n) (Fin n) K} (hN₁ : P₁ * N = N * P₁)
    (hN₂ : P₂ * N = N * P₂) (a b : K) : blk P₁ P₂ a b * N = N * blk P₁ P₂ a b := by
  rw [blk, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, hN₁, hN₂]

theorem blk_spec {N : Matrix (Fin n) (Fin n) K} (h1 : P₁ * P₁ = P₁) (h2 : P₂ * P₂ = P₂)
    (h12 : P₁ * P₂ = 0) (h21 : P₂ * P₁ = 0) (hP₁ : adj h P₁ = P₁) (hP₂ : adj h P₂ = P₂)
    (hN₁ : P₁ * N = N * P₁) (hN₂ : P₂ * N = N * P₂) {a b : K} (ha : h.bar a * a = 1)
    (hb : h.bar b * b = 1) {m : ℕ} (ham : a ^ m = 1) (hbm : b ^ m = 1) :
    adj h (blk P₁ P₂ a b) * blk P₁ P₂ a b = 1 ∧
      blk P₁ P₂ a b * (N + 1) = (N + 1) * blk P₁ P₂ a b ∧ blk P₁ P₂ a b ^ m = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [adj_blk h hP₁ hP₂, blk_mul h1 h2 h12 h21, ha, hb, blk_one_one]
  · rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, blk_commute hN₁ hN₂]
  · rw [blk_pow h1 h2 h12 h21, ham, hbm, blk_one_one]

end Blk

include h in
theorem exists_circle : ∃ a : K, orderOf a = 2 ^ f + 1 := by
  have : Finite K := h.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(Units.map h.normHom).ker)
  refine ⟨((g : Kˣ) : K), ?_⟩
  rw [orderOf_units, Subgroup.orderOf_coe, hg,
    (UnitaryFieldData.card_ker_normUnits_and_surjective h).1]

theorem ne_scalar_of_eigen {X : Matrix (Fin n) (Fin n) K} {u v : Fin n → K} {α β : K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hXu : X *ᵥ u = α • u) (hXv : X *ᵥ v = β • v) (hαβ : α ≠ β)
    (c : K) : X ≠ scalar (Fin n) c := by
  rintro rfl
  have hs : ∀ w : Fin n → K, scalar (Fin n) c *ᵥ w = c • w := fun w => by
    rw [scalar_apply, ← smul_one_eq_diagonal, smul_mulVec, one_mulVec]
  have e1 : c = α := smul_left_injective K hu ((hs u).symm.trans hXu)
  have e2 : c = β := smul_left_injective K hv ((hs v).symm.trans hXv)
  exact hαβ (e1.symm.trans e2)

theorem eq_of_add_eq_zero_two {A B : Matrix (Fin n) (Fin n) K}
    (hadd : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0) (h0 : A + B = 0) : A = B :=
  calc A = A + (B + B) := by rw [hadd, add_zero]
    _ = A + B + B := by rw [add_assoc]
    _ = B := by rw [h0, zero_add]

theorem exists_blk_commuting (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    {S : Matrix (Fin n) (Fin n) K} (hS : adj h S * S = 1) (hSS : S * S = 1) (hS1 : S ≠ 1) :
    ∃ X : Matrix (Fin n) (Fin n) K, adj h X * X = 1 ∧ X.det = 1 ∧ X * S = S * X ∧
      X ^ (2 ^ f + 1) = 1 ∧ ∀ c : K, X ≠ scalar (Fin n) c := by
  have : CharP K 2 := h.charP
  have hadd : ∀ M : Matrix (Fin n) (Fin n) K, M + M = 0 := FourGroupEvenCanonical.matrix_add_self
  obtain ⟨a, ha⟩ := exists_circle h
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  have ha1 : a ^ (2 ^ f + 1) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hna : h.bar a * a = 1 := by rw [h.bar_apply, ← pow_succ, ha1]
  have hnb : h.bar (h.bar a) * h.bar a = 1 := by rw [h.bar_bar, mul_comm, hna]
  have hb1 : h.bar a ^ (2 ^ f + 1) = 1 := by rw [← map_pow, ha1, map_one]
  have hne1 : a ≠ 1 := by
    intro e
    rw [e, orderOf_one] at ha
    omega
  have hne2 : a ≠ h.bar a := by
    intro e
    have h2 : a ^ 2 = 1 :=
      calc a ^ 2 = h.bar a * a := by rw [sq, ← e]
        _ = 1 := hna
    have h3 := Nat.le_of_dvd two_pos (ha ▸ orderOf_dvd_of_pow_eq_one h2)
    omega
  have hSadj : adj h S = S :=
    calc adj h S = adj h S * (S * S) := by rw [hSS, Matrix.mul_one]
      _ = S := by rw [← Matrix.mul_assoc, hS, Matrix.one_mul]
  obtain ⟨N, hNdef⟩ : ∃ N, N = S + 1 := ⟨_, rfl⟩
  have hSN : S = N + 1 := by rw [hNdef, add_assoc, hadd, add_zero]
  have hN : adj h N = N := by rw [hNdef, adj_add, hSadj, adj_one]
  have hNN : N * N = 0 := by
    have e : N * N = S * S + (S + S) + 1 := by rw [hNdef]; noncomm_ring
    rw [e, hSS, hadd, add_zero, hadd]
  have hN0 : N ≠ 0 := fun h0 => hS1 (by rw [hSN, h0, zero_add])
  have hNNv : ∀ v : Fin n → K, N *ᵥ (N *ᵥ v) = 0 := fun v => by
    rw [mulVec_mulVec, hNN, zero_mulVec]
  have hsym : ∀ u v : Fin n → K, hf h (N *ᵥ u) v = hf h u (N *ᵥ v) := fun u v => by
    rw [hf_mulVec_left, hN]
  obtain ⟨x₀, hx₀⟩ := exists_hf_ne_zero h hN hN0
  obtain ⟨x₁, hx₁N, hx₁x₁, -⟩ := exists_hyp h hN hNN hx₀
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = N *ᵥ x₁ := ⟨_, rfl⟩
  rw [← hy₁] at hx₁N
  have hNy₁ : N *ᵥ y₁ = 0 := by rw [hy₁, hNNv]
  have hy₁y₁ : hf h y₁ y₁ = 0 := by rw [hy₁, hsym, hNNv, hf_zero_right]
  have hx₁0 : x₁ ≠ 0 := fun h0 => by
    rw [h0, hf_zero_left] at hx₁N
    exact zero_ne_one hx₁N
  obtain ⟨P₁, hP₁⟩ : ∃ P, P = hp h x₁ y₁ := ⟨_, rfl⟩
  have hP₁P₁ : P₁ * P₁ = P₁ := by rw [hP₁]; exact hp_mul_self h hx₁x₁ hy₁y₁ hx₁N
  have hP₁a : adj h P₁ = P₁ := by rw [hP₁]; exact adj_hp h x₁ y₁
  have hP₁x₁ : P₁ *ᵥ x₁ = x₁ := by rw [hP₁]; exact hp_mulVec_left h hx₁x₁ hx₁N
  have hc₁ : P₁ * N = N * P₁ := by
    rw [hP₁, hp, Matrix.add_mul, Matrix.mul_add, rk_mul, rk_mul, mul_rk, mul_rk, hN, hNy₁, ← hy₁,
      rk_zero_left, rk_zero_right, zero_add, add_zero]
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin n) (Fin n) K, M = 1 + P₁ := ⟨_, rfl⟩
  have hMa : adj h M = M := by rw [hMdef, adj_add, adj_one, hP₁a]
  have hMM : M * M = M := by
    have e : M * M = 1 + (P₁ + P₁) + P₁ * P₁ := by rw [hMdef]; noncomm_ring
    rw [e, hadd, add_zero, hP₁P₁, hMdef]
  have hP₁M : P₁ * M = 0 := by rw [hMdef, Matrix.mul_add, Matrix.mul_one, hP₁P₁, hadd]
  have hMN : M * N = N * M := by
    rw [hMdef, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hc₁]
  have hMv : ∀ v : Fin n → K, P₁ *ᵥ v = 0 → M *ᵥ v = v := fun v hv => by
    rw [hMdef, add_mulVec, one_mulVec, hv, add_zero]
  by_cases hN₂ : N * M = 0
  ·
    have hNeq : N * P₁ = N := by
      have e : N + N * P₁ = 0 := by rw [← hN₂, hMdef, Matrix.mul_add, Matrix.mul_one]
      exact (eq_of_add_eq_zero_two hadd e).symm
    obtain ⟨v₀, hv₀, hv₀o⟩ := exists_orth h (m := 2) (by omega) ![x₁, y₁]
    have hP₁v₀ : P₁ *ᵥ v₀ = 0 := by
      have e1 : hf h x₁ v₀ = 0 := hv₀o 0
      have e2 : hf h y₁ v₀ = 0 := hv₀o 1
      rw [hP₁, hp, add_mulVec, rk_mulVec, rk_mulVec, e1, e2, zero_smul, zero_smul, add_zero]
    have hM0 : M ≠ 0 := fun h0 => hv₀ (by
      rw [← hMv v₀ hP₁v₀, h0, zero_mulVec])
    obtain ⟨w₀', hw₀'⟩ := exists_hf_ne_zero h hMa hM0
    obtain ⟨w₀, hw₀⟩ : ∃ w, w = M *ᵥ w₀' := ⟨_, rfl⟩
    have hw₀w₀ : hf h w₀ w₀ ≠ 0 := by
      rw [hw₀, hf_mulVec_left, hMa, mulVec_mulVec, hMM]
      exact hw₀'
    have hP₁w₀ : P₁ *ᵥ w₀ = 0 := by rw [hw₀, mulVec_mulVec, hP₁M, zero_mulVec]
    obtain ⟨l, hl⟩ := exists_unit h hw₀w₀
    obtain ⟨w, hw⟩ : ∃ w, w = l • w₀ := ⟨_, rfl⟩
    rw [← hw] at hl
    have hP₁w : P₁ *ᵥ w = 0 := by rw [hw, mulVec_smul, hP₁w₀, smul_zero]
    have hw0 : w ≠ 0 := fun h0 => by
      rw [h0, hf_zero_left] at hl
      exact zero_ne_one hl
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = rk h w w := ⟨_, rfl⟩
    have hQQ : Q * Q = Q := by rw [hQ, rk_mul_rk, hl, one_smul]
    have hQa : adj h Q = Q := by rw [hQ, adj_rk]
    have hQw : Q *ᵥ w = w := by rw [hQ, rk_mulVec, hl, one_smul]
    have hP₁Q : P₁ * Q = 0 := by rw [hQ, mul_rk, hP₁w, rk_zero_left]
    have hQP₁ : Q * P₁ = 0 := by rw [hQ, rk_mul, hP₁a, hP₁w, rk_zero_right]
    have hNQ : N * Q = 0 := by rw [← hNeq, Matrix.mul_assoc, hP₁Q, Matrix.mul_zero]
    have hQN : Q * N = 0 := by
      have hP₁N : P₁ * N = N := by rw [hc₁, hNeq]
      rw [← hP₁N, ← Matrix.mul_assoc, hQP₁, Matrix.zero_mul]
    have hcQ : Q * N = N * Q := by rw [hQN, hNQ]
    have hb2 : h.bar (h.bar a ^ 2) * h.bar a ^ 2 = 1 := by
      rw [map_pow, h.bar_bar, ← mul_pow, mul_comm, hna, one_pow]
    have hb2m : (h.bar a ^ 2) ^ (2 ^ f + 1) = 1 := by rw [pow_right_comm, hb1, one_pow]
    obtain ⟨hXu, hXS, hXp⟩ := blk_spec h (a := a) (b := h.bar a ^ 2) (m := 2 ^ f + 1) hP₁P₁
      hQQ hP₁Q hQP₁ hP₁a hQa hc₁ hcQ hna hb2 ha1 hb2m
    have hXd : (blk P₁ Q a (h.bar a ^ 2)).det = 1 := by
      rw [det_blk hP₁Q, hP₁, hQ, det_one_add_smul_hp h hy₁y₁ hx₁N, det_one_add_smul_rk_self h hl]
      calc (1 + (a - 1)) ^ 2 * (1 + (h.bar a ^ 2 - 1)) = (h.bar a * a) ^ 2 := by ring
        _ = 1 := by rw [hna, one_pow]
    refine ⟨blk P₁ Q a (h.bar a ^ 2), hXu, hXd, by rw [hSN]; exact hXS, hXp, ?_⟩
    have hXx₁ : blk P₁ Q a (h.bar a ^ 2) *ᵥ x₁ = a • x₁ := by
      have hQx₁ : Q *ᵥ x₁ = 0 := by rw [← hP₁x₁, mulVec_mulVec, hQP₁, zero_mulVec]
      rw [blk_mulVec, hP₁x₁, hQx₁, smul_zero, add_zero]
      module
    have hXw : blk P₁ Q a (h.bar a ^ 2) *ᵥ w = h.bar a ^ 2 • w := by
      rw [blk_mulVec, hP₁w, hQw, smul_zero, add_zero]
      module
    intro c
    by_cases hn3 : n = 3
    · have ha3 : a ≠ h.bar a ^ 2 := by
        intro e
        have h3 : a ^ 3 = 1 :=
          calc a ^ 3 = h.bar a ^ 2 * a ^ 2 := by rw [← e]; ring
            _ = (h.bar a * a) ^ 2 := by ring
            _ = 1 := by rw [hna, one_pow]
        have h4 := Nat.le_of_dvd (by norm_num) (ha ▸ orderOf_dvd_of_pow_eq_one h3)
        exact hq ⟨hn3, by omega⟩
      exact ne_scalar_of_eigen hx₁0 hw0 hXx₁ hXw ha3 c
    · obtain ⟨v, hv, hvo⟩ := exists_orth h (m := 3) (by omega) ![x₁, y₁, w]
      have e1 : hf h x₁ v = 0 := hvo 0
      have e2 : hf h y₁ v = 0 := hvo 1
      have e3 : hf h w v = 0 := hvo 2
      have hP₁v : P₁ *ᵥ v = 0 := by
        rw [hP₁, hp, add_mulVec, rk_mulVec, rk_mulVec, e1, e2, zero_smul, zero_smul, add_zero]
      have hQv : Q *ᵥ v = 0 := by rw [hQ, rk_mulVec, e3, zero_smul]
      have hXv : blk P₁ Q a (h.bar a ^ 2) *ᵥ v = (1 : K) • v := by
        rw [blk_mulVec, hP₁v, hQv, smul_zero, smul_zero, add_zero, add_zero, one_smul]
      exact ne_scalar_of_eigen hx₁0 hv hXx₁ hXv hne1 c
  ·
    have hN₂a : adj h (N * M) = N * M := by rw [adj_mul, hMa, hN, hMN]
    obtain ⟨x₂', hx₂'⟩ := exists_hf_ne_zero h hN₂a hN₂
    obtain ⟨x₂'', hx₂''⟩ : ∃ x, x = M *ᵥ x₂' := ⟨_, rfl⟩
    have hP₁x₂'' : P₁ *ᵥ x₂'' = 0 := by rw [hx₂'', mulVec_mulVec, hP₁M, zero_mulVec]
    have hx₂''N : hf h x₂'' (N *ᵥ x₂'') ≠ 0 := by
      have e : M * (N * M) = N * M := by rw [← Matrix.mul_assoc, hMN, Matrix.mul_assoc, hMM]
      rw [hx₂'', hf_mulVec_left, hMa]
      simp only [mulVec_mulVec]
      rw [e]
      exact hx₂'
    obtain ⟨x₂, hx₂N, hx₂x₂, l, t, hx₂eq⟩ := exists_hyp h hN hNN hx₂''N
    have hP₁x₂ : P₁ *ᵥ x₂ = 0 := by
      rw [hx₂eq, mulVec_add, mulVec_smul, mulVec_smul, hP₁x₂'', mulVec_mulVec, hc₁,
        ← mulVec_mulVec, hP₁x₂'', mulVec_zero, smul_zero, smul_zero, add_zero]
    obtain ⟨y₂, hy₂⟩ : ∃ y, y = N *ᵥ x₂ := ⟨_, rfl⟩
    rw [← hy₂] at hx₂N
    have hNy₂ : N *ᵥ y₂ = 0 := by rw [hy₂, hNNv]
    have hy₂y₂ : hf h y₂ y₂ = 0 := by rw [hy₂, hsym, hNNv, hf_zero_right]
    have hP₁y₂ : P₁ *ᵥ y₂ = 0 := by
      rw [hy₂, mulVec_mulVec, hc₁, ← mulVec_mulVec, hP₁x₂, mulVec_zero]
    have hx₂0 : x₂ ≠ 0 := fun h0 => by
      rw [h0, hf_zero_left] at hx₂N
      exact zero_ne_one hx₂N
    obtain ⟨P₂, hP₂⟩ : ∃ P, P = hp h x₂ y₂ := ⟨_, rfl⟩
    have hP₂P₂ : P₂ * P₂ = P₂ := by rw [hP₂]; exact hp_mul_self h hx₂x₂ hy₂y₂ hx₂N
    have hP₂a : adj h P₂ = P₂ := by rw [hP₂]; exact adj_hp h x₂ y₂
    have hP₂x₂ : P₂ *ᵥ x₂ = x₂ := by rw [hP₂]; exact hp_mulVec_left h hx₂x₂ hx₂N
    have hc₂ : P₂ * N = N * P₂ := by
      rw [hP₂, hp, Matrix.add_mul, Matrix.mul_add, rk_mul, rk_mul, mul_rk, mul_rk, hN, hNy₂,
        ← hy₂, rk_zero_left, rk_zero_right, zero_add, add_zero]
    have hP₁P₂ : P₁ * P₂ = 0 := by
      rw [hP₂, hp, Matrix.mul_add, mul_rk, mul_rk, hP₁x₂, hP₁y₂, rk_zero_left, rk_zero_left,
        add_zero]
    have hP₂P₁ : P₂ * P₁ = 0 := by
      rw [hP₂, hp, Matrix.add_mul, rk_mul, rk_mul, hP₁a, hP₁y₂, hP₁x₂, rk_zero_right,
        rk_zero_right, add_zero]
    obtain ⟨hXu, hXS, hXp⟩ := blk_spec h (a := a) (b := h.bar a) (m := 2 ^ f + 1) hP₁P₁ hP₂P₂
      hP₁P₂ hP₂P₁ hP₁a hP₂a hc₁ hc₂ hna hnb ha1 hb1
    have hXd : (blk P₁ P₂ a (h.bar a)).det = 1 := by
      rw [det_blk hP₁P₂, hP₁, hP₂, det_one_add_smul_hp h hy₁y₁ hx₁N,
        det_one_add_smul_hp h hy₂y₂ hx₂N]
      calc (1 + (a - 1)) ^ 2 * (1 + (h.bar a - 1)) ^ 2 = (h.bar a * a) ^ 2 := by ring
        _ = 1 := by rw [hna, one_pow]
    refine ⟨blk P₁ P₂ a (h.bar a), hXu, hXd, by rw [hSN]; exact hXS, hXp, ?_⟩
    have hXx₁ : blk P₁ P₂ a (h.bar a) *ᵥ x₁ = a • x₁ := by
      have hP₂x₁ : P₂ *ᵥ x₁ = 0 := by rw [← hP₁x₁, mulVec_mulVec, hP₂P₁, zero_mulVec]
      rw [blk_mulVec, hP₁x₁, hP₂x₁, smul_zero, add_zero]
      module
    have hXx₂ : blk P₁ P₂ a (h.bar a) *ᵥ x₂ = h.bar a • x₂ := by
      rw [blk_mulVec, hP₁x₂, hP₂x₂, smul_zero, add_zero]
      module
    exact ne_scalar_of_eigen hx₁0 hx₂0 hXx₁ hXx₂ hne2

theorem exists_fixed_odd_of_refl (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2))
    (β : MulAut (PU h n)) (hβ : orderOf β = 2)
    (hid : primeFormFieldFactor h isPrimeFormGram_one hn hq β = RingEquiv.refl K) :
    ∃ y : PU h n, β y = y ∧ y ≠ 1 ∧ y ^ (2 ^ f + 1) = 1 := by
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  obtain ⟨s, hs1, hss, rfl⟩ := (even_unitary_involution_matrix_lifts h hC hn hq β hβ).2.1 hid
  obtain ⟨S, hSdef⟩ : ∃ S, S = ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := ⟨_, rfl⟩
  have hS : adj h S * S = 1 := by
    have h1 : adj h S * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * S =
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [hSdef]
      exact s.2.1
    simpa only [Units.val_one, Matrix.mul_one] using h1
  have hSS : S * S = 1 := by rw [hSdef, ← Units.val_mul, hss, Units.val_one]
  have hS1 : S ≠ 1 := fun h1 => hs1 (Units.ext (by rw [← hSdef, h1, Units.val_one]))
  obtain ⟨X, hXu, hXd, hXS, hXp, hXs⟩ := exists_blk_commuting h hn hq hS hSS hS1
  have hXu' : X * adj h X = 1 := mul_eq_one_comm.mp hXu
  let gX : GL (Fin n) K := ⟨X, adj h X, hXu', hXu⟩
  have hgX : gX ∈ gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    refine ⟨?_, hXd⟩
    change (X.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * X =
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [Units.val_one, Matrix.mul_one]
    exact hXu
  refine ⟨((⟨gX, hgX⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) : PU h n),
    ?_, ?_, ?_⟩
  · rw [primeFormConjHom_mk]
    congr 1
    apply Subtype.ext
    have hc : (s : GL (Fin n) K) * gX = gX * s :=
      Units.ext (by rw [Units.val_mul, Units.val_mul, ← hSdef]; exact hXS.symm)
    change (s : GL (Fin n) K) * gX * (s : GL (Fin n) K)⁻¹ = gX
    rw [hc, mul_inv_cancel_right]
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    obtain ⟨c, -, -, hc⟩ := mem_normOneScalars.mp h1
    apply hXs c
    have h2 := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar] at h2
    exact h2
  · have hpow : (⟨gX, hgX⟩ : gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^
        (2 ^ f + 1) = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one]
      exact hXp
    rw [← QuotientGroup.mk_pow, hpow, QuotientGroup.mk_one]

end CFSG.ComponentClassification.HarrisLit.L33.C2.PSUTwo
