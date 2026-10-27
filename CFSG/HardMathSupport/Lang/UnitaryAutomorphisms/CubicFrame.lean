module

public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.CubicFrameCW
public import CFSG.HardMathSupport.Lang.Proving.CubicIrreducible
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open Matrix CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

variable {h}

theorem exists_inv_comb (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    (c : Fin 3 → K) (hc : c ≠ 0) :
    ∃ U : Matrix (Fin n) (Fin n) K,
      U * (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) = 1 ∧
      (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) * U = 1 := by
  classical
  have hirr := CFSG.HardMathSupport.Lang.Proving.irreducible_X_pow_three_sub_C hl
  set g : Polynomial K := Polynomial.C (c 2) * Polynomial.X ^ 2 + Polynomial.C (c 1) * Polynomial.X +
    Polynomial.C (c 0) with hg
  have hcoef : ∀ k, g.coeff k = if k = 0 then c 0 else if k = 1 then c 1 else if k = 2 then c 2
      else 0 := by
    intro k
    simp only [hg, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    rcases k with _ | _ | _ | k <;> simp
  have hg0 : g ≠ 0 := by
    intro h0
    apply hc
    ext i
    have := hcoef i
    rw [h0, Polynomial.coeff_zero] at this
    fin_cases i <;> simpa using this.symm
  have hdeg : g.natDegree < 3 := by
    have : g.natDegree ≤ 2 := Polynomial.natDegree_quadratic_le
    omega
  have hndvd : ¬ (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) ∣ g := fun hd => by
    have := Polynomial.natDegree_le_of_dvd hd hg0
    rw [Polynomial.natDegree_X_pow_sub_C] at this
    omega
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hndvd
  have hp0 : Polynomial.aeval B (Polynomial.X ^ 3 - Polynomial.C l : Polynomial K) = 0 := by
    simp [hB3, Algebra.algebraMap_eq_smul_one]
  have hgB : Polynomial.aeval B g = c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2 := by
    simp [hg, Algebra.algebraMap_eq_smul_one]
    abel
  have h1 := congrArg (Polynomial.aeval B) hab
  rw [map_add, map_mul, map_mul, hp0, mul_zero, zero_add, map_one] at h1
  have h2 : Polynomial.aeval B g * Polynomial.aeval B b = 1 := by
    rw [← map_mul, mul_comm, map_mul]; exact h1
  rw [hgB] at h1 h2
  exact ⟨Polynomial.aeval B b, h1, h2⟩

theorem cyc_linearIndependent (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    {w : Fin n → K} (hw : w ≠ 0) :
    LinearIndependent K ![w, B *ᵥ w, (B ^ 2) *ᵥ w] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  have hc0 : c ≠ 0 := fun h0 => by obtain ⟨i, hi⟩ := hne; exact hi (by simp [h0])
  obtain ⟨U, hU, -⟩ := exists_inv_comb B hB3 hl c hc0
  apply hw
  have h1 : (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) *ᵥ w = 0 := by
    simpa [Fin.sum_univ_three, Matrix.add_mulVec, Matrix.smul_mulVec] using hc
  calc w = (U * (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2)) *ᵥ w := by
        rw [hU, one_mulVec]
    _ = 0 := by rw [← mulVec_mulVec, h1, mulVec_zero]

theorem exists_dual_vec (B : Matrix (Fin n) (Fin n) K) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l)
    {w : Fin n → K} (hw : w ≠ 0) :
    ∃ f₀ : Fin n → K, hpair h w f₀ = 1 ∧ hpair h w (B *ᵥ f₀) = 0 ∧
      hpair h w ((B ^ 2) *ᵥ f₀) = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin n) K := Matrix.of fun k => (fun i => h.bar (w i)) ᵥ* B ^ (k : ℕ)
  have hind : LinearIndependent K M.row := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    have hc0 : c ≠ 0 := fun h0 => by obtain ⟨i, hi⟩ := hne; exact hi (by simp [h0])
    obtain ⟨U, -, hU⟩ := exists_inv_comb B hB3 hl c hc0
    have h1 : (fun i => h.bar (w i)) ᵥ*
        (c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) = 0 := by
      have := hc
      have e : ∀ k : Fin 3, M.row k = (fun i => h.bar (w i)) ᵥ* B ^ (k : ℕ) := fun k => rfl
      simp only [Fin.sum_univ_three, e] at this
      simpa [Matrix.vecMul_add, Matrix.vecMul_smul] using this
    apply hw
    have : (fun i => h.bar (w i)) = 0 := by
      calc (fun i => h.bar (w i)) = (fun i => h.bar (w i)) ᵥ*
            ((c 0 • (1 : Matrix (Fin n) (Fin n) K) + c 1 • B + c 2 • B ^ 2) * U) := by
            rw [hU, vecMul_one]
        _ = 0 := by rw [← vecMul_vecMul, h1, zero_vecMul]
    ext i
    have := congrFun this i
    simpa using this
  have hrank : M.rank = 3 := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hind]
    simp
  have hrange : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrank]
    simp
  have : (Pi.single 0 1 : Fin 3 → K) ∈ LinearMap.range M.mulVecLin := by
    rw [hrange]; trivial
  obtain ⟨f₀, hf⟩ := this
  have hk : ∀ k : Fin 3, hpair h w ((B ^ (k : ℕ)) *ᵥ f₀) = (Pi.single 0 1 : Fin 3 → K) k := by
    intro k
    rw [← hf]
    show _ = (M *ᵥ f₀) k
    simp only [Matrix.mulVec, M, Matrix.of_apply]
    rw [← Matrix.dotProduct_mulVec]
    rfl
  refine ⟨f₀, ?_, ?_, ?_⟩
  · simpa using hk 0
  · simpa using hk 1
  · simpa using hk 2

theorem hpair_add_left (x y z : Fin n → K) : hpair h (x + y) z = hpair h x z + hpair h y z := by
  simp [hpair, add_mul, Finset.sum_add_distrib]

theorem hpair_smul_left (x y : Fin n → K) (c : K) : hpair h (c • x) y = h.bar c * hpair h x y := by
  simp [hpair, Finset.mul_sum, mul_assoc]

theorem hpair_zero_right (x : Fin n → K) : hpair h x 0 = 0 := by simp [hpair]

theorem hpair_zero_left (x : Fin n → K) : hpair h 0 x = 0 := by simp [hpair]

theorem hpair_pow_shift {B : Matrix (Fin n) (Fin n) K} (hB : (B.map h.bar)ᵀ * B = 1) (a : ℕ)
    (x y : Fin n → K) : hpair h ((B ^ a) *ᵥ x) ((B ^ a) *ᵥ y) = hpair h x y := by
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hpair_mulVec hB, ih]

theorem hpair_pow_pow {B : Matrix (Fin n) (Fin n) K} (hB : (B.map h.bar)ᵀ * B = 1)
    (x y : Fin n → K) (i j : ℕ) :
    hpair h ((B ^ i) *ᵥ x) ((B ^ j) *ᵥ y) =
      if i ≤ j then hpair h x ((B ^ (j - i)) *ᵥ y) else h.bar (hpair h y ((B ^ (i - j)) *ᵥ x)) := by
  split_ifs with hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [pow_add, ← Matrix.mulVec_mulVec, hpair_pow_shift hB, Nat.add_sub_cancel_left]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_le.mp hij).le
    rw [hpair_comm, pow_add, ← Matrix.mulVec_mulVec, hpair_pow_shift hB, Nat.add_sub_cancel_left]

theorem pow_three_mulVec {B : Matrix (Fin n) (Fin n) K} {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (x : Fin n → K) :
    (B ^ 3) *ᵥ x = l • x := by
  rw [hB3, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem exists_adjust (B : Matrix (Fin n) (Fin n) K) (hB : (B.map h.bar)ᵀ * B = 1) {l : K}
    (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K))
    {w f₀ : Fin n → K}
    (hw : ∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ w) ((B ^ (j : ℕ)) *ᵥ w) = 0)
    (hf1 : hpair h w f₀ = 1) (hf2 : hpair h w (B *ᵥ f₀) = 0)
    (hf3 : hpair h w ((B ^ 2) *ᵥ f₀) = 0) :
    ∃ w' : Fin n → K,
      (∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ w') ((B ^ (j : ℕ)) *ᵥ w') = 0) ∧
      ∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ w) ((B ^ (j : ℕ)) *ᵥ w') =
        if i = j then 1 else 0 := by
  classical
  have i0 : ∀ k : ℕ, hpair h w ((B ^ k) *ᵥ w) = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      by_cases hk : k < 3
      · have := hw 0 ⟨k, hk⟩
        simpa using this
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hk)
        rw [add_comm, pow_add, ← Matrix.mulVec_mulVec, pow_three_mulVec hB3, Matrix.mulVec_smul,
          hpair_smul_right, ih m (by omega), mul_zero]
  have i1 : ∀ i j : ℕ, hpair h ((B ^ i) *ᵥ w) ((B ^ j) *ᵥ w) = 0 := by
    intro i j
    rw [hpair_pow_pow hB]
    split_ifs
    · exact i0 _
    · rw [i0, map_zero]
  have hl1 : h.bar l * l = 1 := by
    have := hpair_pow_shift (h := h) hB 3 w f₀
    rw [pow_three_mulVec hB3, pow_three_mulVec hB3, hpair_smul_left, hpair_smul_right, hf1] at this
    linear_combination this
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl1
  have Φ3 : ∀ a b : ℕ, hpair h ((B ^ a) *ᵥ w) ((B ^ (b + 3)) *ᵥ f₀) =
      l * hpair h ((B ^ a) *ᵥ w) ((B ^ b) *ᵥ f₀) := by
    intro a b
    rw [pow_add, ← Matrix.mulVec_mulVec, pow_three_mulVec hB3, Matrix.mulVec_smul,
      hpair_smul_right]
  have Φ10 : hpair h (B *ᵥ w) f₀ = 0 := by
    have e1 := Φ3 1 0
    rw [hpair_pow_pow hB] at e1
    norm_num at e1
    rw [hf3] at e1
    simpa [hl0] using e1.symm
  have Φ20 : hpair h ((B ^ 2) *ᵥ w) f₀ = 0 := by
    have e1 := Φ3 2 0
    rw [hpair_pow_pow hB] at e1
    norm_num at e1
    rw [hf2] at e1
    simpa [hl0] using e1.symm
  have Φ21 : hpair h ((B ^ 2) *ᵥ w) (B *ᵥ f₀) = 0 := by
    have e1 := Φ3 2 1
    rw [hpair_pow_pow hB] at e1
    norm_num at e1
    rw [hf3] at e1
    simpa [hl0] using e1.symm
  have Φ22 : hpair h ((B ^ 2) *ᵥ w) ((B ^ 2) *ᵥ f₀) = 1 := by
    rw [hpair_pow_shift hB, hf1]
  have q1 : hpair h f₀ w = 1 := by rw [hpair_comm, hf1, map_one]
  have q2 : hpair h f₀ (B *ᵥ w) = 0 := by rw [hpair_comm, Φ10, map_zero]
  have q3 : hpair h f₀ ((B ^ 2) *ᵥ w) = 0 := by rw [hpair_comm, Φ20, map_zero]
  have q4 : hpair h f₀ ((B ^ 3) *ᵥ w) = l := by
    rw [pow_three_mulVec hB3, hpair_smul_right, q1, mul_one]
  have q5 : hpair h f₀ ((B ^ 4) *ᵥ w) = 0 := by
    have : (B ^ 4) *ᵥ w = l • (B *ᵥ w) := by
      rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, ← Matrix.mulVec_mulVec, pow_three_mulVec hB3,
        Matrix.mulVec_smul, pow_one]
    rw [this, hpair_smul_right, q2, mul_zero]
  have a2 : hpair h f₀ ((B ^ 2) *ᵥ f₀) = l * h.bar (hpair h f₀ (B *ᵥ f₀)) := by
    have := hpair_pow_shift (h := h) hB 1 f₀ ((B ^ 2) *ᵥ f₀)
    rw [pow_one, Matrix.mulVec_mulVec, ← pow_succ', pow_three_mulVec hB3, hpair_smul_right,
      hpair_comm f₀ (B *ᵥ f₀)] at this
    exact this.symm
  have expand : ∀ (g₀ g₂ : K) (m : ℕ),
      hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))
        ((B ^ m) *ᵥ (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))) =
      hpair h f₀ ((B ^ m) *ᵥ f₀) + g₀ * hpair h f₀ ((B ^ m) *ᵥ w) +
        g₂ * hpair h f₀ ((B ^ (m + 2)) *ᵥ w) + h.bar g₀ * hpair h w ((B ^ m) *ᵥ f₀) +
        h.bar g₂ * hpair h ((B ^ 2) *ᵥ w) ((B ^ m) *ᵥ f₀) := by
    intro g₀ g₂ m
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add,
      hpair_add_left, hpair_add_right, hpair_smul_left, hpair_smul_right, i0, i1]
    ring
  have E2 : ∀ (g₀ g₂ : K) (m : ℕ), hpair h w ((B ^ m) *ᵥ (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))) =
      hpair h w ((B ^ m) *ᵥ f₀) := by
    intro g₀ g₂ m
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← pow_add,
      hpair_add_right, hpair_smul_right, i0]
    ring
  have E3 : ∀ (g₀ g₂ : K) (m : ℕ), hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w)) ((B ^ m) *ᵥ w) =
      hpair h f₀ ((B ^ m) *ᵥ w) := by
    intro g₀ g₂ m
    simp only [hpair_add_left, hpair_smul_left, i0, i1]
    ring
  have ha0 : h.bar (hpair h f₀ f₀) = hpair h f₀ f₀ := (hpair_comm f₀ f₀).symm
  have hmem : -hpair h f₀ f₀ ∈ h.fixedField := neg_mem (h.mem_fixedField.mpr ha0)
  obtain ⟨g₀, hg₀⟩ := h.traceLin_surjective ⟨_, hmem⟩
  have hg₀' : g₀ + h.bar g₀ = -hpair h f₀ f₀ := congrArg Subtype.val hg₀
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : K, g₂ = -hpair h f₀ (B *ᵥ f₀) * h.bar l := ⟨_, rfl⟩
  have hg₂b : h.bar g₂ = -h.bar (hpair h f₀ (B *ᵥ f₀)) * l := by
    rw [hg₂, map_mul, map_neg, h.bar_bar]
  have T0 : hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w)) (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w)) = 0 := by
    have E := expand g₀ g₂ 0
    simp only [pow_zero, Matrix.one_mulVec, zero_add] at E
    rw [E, q1, q3, hf1, Φ20]
    linear_combination hg₀'
  have T1 : hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))
      (B *ᵥ (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))) = 0 := by
    have E := expand g₀ g₂ 1
    rw [show (1 + 2 : ℕ) = 3 from rfl, pow_one] at E
    rw [E, q2, q4, hf2, Φ21]
    linear_combination (-hpair h f₀ (B *ᵥ f₀)) * hl1 + l * hg₂
  have T2 : hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))
      ((B ^ 2) *ᵥ (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))) = 0 := by
    have E := expand g₀ g₂ 2
    rw [show (2 + 2 : ℕ) = 4 from rfl] at E
    rw [E, a2, q3, q5, hf3, Φ22]
    linear_combination hg₂b
  have key : ∀ k : ℕ, k < 3 → hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))
      ((B ^ k) *ᵥ (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))) = 0 := by
    intro k hk
    interval_cases k
    · simpa using T0
    · simpa using T1
    · exact T2
  have K2 : ∀ k : ℕ, k < 3 → hpair h w ((B ^ k) *ᵥ (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w))) =
      if k = 0 then 1 else 0 := by
    intro k hk
    rw [E2]
    interval_cases k
    · simpa using hf1
    · simpa using hf2
    · simpa using hf3
  have K3 : ∀ k : ℕ, 0 < k → k < 3 →
      hpair h (f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w)) ((B ^ k) *ᵥ w) = 0 := by
    intro k hk0 hk
    rw [E3]
    interval_cases k
    · simpa using q2
    · exact q3
  refine ⟨f₀ + g₀ • w + g₂ • ((B ^ 2) *ᵥ w), ?_, ?_⟩
  · intro i j
    rw [hpair_pow_pow hB]
    have hi := i.2
    have hj := j.2
    split_ifs with hij
    · exact key _ (by omega)
    · rw [key _ (by omega), map_zero]
  · intro i j
    rw [hpair_pow_pow hB]
    have hi := i.2
    have hj := j.2
    by_cases hij : (i : ℕ) ≤ j
    · simp only [hij, ↓reduceIte]
      rw [K2 _ (by omega)]
      simp only [Fin.ext_iff]
      by_cases h0 : (j : ℕ) - i = 0 <;> simp [h0] <;> omega
    · simp only [hij, ↓reduceIte]
      rw [K3 _ (by omega) (by omega), map_zero]
      have : i ≠ j := fun h => hij (by rw [h])
      simp [this]

theorem exists_frame (hn : 6 ≤ n) (B : Matrix (Fin n) (Fin n) K) (hB : (B.map h.bar)ᵀ * B = 1)
    {l : K} (hB3 : B ^ 3 = l • (1 : Matrix (Fin n) (Fin n) K)) (hl : ∀ x : K, x ^ 3 ≠ l) :
    ∃ w w' : Fin n → K, w ≠ 0 ∧
      (∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ w) ((B ^ (j : ℕ)) *ᵥ w) = 0) ∧
      (∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ w') ((B ^ (j : ℕ)) *ᵥ w') = 0) ∧
      ∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ w) ((B ^ (j : ℕ)) *ᵥ w') =
        if i = j then 1 else 0 := by
  obtain ⟨v, hv0, hv1, hv2⟩ := exists_isotropic_vec h (by omega : 4 ≤ n) B
  have h2 : hpair h v ((B ^ 2) *ᵥ v) = 0 := by
    have := hpair_pow_shift (h := h) hB 1 v ((B ^ 2) *ᵥ v)
    rw [pow_one, Matrix.mulVec_mulVec, ← pow_succ', pow_three_mulVec hB3, hpair_smul_right,
      hpair_comm v (B *ᵥ v), hv2, map_zero, mul_zero] at this
    exact this.symm
  have hk : ∀ k : ℕ, k < 3 → hpair h v ((B ^ k) *ᵥ v) = 0 := by
    intro k hk
    interval_cases k
    · simpa using hv1
    · simpa using hv2
    · exact h2
  have hw : ∀ i j : Fin 3, hpair h ((B ^ (i : ℕ)) *ᵥ v) ((B ^ (j : ℕ)) *ᵥ v) = 0 := by
    intro i j
    rw [hpair_pow_pow hB]
    have hi := i.2
    have hj := j.2
    split_ifs with hij
    · exact hk _ (by omega)
    · rw [hk _ (by omega), map_zero]
  obtain ⟨f₀, hf1, hf2, hf3⟩ := exists_dual_vec (h := h) B hB3 hl hv0
  obtain ⟨w', hw'1, hw'2⟩ := exists_adjust B hB hB3 hw hf1 hf2 hf3
  exact ⟨v, w', hv0, hw, hw'1, hw'2⟩

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
