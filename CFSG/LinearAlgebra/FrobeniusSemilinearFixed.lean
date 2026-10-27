module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.LinearAlgebra

variable {L : Type*} [Field L] [IsAlgClosed L]

omit [IsAlgClosed L] in
private lemma frobFix_sigma_iterate_pow {σ : L →+* L} {Q : ℕ} (hσ : ∀ c, σ c = c ^ Q)
    (n : ℕ) (c : L) : σ^[n] c = c ^ Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, hσ, ← pow_mul, ← pow_succ]

omit [IsAlgClosed L] in
private lemma frobFix_sigma_iterate_zero {σ : L →+* L} (n : ℕ) : σ^[n] (0 : L) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

omit [IsAlgClosed L] in
private lemma frobFix_exists_max {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] (w : ℕ → V) (hw0 : w 0 ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ LinearIndependent L (fun i : Fin m => w i) ∧
      ¬ LinearIndependent L (fun i : Fin (m + 1) => w i) := by
  classical
  have hdep : ∃ n : ℕ, ¬ LinearIndependent L (fun i : Fin n => w i) := by
    refine ⟨Module.finrank L V + 1, fun hli => ?_⟩
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at hle
    omega
  let n := Nat.find hdep
  have hn : ¬ LinearIndependent L (fun i : Fin n => w i) := Nat.find_spec hdep
  have hn_min : ∀ k, k < n → LinearIndependent L (fun i : Fin k => w i) := by
    intro k hk
    by_contra h
    have hle : n ≤ k := Nat.find_min' hdep h
    omega
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0] at hn
    exact hn linearIndependent_empty_type
  have hn1 : n ≠ 1 := by
    intro h0
    rw [h0] at hn
    exact hn (by
      rw [linearIndependent_unique_iff]
      simpa using hw0)
  refine ⟨n - 1, by omega, hn_min (n - 1) (by omega), ?_⟩
  rw [show n - 1 + 1 = n from Nat.sub_add_cancel (by omega)]
  exact hn

private def frobFix_x (σ : L →+* L) (A : ℕ → L) (y : L) : ℕ → L
  | 0 => A 0 * σ y
  | n + 1 => σ (frobFix_x σ A y n) + A (n + 1) * σ y

omit [IsAlgClosed L] in
private lemma frobFix_x_eq_sum {σ : L →+* L} {A : ℕ → L} {y : L} (n : ℕ) :
    frobFix_x σ A y n =
      ∑ j ∈ Finset.range (n + 1), σ^[n - j] (A j) * σ^[n - j + 1] y := by
  induction n with
  | zero => simp [frobFix_x]
  | succ n ih =>
    change σ (frobFix_x σ A y n) + A (n + 1) * σ y =
      ∑ j ∈ Finset.range (n + 1 + 1), σ^[n + 1 - j] (A j) * σ^[n + 1 - j + 1] y
    rw [ih, map_sum]
    conv_rhs => rw [Finset.sum_range_succ]
    have hsum : (∑ j ∈ Finset.range (n + 1),
          σ (σ^[n - j] (A j) * σ^[n - j + 1] y)) =
        ∑ j ∈ Finset.range (n + 1),
          σ^[n + 1 - j] (A j) * σ^[n + 1 - j + 1] y := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hj' : j < n + 1 := Finset.mem_range.mp hj
      have h1 : n - j + 1 = n + 1 - j := by omega
      rw [map_mul, ← h1, Function.iterate_succ_apply' σ (n - j) (A j),
        Function.iterate_succ_apply' σ (n - j + 1) y]
    rw [hsum]
    congr 1
    simp

private lemma frobFix_exists_root {Q : ℕ} (hQ : 2 ≤ Q) {m : ℕ} (b : ℕ → L)
    (hb : ∃ j, j < m ∧ b j ≠ 0) :
    ∃ y : L, y ≠ 0 ∧ ∑ j ∈ Finset.range m, b j * y ^ Q ^ (m - j) = y := by
  classical
  obtain ⟨j, hj, hbj⟩ := hb
  have hpow_inj : Function.Injective (fun n : ℕ => Q ^ n) := Nat.pow_right_injective hQ
  have hpos : ∀ i ∈ Finset.range m, 0 < Q ^ (m - i) - 1 := by
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have h1 : 1 < Q ^ (m - i) := by
      have h0 : 0 < m - i := by omega
      simpa using (pow_right_strictMono₀ (show 1 < Q by omega) h0)
    omega
  have hexp_ne : ∀ i ∈ Finset.range m, i ≠ j → Q ^ (m - i) - 1 ≠ Q ^ (m - j) - 1 := by
    intro i hi hij heq
    have hi' : i < m := Finset.mem_range.mp hi
    have h1 : 1 ≤ Q ^ (m - i) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ Q ^ (m - j) := Nat.one_le_pow _ _ (by omega)
    have hpow : Q ^ (m - i) = Q ^ (m - j) := by omega
    have hsub : m - i = m - j := hpow_inj hpow
    omega
  let R : Polynomial L :=
    ∑ i ∈ Finset.range m, Polynomial.C (b i) * Polynomial.X ^ (Q ^ (m - i) - 1) - 1
  have hsumcoeff : (∑ i ∈ Finset.range m,
        Polynomial.C (b i) * Polynomial.X ^ (Q ^ (m - i) - 1)).coeff (Q ^ (m - j) - 1) =
      b j := by
    rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single j]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro i hi hij
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      exact fun h => hexp_ne i hi hij h.symm
    · intro hnot
      exact absurd (Finset.mem_range.mpr hj) hnot
  have hcoeff : R.coeff (Q ^ (m - j) - 1) = b j := by
    dsimp only [R]
    rw [Polynomial.coeff_sub, Polynomial.coeff_one,
      if_neg (ne_of_gt (hpos j (Finset.mem_range.mpr hj))), hsumcoeff]
    ring
  have hdeg : R.degree ≠ 0 := by
    have hle := Polynomial.le_degree_of_ne_zero (p := R) (n := Q ^ (m - j) - 1)
      (by rw [hcoeff]; exact hbj)
    have hpos' : 0 < Q ^ (m - j) - 1 := hpos j (Finset.mem_range.mpr hj)
    intro h0
    have hle' : ((Q ^ (m - j) - 1 : ℕ) : WithBot ℕ) ≤ 0 := by rw [h0] at hle; exact hle
    have hle'' : Q ^ (m - j) - 1 ≤ 0 := by
      exact WithBot.coe_le_coe.mp (by simpa using hle')
    omega
  obtain ⟨y, hyroot⟩ := IsAlgClosed.exists_root R hdeg
  have hyeval : R.eval y = 0 := Polynomial.IsRoot.def.mp hyroot
  have hR0 : R.eval 0 = -1 := by
    have hcoeff0 : R.coeff 0 = -1 := by
      dsimp only [R]
      rw [Polynomial.coeff_sub, Polynomial.coeff_one, if_pos rfl,
        Polynomial.finset_sum_coeff]
      have hzero : ∀ i ∈ Finset.range m,
          (Polynomial.C (b i) * Polynomial.X ^ (Q ^ (m - i) - 1)).coeff 0 = 0 := by
        intro i hi
        rw [Polynomial.coeff_C_mul_X_pow, if_neg]
        exact fun h => (ne_of_gt (hpos i hi)) h.symm
      rw [Finset.sum_eq_zero hzero]
      ring
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hcoeff0
  have hy_ne : y ≠ 0 := by
    intro h0
    rw [h0, hR0] at hyeval
    exact one_ne_zero (neg_eq_zero.mp hyeval)
  have hsum1 : ∑ i ∈ Finset.range m, b i * y ^ (Q ^ (m - i) - 1) = 1 := by
    have h := hyeval
    dsimp only [R] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at h
    exact sub_eq_zero.mp h
  refine ⟨y, hy_ne, ?_⟩
  have hmul : y * (∑ i ∈ Finset.range m, b i * y ^ (Q ^ (m - i) - 1)) = y := by
    rw [hsum1, mul_one]
  calc ∑ i ∈ Finset.range m, b i * y ^ Q ^ (m - i)
      = ∑ i ∈ Finset.range m, y * (b i * y ^ (Q ^ (m - i) - 1)) := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hle : 1 ≤ Q ^ (m - i) := Nat.one_le_pow _ _ (by omega)
        calc b i * y ^ Q ^ (m - i)
            = b i * y ^ (Q ^ (m - i) - 1 + 1) := by rw [Nat.sub_add_cancel hle]
          _ = b i * (y * y ^ (Q ^ (m - i) - 1)) := by rw [pow_succ']
          _ = y * (b i * y ^ (Q ^ (m - i) - 1)) := by ring
    _ = y * ∑ i ∈ Finset.range m, b i * y ^ (Q ^ (m - i) - 1) := by
        rw [Finset.mul_sum]
    _ = y := hmul

omit [IsAlgClosed L] in
private lemma frobFix_phi_sum {V : Type*} [AddCommGroup V] [Module L V] {σ : L →+* L}
    {φ : V →ₛₗ[σ] V} {w : ℕ → V} (hw : ∀ i, w (i + 1) = φ (w i)) {k : ℕ}
    {A : ℕ → L} {y : L} (hx_last : frobFix_x σ A y k = y)
    (hwrel : ∑ i ∈ Finset.range (k + 1), A i • w i = w (k + 1)) :
    φ (∑ i ∈ Finset.range (k + 1), frobFix_x σ A y i • w i) =
      ∑ i ∈ Finset.range (k + 1), frobFix_x σ A y i • w i := by
  have hx0 : frobFix_x σ A y 0 = A 0 * σ y := rfl
  have hxsucc : ∀ i, frobFix_x σ A y (i + 1) =
      σ (frobFix_x σ A y i) + A (i + 1) * σ y := fun i => rfl
  have hφW : φ (∑ i ∈ Finset.range (k + 1), frobFix_x σ A y i • w i) =
      ∑ i ∈ Finset.range (k + 1), σ (frobFix_x σ A y i) • w (i + 1) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smulₛₗ, hw i]
  have hsplit : φ (∑ i ∈ Finset.range (k + 1), frobFix_x σ A y i • w i) =
      (∑ i ∈ Finset.range k, σ (frobFix_x σ A y i) • w (i + 1)) +
        σ (frobFix_x σ A y k) • w (k + 1) := by
    rw [hφW]
    conv_lhs => rw [Finset.sum_range_succ]
  have hexpand : σ (frobFix_x σ A y k) • w (k + 1) =
      (∑ i ∈ Finset.range k, (σ (frobFix_x σ A y k) * A (i + 1)) • w (i + 1)) +
        (σ (frobFix_x σ A y k) * A 0) • w 0 := by
    rw [show w (k + 1) = ∑ i ∈ Finset.range (k + 1), A i • w i from hwrel.symm,
      Finset.smul_sum]
    conv_lhs => rw [Finset.sum_range_succ']
    simp only [smul_smul]
  have hφW' : φ (∑ i ∈ Finset.range (k + 1), frobFix_x σ A y i • w i) =
      (∑ i ∈ Finset.range k,
        (σ (frobFix_x σ A y i) + σ (frobFix_x σ A y k) * A (i + 1)) • w (i + 1)) +
        (σ (frobFix_x σ A y k) * A 0) • w 0 := by
    rw [hsplit, hexpand]
    have hS : (∑ i ∈ Finset.range k, σ (frobFix_x σ A y i) • w (i + 1)) +
        (∑ i ∈ Finset.range k, (σ (frobFix_x σ A y k) * A (i + 1)) • w (i + 1)) =
        ∑ i ∈ Finset.range k,
          (σ (frobFix_x σ A y i) + σ (frobFix_x σ A y k) * A (i + 1)) • w (i + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [add_smul]
    rw [← hS]
    abel
  have hW' : (∑ i ∈ Finset.range (k + 1), frobFix_x σ A y i • w i) =
      (∑ i ∈ Finset.range k, frobFix_x σ A y (i + 1) • w (i + 1)) +
        frobFix_x σ A y 0 • w 0 := by
    conv_lhs => rw [Finset.sum_range_succ']
  rw [hφW', hW', hx_last]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hxsucc i]
    congr 1
    ring
  · rw [hx0]
    congr 1
    ring

omit [IsAlgClosed L] in
private lemma frobFix_sum_ne_zero {V : Type*} [AddCommGroup V] [Module L V] {w : ℕ → V}
    {k : ℕ} (hli : LinearIndependent L (fun i : Fin (k + 1) => w ↑i)) {x : ℕ → L} {y : L}
    (hx : x k = y) (hy : y ≠ 0) :
    ∑ i ∈ Finset.range (k + 1), x i • w i ≠ 0 := by
  intro h0
  have hsum0 : ∑ i : Fin (k + 1), x ↑i • w ↑i = 0 := by
    rw [← Finset.sum_range (f := fun i => x i • w i)]
    rw [show (∑ i ∈ Finset.range (k + 1), x i • w i) = 0 from h0]
  have hx_all : ∀ i : Fin (k + 1), x ↑i = 0 :=
    (Fintype.linearIndependent_iff.mp hli) (fun i : Fin (k + 1) => x ↑i) hsum0
  have hk0 : x k = 0 := hx_all ⟨k, by omega⟩
  rw [hx] at hk0
  exact hy hk0

theorem exists_ne_zero_fixed_of_frobeniusSemilinear {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] [Nontrivial V] {σ : L →+* L} {Q : ℕ} (hQ : 2 ≤ Q)
    (hσ : ∀ c, σ c = c ^ Q) (φ : V →ₛₗ[σ] V) (hφ : Function.Injective φ) :
    ∃ v : V, v ≠ 0 ∧ φ v = v := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let w : ℕ → V := fun i => φ^[i] v
  have hw0 : w 0 ≠ 0 := hv
  obtain ⟨m, hm, hli, hdep⟩ := frobFix_exists_max (L := L) w hw0
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hmem : w (k + 1) ∈ Submodule.span L (Set.range (fun i : Fin (k + 1) => w ↑i)) := by
    have h := mt (linearIndependent_fin_succ' (K := L) (n := k + 1)
      (v := fun i : Fin ((k + 1) + 1) => (w ↑i : V))).mpr hdep
    rcases (not_and_or.mp h) with h1 | h2
    · exact absurd hli h1
    · exact not_not.mp h2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem
  let A : ℕ → L := fun i => if h : i < k + 1 then a ⟨i, h⟩ else 0
  have hA : ∀ i (h : i < k + 1), A i = a ⟨i, h⟩ := fun i h => dif_pos h
  have hwrel : ∑ i ∈ Finset.range (k + 1), A i • w i = w (k + 1) := by
    rw [Finset.sum_range]
    have hsum : (∑ i : Fin (k + 1), A ↑i • w ↑i) = ∑ i : Fin (k + 1), a i • w ↑i := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hA ↑i i.isLt]
    rw [hsum]
    exact ha
  have hwm : w (k + 1) ≠ 0 := by
    have hz : ∀ n, φ^[n] (0 : V) = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]
    intro h0
    have h1 : φ^[k + 1] v = φ^[k + 1] 0 := by
      rw [show φ^[k + 1] v = 0 from h0, hz]
    exact hv ((hφ.iterate (k + 1)) h1)
  have hex : ∃ i : Fin (k + 1), a i ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : w (k + 1) = 0 := by
      rw [← ha]
      exact Finset.sum_eq_zero (fun i _ => by rw [h i, zero_smul])
    exact hwm hzero
  have hσinj : Function.Injective σ := RingHom.injective σ
  let b : ℕ → L := fun i => σ^[k - i] (A i)
  have hb : ∃ i, i < k + 1 ∧ b i ≠ 0 := by
    obtain ⟨i, hi⟩ := hex
    refine ⟨↑i, i.isLt, ?_⟩
    have hAi : A ↑i = a i := hA ↑i i.isLt
    intro h0
    have h0' : σ^[k - ↑i] (A ↑i) = σ^[k - ↑i] (0 : L) := by
      rw [frobFix_sigma_iterate_zero]
      exact h0
    have hzero : A ↑i = 0 := (hσinj.iterate (k - ↑i)) h0'
    rw [hAi] at hzero
    exact hi hzero
  obtain ⟨y, hy_ne, hy_eq⟩ := frobFix_exists_root hQ (m := k + 1) b hb
  let x : ℕ → L := frobFix_x σ A y
  let W : V := ∑ i ∈ Finset.range (k + 1), x i • w i
  have hx_last : x k = y := by
    have hxk : x k = frobFix_x σ A y k := rfl
    rw [hxk, frobFix_x_eq_sum]
    calc ∑ i ∈ Finset.range (k + 1), σ^[k - i] (A i) * σ^[k - i + 1] y
        = ∑ i ∈ Finset.range (k + 1), b i * y ^ Q ^ (k + 1 - i) := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have hi' : i < k + 1 := Finset.mem_range.mp hi
          have h1 : k - i + 1 = k + 1 - i := by omega
          rw [h1, frobFix_sigma_iterate_pow hσ (k + 1 - i) y]
      _ = y := hy_eq
  have hw : ∀ i, w (i + 1) = φ (w i) := fun i => Function.iterate_succ_apply' φ i v
  have hfixed : φ W = W := by
    rw [show W = ∑ i ∈ Finset.range (k + 1), x i • w i from rfl]
    exact frobFix_phi_sum hw hx_last hwrel
  have hW_ne : W ≠ 0 := by
    rw [show W = ∑ i ∈ Finset.range (k + 1), x i • w i from rfl]
    exact frobFix_sum_ne_zero hli hx_last hy_ne
  exact ⟨W, hW_ne, hfixed⟩

end CFSG.LinearAlgebra
