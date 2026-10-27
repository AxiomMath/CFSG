module

public import Mathlib

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix

namespace HeisAux

variable {K : Type} [Field K]

@[expose] def W (g h : GL (Fin 3) K) (d : Kˣ) : Prop :=
  g * h * g⁻¹ = h * Matrix.GeneralLinearGroup.scalar (Fin 3) d

local notation "S" => Matrix.GeneralLinearGroup.scalar (Fin 3)

lemma conj_scalar (g : GL (Fin 3) K) (d : Kˣ) : g * S d * g⁻¹ = S d := by
  rw [← Matrix.GeneralLinearGroup.scalar_commute]; group

lemma W_mul_left {g g' h : GL (Fin 3) K} {d d' : Kˣ} (hg : W g h d) (hg' : W g' h d') :
    W (g * g') h (d * d') := by
  unfold W at *
  have e : g * g' * h * (g * g')⁻¹ = g * (g' * h * g'⁻¹) * g⁻¹ := by group
  have e2 : g * (h * S d') * g⁻¹ = (g * h * g⁻¹) * (g * S d' * g⁻¹) := by group
  rw [e, hg', e2, hg, conj_scalar, mul_assoc, ← map_mul]

lemma W_inv_left {g h : GL (Fin 3) K} {d : Kˣ} (hg : W g h d) : W g⁻¹ h d⁻¹ := by
  unfold W at *
  rw [mul_inv_eq_iff_eq_mul] at hg ⊢
  have c1 := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) d g
  have e : h * g = g * h * S d⁻¹ := by
    calc h * g = h * g * (S d * S d⁻¹) := by rw [← map_mul]; simp
      _ = h * (S d * g) * S d⁻¹ := by rw [c1]; group
      _ = h * S d * g * S d⁻¹ := by group
      _ = g * h * S d⁻¹ := by rw [hg]
  calc g⁻¹ * h = g⁻¹ * (h * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * h * S d⁻¹) * g⁻¹ := by rw [e]
    _ = h * S d⁻¹ * g⁻¹⁻¹⁻¹ := by group

lemma W_mul_right {g h h' : GL (Fin 3) K} {d d' : Kˣ} (hg : W g h d) (hg' : W g h' d') :
    W g (h * h') (d * d') := by
  unfold W at *
  have e : g * (h * h') * g⁻¹ = (g * h * g⁻¹) * (g * h' * g⁻¹) := by group
  rw [e, hg, hg']
  rw [map_mul]
  have := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) d h'
  calc h * S d * (h' * S d') = h * (S d * h') * S d' := by group
    _ = _ := by rw [this]; group

lemma W_pow {g h : GL (Fin 3) K} {d : Kˣ} (hg : W g h d) (n : ℕ) : W g (h ^ n) (d ^ n) := by
  induction n with
  | zero => unfold W; simp
  | succ n ih => rw [pow_succ, pow_succ]; exact W_mul_right ih hg

lemma W_pow_left {g h : GL (Fin 3) K} {d : Kˣ} (hg : W g h d) (n : ℕ) : W (g ^ n) h (d ^ n) := by
  induction n with
  | zero => unfold W; simp
  | succ n ih => rw [pow_succ, pow_succ]; exact W_mul_left ih hg

lemma W_inv_right {g h : GL (Fin 3) K} {d : Kˣ} (hg : W g h d) : W g h⁻¹ d⁻¹ := by
  unfold W at *
  calc g * h⁻¹ * g⁻¹ = (g * h * g⁻¹)⁻¹ := by group
    _ = (h * S d)⁻¹ := by rw [hg]
    _ = S d⁻¹ * h⁻¹ := by rw [_root_.mul_inv_rev, ← map_inv]
    _ = h⁻¹ * S d⁻¹ := Matrix.GeneralLinearGroup.scalar_commute _ _

lemma W_self (g : GL (Fin 3) K) : W g g 1 := by
  unfold W; simp

lemma W_matrix {g h : GL (Fin 3) K} {d : Kˣ} (hg : W g h d) :
    (g : Matrix (Fin 3) (Fin 3) K) * h = (d : K) • ((h : Matrix (Fin 3) (Fin 3) K) * g) := by
  unfold W at hg
  rw [mul_inv_eq_iff_eq_mul] at hg
  have c1 := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) d g
  have : g * h = h * g * S d := by rw [hg, mul_assoc, c1, mul_assoc]
  have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) this
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one] at this
  exact this

lemma coeff_aux {ι : Type} [Fintype ι] (Y : ι → Matrix (Fin 3) (Fin 3) K)
    (hli : LinearIndependent K Y) (x : ι → K) (g : GL (Fin 3) K) (d : ι → Kˣ)
    (hW : ∀ p, (g : Matrix (Fin 3) (Fin 3) K) * Y p = (d p : K) • (Y p * g))
    (hN : (g : Matrix (Fin 3) (Fin 3) K) * (∑ p, x p • Y p) = (∑ p, x p • Y p) * g) :
    ∀ p, x p * ((d p : K) - 1) = 0 := by
  have h1 : (∑ p, (x p * ((d p : K) - 1)) • Y p) * (g : Matrix (Fin 3) (Fin 3) K) = 0 := by
    have : (g : Matrix (Fin 3) (Fin 3) K) * (∑ p, x p • Y p) - (∑ p, x p • Y p) * g = 0 :=
      sub_eq_zero.mpr hN
    rw [← this, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mul_smul, hW p, smul_smul, Matrix.smul_mul, Matrix.smul_mul, ← sub_smul]
    congr 1; ring
  have h2 : ∑ p, (x p * ((d p : K) - 1)) • Y p = 0 := by
    have := congrArg (fun N => N * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [Matrix.mul_assoc, ← Units.val_mul] using this
  exact Fintype.linearIndependent_iff.mp hli _ h2

lemma trace_zero_of_W {g h : GL (Fin 3) K} {d : Kˣ} (hg : W g h d) (hd : d ≠ 1) :
    Matrix.trace (h : Matrix (Fin 3) (Fin 3) K) = 0 := by
  have h1 : Matrix.trace ((g * h * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = Matrix.trace (h : Matrix (Fin 3) (Fin 3) K) := by
    simpa using Matrix.trace_units_conj g (h : Matrix (Fin 3) (Fin 3) K)
  unfold W at hg
  rw [hg] at h1
  simp [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal ] at h1
  have h2 : ((d : Kˣ) : K) ≠ 1 := fun e => hd (Units.ext e)
  have h3 : (((d : Kˣ) : K) - 1) * Matrix.trace (h : Matrix (Fin 3) (Fin 3) K) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact h1
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h2)

def Yg (A B : GL (Fin 3) K) (p : Fin 3 × Fin 3) : GL (Fin 3) K :=
  A ^ (p.1 : ℕ) * B ^ (p.2 : ℕ)

section Heis

variable {c : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {A B : GL (Fin 3) K}
  (hAB : A * B = B * A * S c)

include hAB in
lemma WAB : W A B c := by
  unfold W
  rw [mul_inv_eq_iff_eq_mul, hAB]
  have c1 := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) c A
  rw [mul_assoc, ← c1, mul_assoc]

include hAB in
lemma WBA : W B A c⁻¹ := by
  unfold W
  rw [mul_inv_eq_iff_eq_mul]
  have c1 := Matrix.GeneralLinearGroup.scalar_commute (n := Fin 3) c⁻¹ B
  have e : B * A = A * B * S c⁻¹ := by
    rw [hAB, mul_assoc, ← map_mul]; simp
  rw [mul_assoc, c1, ← mul_assoc, ← e]

include hAB in
lemma WA_Y (p : Fin 3 × Fin 3) : W A (Yg A B p) (c ^ (p.2 : ℕ)) := by
  have := W_mul_right (W_pow (W_self A) (p.1 : ℕ)) (W_pow (WAB hAB) (p.2 : ℕ))
  simpa [Yg] using this

include hAB in
lemma WB_Y (p : Fin 3 × Fin 3) : W B (Yg A B p) ((c⁻¹) ^ (p.1 : ℕ)) := by
  have := W_mul_right (W_pow (WBA hAB) (p.1 : ℕ)) (W_pow (W_self B) (p.2 : ℕ))
  simpa [Yg] using this

include hc3 hc1 in
lemma pow_inj3 {i j : ℕ} (hi : i < 3) (hj : j < 3) (h : c ^ i = c ^ j) : i = j := by
  have ho : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  rw [pow_eq_pow_iff_modEq, ho] at h
  exact Nat.ModEq.eq_of_lt_of_lt h hi hj

include hc3 hc1 hAB in
lemma trace_Yg_inv_mul {p q : Fin 3 × Fin 3} (hpq : p ≠ q) :
    Matrix.trace ((((Yg A B q)⁻¹ * Yg A B p : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) = 0 := by
  by_cases hj : p.2 = q.2
  · have hi : p.1 ≠ q.1 := fun hi => hpq (Prod.ext hi hj)
    refine trace_zero_of_W (g := B) (d := ((c⁻¹) ^ (q.1 : ℕ))⁻¹ * (c⁻¹) ^ (p.1 : ℕ))
      (W_mul_right (W_inv_right (WB_Y hAB q)) (WB_Y hAB p)) ?_
    intro h
    rw [inv_mul_eq_one, inv_pow, inv_pow, _root_.inv_inj] at h
    exact hi (Fin.ext (pow_inj3 hc3 hc1 q.1.2 p.1.2 h).symm)
  · refine trace_zero_of_W (g := A) (d := (c ^ (q.2 : ℕ))⁻¹ * c ^ (p.2 : ℕ))
      (W_mul_right (W_inv_right (WA_Y hAB q)) (WA_Y hAB p)) ?_
    intro h
    rw [inv_mul_eq_one] at h
    exact hj (Fin.ext (pow_inj3 hc3 hc1 p.2.2 q.2.2 h.symm))

include hc3 hc1 in
lemma three_ne_zero' : (3 : K) ≠ 0 := by
  intro h3
  have h : ((c : K) - 1) ^ 3 = 0 := by
    have hc : (c : K) ^ 3 = 1 := by simpa using congrArg Units.val hc3
    linear_combination hc - (c : K) * ((c : K) - 1) * h3
  have : (c : K) = 1 :=
    sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (3:ℕ) ≠ 0)).mp h)
  exact hc1 (Units.ext this)

include hc3 hc1 hAB in
lemma linIndep_Yg : LinearIndependent K
    (fun p : Fin 3 × Fin 3 => ((Yg A B p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h1 := congrArg (fun N : Matrix (Fin 3) (Fin 3) K =>
    Matrix.trace ((((Yg A B q)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N)) hg
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    Matrix.mul_zero, Matrix.trace_zero] at h1
  rw [Finset.sum_eq_single q] at h1
  · have e : Matrix.trace ((((Yg A B q)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((Yg A B q : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 3 := by
      rw [← Units.val_mul, inv_mul_cancel]; simp
    rw [e, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (three_ne_zero' hc3 hc1)
  · intro p _ hp
    have := trace_Yg_inv_mul hc3 hc1 hAB hp
    rw [Units.val_mul] at this
    rw [this, smul_zero]
  · simp

include hc3 hc1 hAB in
lemma commutant_scalar {N : Matrix (Fin 3) (Fin 3) K}
    (hA : (A : Matrix (Fin 3) (Fin 3) K) * N = N * A)
    (hB : (B : Matrix (Fin 3) (Fin 3) K) * N = N * B) :
    ∃ x : K, N = x • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hli := linIndep_Yg hc3 hc1 hAB
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [Module.finrank_matrix])
  have hb : ∀ p, b p = ((Yg A B p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro p; simp [b]
  have hN : N = ∑ p, b.repr N p • ((Yg A B p : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    conv_lhs => rw [← b.sum_repr N]
    simp only [hb]
  have hxA := coeff_aux _ hli (fun p => b.repr N p) A (fun p => c ^ (p.2 : ℕ))
    (fun p => W_matrix (WA_Y hAB p)) (by rw [← hN]; exact hA)
  have hxB := coeff_aux _ hli (fun p => b.repr N p) B (fun p => (c⁻¹) ^ (p.1 : ℕ))
    (fun p => W_matrix (WB_Y hAB p)) (by rw [← hN]; exact hB)
  have hz : ∀ p, p ≠ (0, 0) → b.repr N p = 0 := by
    intro p hp
    by_cases h2 : (p.2 : ℕ) = 0
    · have h1 : (p.1 : ℕ) ≠ 0 := fun h1 => hp (Prod.ext (Fin.ext h1) (Fin.ext h2))
      have := hxB p
      simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] at this
      refine (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr ?_)
      intro h
      have h' : c ^ (p.1 : ℕ) = 1 := by
        apply Units.ext
        have := congrArg (fun x => x⁻¹) h
        simpa using this
      exact h1 (pow_inj3 hc3 hc1 p.1.2 (by norm_num) (h'.trans (pow_zero c).symm))
    · have := hxA p
      simp only [Units.val_pow_eq_pow_val] at this
      refine (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr ?_)
      intro h
      have h' : c ^ (p.2 : ℕ) = 1 := Units.ext (by simpa using h)
      exact h2 (pow_inj3 hc3 hc1 p.2.2 (by norm_num) (h'.trans (pow_zero c).symm))
  refine ⟨b.repr N (0, 0), ?_⟩
  conv_lhs => rw [hN]
  rw [Finset.sum_eq_single (0, 0)]
  · simp [Yg]
  · intro p _ hp; rw [hz p hp, zero_smul]
  · simp

include hc3 hc1 in
lemma cube_root {d : Kˣ} (hd : d ^ 3 = 1) : ∃ s : ℕ, d = c ^ s := by
  have hc : (c : K) ^ 3 = 1 := by simpa using congrArg Units.val hc3
  have hd' : (d : K) ^ 3 = 1 := by simpa using congrArg Units.val hd
  have hs : 1 + (c : K) + (c : K) ^ 2 = 0 := by
    have h : ((c : K) - 1) * (1 + (c : K) + (c : K) ^ 2) = 0 := by
      linear_combination hc
    refine (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr fun e => hc1 (Units.ext e))
  have h : ((d : K) - 1) * (((d : K) - c) * ((d : K) - (c : K) ^ 2)) = 0 := by
    linear_combination hd' + ((d : K) - (d : K) ^ 2) * hs + ((d : K) - 1) * hc
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨0, Units.ext (by simpa [sub_eq_zero] using h)⟩
  rcases mul_eq_zero.mp h with h | h
  · exact ⟨1, Units.ext (by simpa [sub_eq_zero] using h)⟩
  · exact ⟨2, Units.ext (by simpa [sub_eq_zero] using h)⟩

end Heis

end HeisAux

open HeisAux in
theorem heisenberg_normalizer {K : Type} [Field K] {c : Kˣ} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    {A B : GL (Fin 3) K}
    (hAB : A * B = B * A * Matrix.GeneralLinearGroup.scalar (Fin 3) c)
    {Y : GL (Fin 3) K} {dA dB : Kˣ} (hdA : dA ^ 3 = 1) (hdB : dB ^ 3 = 1)
    (hYA : Y * A * Y⁻¹ = A * Matrix.GeneralLinearGroup.scalar (Fin 3) dA)
    (hYB : Y * B * Y⁻¹ = B * Matrix.GeneralLinearGroup.scalar (Fin 3) dB) :
    ∃ (i j : ℕ) (m : Kˣ),
      Y = A ^ i * B ^ j * Matrix.GeneralLinearGroup.scalar (Fin 3) m := by
  obtain ⟨s, hs⟩ := cube_root hc3 hc1 hdA
  obtain ⟨t, ht⟩ := cube_root hc3 hc1 hdB
  have hYA' : W Y A dA := hYA
  have hYB' : W Y B dB := hYB
  set X : GL (Fin 3) K := A ^ t * B ^ (2 * s) with hX
  have hXA : W X A (1 ^ t * (c⁻¹) ^ (2 * s)) :=
    W_mul_left (W_pow_left (W_self A) t) (W_pow_left (WBA hAB) (2 * s))
  have hXB : W X B (c ^ t * 1 ^ (2 * s)) :=
    W_mul_left (W_pow_left (WAB hAB) t) (W_pow_left (W_self B) (2 * s))
  have e1 : (1 : Kˣ) ^ t * (c⁻¹) ^ (2 * s) = dA := by
    rw [hs, one_pow, one_mul, inv_pow, inv_eq_iff_eq_inv, ← mul_eq_one_iff_eq_inv,
      ← pow_add, show 2 * s + s = 3 * s by ring, pow_mul, hc3, one_pow]
  have e2 : c ^ t * (1 : Kˣ) ^ (2 * s) = dB := by rw [ht, one_pow, mul_one]
  rw [e1] at hXA
  rw [e2] at hXB
  have hMA : W (X⁻¹ * Y) A 1 := by
    have := W_mul_left (W_inv_left hXA) hYA'
    rwa [inv_mul_cancel] at this
  have hMB : W (X⁻¹ * Y) B 1 := by
    have := W_mul_left (W_inv_left hXB) hYB'
    rwa [inv_mul_cancel] at this
  have cA := W_matrix hMA
  have cB := W_matrix hMB
  simp only [Units.val_one, one_smul] at cA cB
  obtain ⟨x, hx⟩ := commutant_scalar hc3 hc1 hAB cA.symm cB.symm
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 := (X⁻¹ * Y).mul_inv
    rw [hx, h0, zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨t, 2 * s, Units.mk0 x hx0, ?_⟩
  have : X⁻¹ * Y = Matrix.GeneralLinearGroup.scalar (Fin 3) (Units.mk0 x hx0) := by
    apply Units.ext
    simp [hx, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  rw [← hX, ← this]; group

end CFSG.HardMathSupport.Timmesfeld.CrossChar
