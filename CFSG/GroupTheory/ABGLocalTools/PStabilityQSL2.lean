module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.FieldTheory.Finite.Basic

public section

open Matrix

namespace CFSG.ABGLocalTools.SL2Facts

variable {F : Type*} [Field F]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) F

theorem det_eq (A : SL2) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have := A.2
  rw [Matrix.det_fin_two] at this
  exact this

theorem sq_eq (A : SL2) :
    ((A ^ 2 : SL2) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) • (A : Matrix (Fin 2) (Fin 2) F) - 1 := by
  have hdet := det_eq A
  rw [Matrix.SpecialLinearGroup.coe_pow]
  rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination (-1 : F) * hdet

theorem mul_self_eq (A : SL2) :
    (A : Matrix (Fin 2) (Fin 2) F) * A =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) • (A : Matrix (Fin 2) (Fin 2) F) - 1 := by
  rw [← sq_eq, Matrix.SpecialLinearGroup.coe_pow, sq]

theorem pow_eq_one_of_root {A : SL2} {μ : F}
    (hμ : μ ^ 2 - Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) * μ + 1 = 0) {n : ℕ}
    (hn : A ^ n = 1) : μ ^ n = 1 := by
  have hdet := det_eq A
  set M : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) - μ • 1 with hM
  have hMdet : M.det = 0 := by
    rw [hM, Matrix.det_fin_two]
    simp [Matrix.trace_fin_two] at hμ ⊢
    linear_combination hμ + hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hMdet
  have hAv : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = μ • v := by
    have h := hv
    rw [hM, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hpow : ∀ k : ℕ, ((A ^ k : SL2) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hAv,
        Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
  have h := hpow n
  rw [hn, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h
  by_contra hne
  apply hv0
  have h2 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hne
  · exact h3

@[expose] def uT (t : F) : SL2 := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_uT (t : F) : ((uT t : SL2) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := rfl

theorem trace_comm_uT (A : SL2) (t : F) :
    Matrix.trace ((A * uT t * A⁻¹ * (uT t)⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) =
      2 + (A 1 0) ^ 2 * t ^ 2 := by
  have hdet := det_eq A
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv, coe_uT, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F)]
  simp [Matrix.trace_fin_two]
  linear_combination 2 * hdet

theorem trace_mul_add_trace_mul_inv (A B : SL2) :
    Matrix.trace ((A * B : SL2) : Matrix (Fin 2) (Fin 2) F) +
      Matrix.trace ((A * B⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) *
        Matrix.trace (B : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) F),
    Matrix.eta_fin_two (B : Matrix (Fin 2) (Fin 2) F)]
  simp [Matrix.trace_fin_two]
  ring

theorem trace_conj (A u : SL2) :
    Matrix.trace ((u * A * u⁻¹ : SL2) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, Matrix.SpecialLinearGroup.coe_inv,
    ← Matrix.SpecialLinearGroup.coe_inv, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem pow_two_mul_eq_one_of_comm_pow {A : SL2} (hγ : A 1 0 ≠ 0) {lam : F} (hlam : lam ≠ 0)
    {n : ℕ}
    (hn : (A * uT ((lam - lam⁻¹) / A 1 0) * A⁻¹ * (uT ((lam - lam⁻¹) / A 1 0))⁻¹) ^ n = 1) :
    lam ^ (2 * n) = 1 := by
  rw [pow_mul]
  refine pow_eq_one_of_root ?_ hn
  rw [trace_comm_uT]
  field_simp
  ring

theorem uT_mul_uT (s t : F) : uT s * uT t = uT (s + t) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uT, coe_uT, coe_uT]
  simp [add_comm]

theorem uT_pow (t : F) (n : ℕ) : uT t ^ n = uT (n * t) := by
  induction n with
  | zero =>
    apply Subtype.ext
    rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, coe_uT]
    simp [Matrix.one_fin_two]
  | succ n ih => rw [pow_succ, ih, uT_mul_uT]; push_cast; ring_nf

theorem pow_apply_of_lower_eq_zero {A : SL2} (h : A 1 0 = 0) (n : ℕ) :
    (A ^ n) 1 0 = 0 ∧ (A ^ n) 0 0 = A 0 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [ih.1, ih.2, h]
    constructor <;> ring

theorem charP_of_card_eq_prime_pow [Finite F] {r n : ℕ} (hr : r.Prime)
    (hcard : Nat.card F = r ^ n) : CharP F r := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, hs, m, hsp, hm⟩ := FiniteField.card' (K := F)
  rw [← Nat.card_eq_fintype_card, hcard] at hm
  have hsr : s = r := by
    have h1 : s ∣ r ^ n := by rw [hm]; exact dvd_pow_self s m.ne_zero
    exact (Nat.prime_dvd_prime_iff_eq hsp hr).mp (hsp.dvd_of_dvd_pow h1)
  rw [hsr] at hs
  exact hs

@[expose] def U {R : Type*} [CommRing R] : ℕ → R → R
  | 0, _ => 0
  | 1, _ => 1
  | (n + 2), τ => τ * U (n + 1) τ - U n τ

theorem U_zero {R : Type*} [CommRing R] (τ : R) : U 0 τ = 0 := rfl

theorem U_one {R : Type*} [CommRing R] (τ : R) : U 1 τ = 1 := rfl

theorem U_add_two {R : Type*} [CommRing R] (n : ℕ) (τ : R) :
    U (n + 2) τ = τ * U (n + 1) τ - U n τ := rfl

theorem U_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (τ : R) :
    f (U n τ) = U n (f τ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [U]
    | 1, _ => simp [U]
    | (n + 2), ih => simp [U, ih (n + 1) (by omega), ih n (by omega)]

theorem pow_succ_eq (A : SL2) (n : ℕ) :
    ((A ^ (n + 1) : SL2) : Matrix (Fin 2) (Fin 2) F) =
      U (n + 1) (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) • (A : Matrix (Fin 2) (Fin 2) F) -
        U n (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) • 1 := by
  set τ := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)
  induction n with
  | zero => simp [U]
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, sub_mul, smul_mul_assoc,
      smul_mul_assoc, Matrix.one_mul, mul_self_eq]
    simp only [U]
    rw [smul_sub, smul_smul, sub_smul, mul_comm (U (n + 1) τ) τ]
    abel

theorem pow_succ_eq_one_of_U {A : SL2} {n : ℕ}
    (h1 : U (n + 1) (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) = 0)
    (h2 : U n (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) = -1) : A ^ (n + 1) = 1 := by
  apply Subtype.ext
  rw [pow_succ_eq, h1, h2, zero_smul, zero_sub, neg_smul, neg_neg, one_smul,
    Matrix.SpecialLinearGroup.coe_one]

theorem U_of_pow_succ_eq_one {A : SL2} {n : ℕ} (hA : A ^ (n + 1) = 1)
    (h2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ 2)
    (hm2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ -2) :
    U (n + 1) (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) = 0 ∧
      U n (Matrix.trace (A : Matrix (Fin 2) (Fin 2) F)) = -1 := by
  have hdet := det_eq A
  have h := pow_succ_eq A n
  rw [hA, Matrix.SpecialLinearGroup.coe_one, eq_sub_iff_add_eq] at h
  set τ := Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) with hτ
  have h' : U (n + 1) τ • (A : Matrix (Fin 2) (Fin 2) F) =
      (1 + U n τ) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [add_smul, one_smul]
    exact h.symm
  by_cases hU : U (n + 1) τ = 0
  · refine ⟨hU, ?_⟩
    rw [hU, zero_smul] at h'
    have h00 := congrFun (congrFun h' 0) 0
    simp at h00
    linear_combination -h00
  · exfalso
    have hAc : (A : Matrix (Fin 2) (Fin 2) F) = ((U (n + 1) τ)⁻¹ * (1 + U n τ)) • 1 := by
      have := congrArg (fun M => (U (n + 1) τ)⁻¹ • M) h'
      simp only [smul_smul, inv_mul_cancel₀ hU, one_smul] at this
      exact this
    set c := (U (n + 1) τ)⁻¹ * (1 + U n τ)
    have h00 := congrFun (congrFun hAc 0) 0
    have h11 := congrFun (congrFun hAc 1) 1
    have h01 := congrFun (congrFun hAc 0) 1
    have h10 := congrFun (congrFun hAc 1) 0
    simp at h00 h11 h01 h10
    have hτc : τ = 2 * c := by
      rw [hτ, Matrix.trace_fin_two, h00, h11]
      ring
    have hc2 : c ^ 2 = 1 := by
      rw [h00, h11, h01, h10] at hdet
      linear_combination hdet
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp this with hc | hc
    · apply h2
      rw [hτc]
      linear_combination 2 * hc
    · apply hm2
      rw [hτc]
      linear_combination 2 * hc

theorem U_add_four_of_char_three {R : Type*} [CommRing R] (h3 : (3 : R) = 0) {τ : R}
    (hτ : τ ^ 2 = -1) (n : ℕ) : U (n + 4) τ = - U n τ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      simp only [U_add_two, U_one, U_zero, zero_add]
      linear_combination τ * hτ - τ * h3
    | 1, _ =>
      simp only [U_add_two, U_one, U_zero, zero_add]
      linear_combination (τ ^ 2 - 4) * hτ + 2 * h3
    | (n + 2), ih =>
      rw [show n + 2 + 4 = (n + 4) + 2 by ring, U_add_two, show n + 4 + 1 = (n + 1) + 4 by ring,
        ih (n + 1) (by omega), ih n (by omega), U_add_two]
      ring

theorem not_pow_of_trace_sq_eq_neg_one [CharP F 3] {A : SL2}
    (hτ : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ^ 2 = -1) :
    (A ^ 4 ≠ 1 ∧ A ^ 6 ≠ 1 ∧ A ^ 10 ≠ 1) ∧ A ^ 8 = 1 := by
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hτ0 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
    rintro h0
    rw [h0] at hτ
    have : (1 : F) = 0 := by linear_combination hτ
    exact one_ne_zero this
  have h2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ 2 := by
    rintro h
    rw [h] at hτ
    have h1 : (1 : F) = 0 := by linear_combination 2 * hτ - 3 * h3
    exact one_ne_zero h1
  have hm2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ -2 := by
    rintro h
    rw [h] at hτ
    have h1 : (1 : F) = 0 := by linear_combination 2 * hτ - 3 * h3
    exact one_ne_zero h1
  refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_⟩
  · obtain ⟨-, h3'⟩ := U_of_pow_succ_eq_one (n := 3) h h2 hm2
    simp only [U_add_two, U_one, U_zero, zero_add] at h3'
    have : (1 : F) = 0 := by linear_combination hτ - h3'
    exact one_ne_zero this
  · obtain ⟨h6, -⟩ := U_of_pow_succ_eq_one (n := 5) h h2 hm2
    rw [show 5 + 1 = 2 + 4 by ring, U_add_four_of_char_three h3 hτ] at h6
    simp only [U_add_two, U_one, U_zero, zero_add] at h6
    exact hτ0 (by linear_combination -h6)
  · obtain ⟨h10, -⟩ := U_of_pow_succ_eq_one (n := 9) h h2 hm2
    rw [show 9 + 1 = (2 + 4) + 4 by ring, U_add_four_of_char_three h3 hτ,
      U_add_four_of_char_three h3 hτ] at h10
    simp only [U_add_two, U_one, U_zero, zero_add, neg_neg] at h10
    exact hτ0 (by linear_combination h10)
  · refine pow_succ_eq_one_of_U (n := 7) ?_ ?_
    · rw [show 7 + 1 = (0 + 4) + 4 by ring, U_add_four_of_char_three h3 hτ,
        U_add_four_of_char_three h3 hτ, U_zero, neg_zero, neg_zero]
    · rw [show 7 = 3 + 4 by ring, U_add_four_of_char_three h3 hτ]
      simp only [U_add_two, U_one, U_zero, zero_add]
      linear_combination -hτ + h3

theorem U_castHom {p : ℕ} [CharP F p] (n : ℕ) (a : ZMod p) :
    U n (ZMod.castHom (dvd_refl p) F a) = ZMod.castHom (dvd_refl p) F (U n a) :=
  (U_map _ n a).symm

theorem U_four_five_ne : U 4 (5 : ZMod 11) ≠ 0 := by decide

theorem U_five_five_ne : U 5 (5 : ZMod 11) ≠ -1 := by decide

theorem U_ten_five_ne : U 10 (5 : ZMod 11) ≠ 0 := by decide

theorem U_twelve_five : U 12 (5 : ZMod 11) = 0 ∧ U 11 (5 : ZMod 11) = -1 := by decide

theorem not_pow_of_trace_eq_five [CharP F 11] {A : SL2}
    (hτ : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) = 5) :
    (A ^ 4 ≠ 1 ∧ A ^ 6 ≠ 1 ∧ A ^ 10 ≠ 1) ∧ A ^ 12 = 1 := by
  set φ := ZMod.castHom (dvd_refl 11) F
  have hinj : Function.Injective φ := ZMod.castHom_injective F
  have h5 : (5 : F) = φ 5 := (map_ofNat φ 5).symm
  have h2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ 2 := by
    rw [hτ, h5, show (2 : F) = φ 2 from (map_ofNat φ 2).symm, hinj.ne_iff]
    decide
  have hm2 : Matrix.trace (A : Matrix (Fin 2) (Fin 2) F) ≠ -2 := by
    rw [hτ, h5, show (-2 : F) = φ (-2) by rw [map_neg, map_ofNat], hinj.ne_iff]
    decide
  refine ⟨⟨fun h => ?_, fun h => ?_, fun h => ?_⟩, ?_⟩
  · obtain ⟨h4, -⟩ := U_of_pow_succ_eq_one (n := 3) h h2 hm2
    rw [hτ, h5, U_castHom, ← map_zero φ, hinj.eq_iff] at h4
    exact U_four_five_ne h4
  · obtain ⟨-, h5'⟩ := U_of_pow_succ_eq_one (n := 5) h h2 hm2
    rw [hτ, h5, U_castHom, show (-1 : F) = φ (-1) by rw [map_neg, map_one], hinj.eq_iff] at h5'
    exact U_five_five_ne h5'
  · obtain ⟨h10, -⟩ := U_of_pow_succ_eq_one (n := 9) h h2 hm2
    rw [hτ, h5, U_castHom, ← map_zero φ, hinj.eq_iff] at h10
    exact U_ten_five_ne h10
  · refine pow_succ_eq_one_of_U (n := 11) ?_ ?_
    · rw [hτ, h5, U_castHom, U_twelve_five.1, map_zero]
    · rw [hτ, h5, U_castHom, U_twelve_five.2, map_neg, map_one]

theorem U_exponent_three : ∀ τ : ZMod 3, (U 4 τ = 0 ∧ U 3 τ = -1) ∨ (U 6 τ = 0 ∧ U 5 τ = -1) ∨
    (U 10 τ = 0 ∧ U 9 τ = -1) := by decide

theorem U_exponent_five : ∀ τ : ZMod 5, (U 4 τ = 0 ∧ U 3 τ = -1) ∨ (U 6 τ = 0 ∧ U 5 τ = -1) ∨
    (U 10 τ = 0 ∧ U 9 τ = -1) := by decide

theorem pow_four_or_six_or_ten_of_prime_card {p : ℕ} [CharP F p] [Finite F]
    (hp : Nat.card F = p)
    (hU : ∀ τ : ZMod p, (U 4 τ = 0 ∧ U 3 τ = -1) ∨ (U 6 τ = 0 ∧ U 5 τ = -1) ∨
      (U 10 τ = 0 ∧ U 9 τ = -1)) (g : SL2) :
    g ^ 4 = 1 ∨ g ^ 6 = 1 ∨ g ^ 10 = 1 := by
  set φ := ZMod.castHom (dvd_refl p) F
  have hinj : Function.Injective φ := ZMod.castHom_injective F
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := F)
    omega
  have : NeZero p := ⟨hp0⟩
  have hsurj : Function.Surjective φ := by
    have : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card (ZMod p) = Fintype.card F := by
      rw [ZMod.card, ← Nat.card_eq_fintype_card, hp]
    exact (Fintype.bijective_iff_injective_and_card φ).mpr ⟨hinj, hcard⟩ |>.2
  obtain ⟨a, ha⟩ := hsurj (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F))
  have key : ∀ n : ℕ, U n a = 0 → U n (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)) = 0 := by
    intro n h; rw [← ha, U_castHom, h, map_zero]
  have key' : ∀ n : ℕ, U n a = -1 →
      U n (Matrix.trace (g : Matrix (Fin 2) (Fin 2) F)) = -1 := by
    intro n h; rw [← ha, U_castHom, h, map_neg, map_one]
  rcases hU a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (pow_succ_eq_one_of_U (n := 3) (key 4 h1) (key' 3 h2))
  · exact Or.inr (Or.inl (pow_succ_eq_one_of_U (n := 5) (key 6 h1) (key' 5 h2)))
  · exact Or.inr (Or.inr (pow_succ_eq_one_of_U (n := 9) (key 10 h1) (key' 9 h2)))

end CFSG.ABGLocalTools.SL2Facts
