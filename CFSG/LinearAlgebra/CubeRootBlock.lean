module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LinearAlgebra

open Matrix
open scoped MatrixGroups

variable {K : Type*} [Field K]

@[expose] def cubeRootBlock (K : Type*) [Field K] : SL(2, K) :=
  ⟨!![0, 1; -1, -1], by simp [Matrix.det_fin_two]⟩

@[expose] def cubeRootDiag (ω : Kˣ) : SL(2, K) :=
  ⟨!![(ω : K), 0; 0, ((ω⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

open scoped Classical in
@[expose] noncomputable def cubeRootBlockStd (K : Type*) [Field K] : SL(2, K) :=
  if h : ∃ ω : Kˣ, (ω : K) ^ 2 + ω + 1 = 0 then cubeRootDiag h.choose else cubeRootBlock K

structure IsCubeRootBlock (s : SL(2, K)) : Prop where
  three_ne_zero : (3 : K) ≠ 0
  sq_add_self_add_one :
    (s : Matrix (Fin 2) (Fin 2) K) ^ 2 + (s : Matrix (Fin 2) (Fin 2) K) + 1 = 0
  exists_inverter : ∃ t : SL(2, K), t * s = s ^ 2 * t
  exists_cyclicVector : ∃ v : Fin 2 → K,
    v 0 * ((s : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 1 ≠ v 1 * ((s : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0

@[expose] def cubePowHom {G : Type*} [Group G] (g : G) (hg : g ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun x := g ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

theorem exists_sq_sub_mul_add_sq_eq_neg_one [Finite K] (h3 : (3 : K) ≠ 0) :
    ∃ a b : K, a ^ 2 - a * b + b ^ 2 = -1 := by
  haveI := Fintype.ofFinite K
  by_cases h2 : (2 : K) = 0
  · exact ⟨1, 0, by linear_combination h2⟩
  · have hchar : ringChar K ≠ 2 := by
      intro h
      apply h2
      have := (ringChar.spec K 2).mpr (by rw [h])
      exact_mod_cast this
    have hR := FiniteField.odd_card_of_char_ne_two hchar
    have h4 : (4 : K) ≠ 0 := by
      have : (4 : K) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have h34 : (3 / 4 : K) ≠ 0 := div_ne_zero h3 h4
    have hf : (Polynomial.X ^ 2 : Polynomial K).degree = 2 := Polynomial.degree_X_pow 2
    have hg : (Polynomial.C (3 / 4 : K) * Polynomial.X ^ 2 + Polynomial.C 1 : Polynomial K).degree
        = 2 := by
      rw [Polynomial.degree_add_C, Polynomial.degree_C_mul_X_pow 2 h34]
      · norm_num
      · rw [Polynomial.degree_C_mul_X_pow 2 h34]
        norm_num
    obtain ⟨a', b', hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hR
    simp at hab
    refine ⟨a' + b' / 2, b', ?_⟩
    field_simp at hab ⊢
    linear_combination hab

theorem isCubeRootBlock_cubeRootBlock [Finite K] (h3 : (3 : K) ≠ 0) :
    IsCubeRootBlock (cubeRootBlock K) := by
  obtain ⟨a, b, hab⟩ := exists_sq_sub_mul_add_sq_eq_neg_one h3
  obtain ⟨t, ht⟩ : ∃ t : SL(2, K), (t : Matrix (Fin 2) (Fin 2) K) = !![a, b; b - a, -a] :=
    ⟨⟨!![a, b; b - a, -a], by rw [Matrix.det_fin_two_of]; linear_combination -hab⟩, rfl⟩
  refine ⟨h3, ?_, ⟨t, ?_⟩, ⟨![1, 0], ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeRootBlock, sq, Matrix.mul_apply, Fin.sum_univ_two]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, ht]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeRootBlock, sq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [cubeRootBlock, Matrix.mulVec, dotProduct]

theorem isCubeRootBlock_cubeRootDiag (h3 : (3 : K) ≠ 0) {ω : Kˣ}
    (hω : (ω : K) ^ 2 + ω + 1 = 0) : IsCubeRootBlock (cubeRootDiag ω) := by
  have hω3 : (ω : K) ^ 3 = 1 := by linear_combination ((ω : K) - 1) * hω
  have hωne : (ω : K) ≠ 0 := ω.ne_zero
  have hinv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    have : (ω : K) * (ω : K) ^ 2 = 1 := by linear_combination hω3
    rw [Units.val_inv_eq_inv_val]
    exact inv_eq_of_mul_eq_one_right this
  have hne : (ω : K) ≠ (ω : K) ^ 2 := by
    intro h
    have h1 : (ω : K) = 1 := by
      have : (ω : K) * ((ω : K) - 1) = 0 := by linear_combination -h
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hωne)
    apply h3
    rw [h1] at hω
    linear_combination hω
  obtain ⟨w, hw⟩ : ∃ w : SL(2, K), (w : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
    ⟨⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩, rfl⟩
  refine ⟨h3, ?_, ⟨w, ?_⟩, ⟨![1, 1], ?_⟩⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeRootDiag, sq, Matrix.mul_apply, Fin.sum_univ_two, hinv]
    · linear_combination hω
    · linear_combination hω + (ω : K) * hω3
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, hw]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cubeRootDiag, sq, Matrix.mul_apply, Fin.sum_univ_two, hinv]
    linear_combination (-(ω : K)) * hω3
  · simp [cubeRootDiag, Matrix.mulVec, dotProduct, hinv]
    exact fun h => hne h.symm

theorem exists_unit_sq_add_self_add_one_iff [Finite K] (h3 : (3 : K) ≠ 0) :
    (∃ ω : Kˣ, (ω : K) ^ 2 + ω + 1 = 0) ↔ Nat.card K % 3 = 1 := by
  haveI := Nat.fact_prime_three
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  constructor
  · rintro ⟨ω, hω⟩
    have hω3 : (ω : K) ^ 3 = 1 := by linear_combination ((ω : K) - 1) * hω
    have hω1 : ω ^ 3 = 1 := Units.ext (by simpa using hω3)
    have hne : ω ≠ 1 := by
      intro h1
      apply h3
      rw [h1] at hω
      simp at hω
      linear_combination hω
    have hord : orderOf ω = 3 := orderOf_eq_prime hω1 hne
    have hdvd : 3 ∣ Nat.card Kˣ := hord ▸ orderOf_dvd_natCard ω
    rw [Nat.card_units] at hdvd
    omega
  · intro h
    have hdvd : 3 ∣ Nat.card Kˣ := by
      rw [Nat.card_units]
      omega
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hω1 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
    have hne : ω ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hω
      omega
    refine ⟨ω, ?_⟩
    have hω3 : (ω : K) ^ 3 = 1 := by simpa using congrArg (fun u : Kˣ => (u : K)) hω1
    have hne' : (ω : K) - 1 ≠ 0 := by
      intro h0
      apply hne
      exact Units.ext (by simpa using sub_eq_zero.mp h0)
    have : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.mp this).resolve_left hne'

theorem isCubeRootBlock_cubeRootBlockStd [Finite K] (h3 : (3 : K) ≠ 0) :
    IsCubeRootBlock (cubeRootBlockStd K) := by
  unfold cubeRootBlockStd
  split_ifs with h
  · exact isCubeRootBlock_cubeRootDiag h3 h.choose_spec
  · exact isCubeRootBlock_cubeRootBlock h3

theorem cubeRootBlockStd_eq_cubeRootDiag [Finite K] (h3 : (3 : K) ≠ 0)
    (hq : Nat.card K % 3 = 1) :
    ∃ ω : Kˣ, (ω : K) ^ 2 + ω + 1 = 0 ∧ cubeRootBlockStd K = cubeRootDiag ω := by
  have h : ∃ ω : Kˣ, (ω : K) ^ 2 + ω + 1 = 0 :=
    (exists_unit_sq_add_self_add_one_iff h3).mpr hq
  refine ⟨h.choose, h.choose_spec, ?_⟩
  unfold cubeRootBlockStd
  rw [dif_pos h]

theorem cubeRootBlockStd_eq_cubeRootBlock [Finite K] (h3 : (3 : K) ≠ 0)
    (hq : ¬ Nat.card K % 3 = 1) : cubeRootBlockStd K = cubeRootBlock K := by
  have h : ¬ ∃ ω : Kˣ, (ω : K) ^ 2 + ω + 1 = 0 := fun h =>
    hq ((exists_unit_sq_add_self_add_one_iff h3).mp h)
  unfold cubeRootBlockStd
  rw [dif_neg h]

theorem exists_proportional_of_minors {p q r t a b c d v0 v1 : K}
    (E00 : q * c = b * r) (E01 : b * (p - t) = (a - d) * q) (E10 : c * (p - t) = (a - d) * r)
    (hD : v0 * (c * v0 + d * v1) - v1 * (a * v0 + b * v1) ≠ 0) :
    ∃ y : K, q = y * b ∧ r = y * c ∧ p - t = y * (a - d) := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · have had : a - d ≠ 0 := by
        intro h
        apply hD
        subst hb hc
        linear_combination (-(v0 * v1)) * h
      refine ⟨(p - t) / (a - d), ?_, ?_, ?_⟩
      · subst hb
        have : (a - d) * q = 0 := by linear_combination -E01
        have hq : q = 0 := (mul_eq_zero.mp this).resolve_left had
        simp [hq]
      · subst hc
        have : (a - d) * r = 0 := by linear_combination -E10
        have hr : r = 0 := (mul_eq_zero.mp this).resolve_left had
        simp [hr]
      · field_simp
    · refine ⟨r / c, ?_, ?_, ?_⟩
      · subst hb
        have : q * c = 0 := by linear_combination E00
        have hq : q = 0 := (mul_eq_zero.mp this).resolve_right hc
        simp [hq]
      · field_simp
      · field_simp
        linear_combination E10
  · refine ⟨q / b, ?_, ?_, ?_⟩
    · field_simp
    · field_simp
      linear_combination -E00
    · field_simp
      linear_combination E01

namespace IsCubeRootBlock

variable {s : SL(2, K)}

theorem pow_three (hs : IsCubeRootBlock s) : s ^ 3 = 1 := by
  apply Subtype.ext
  have h := hs.sq_add_self_add_one
  have e : (s : Matrix (Fin 2) (Fin 2) K) ^ 3 =
      1 + ((s : Matrix (Fin 2) (Fin 2) K) - 1) *
        ((s : Matrix (Fin 2) (Fin 2) K) ^ 2 + (s : Matrix (Fin 2) (Fin 2) K) + 1) := by
    noncomm_ring
  rw [h, mul_zero, add_zero] at e
  rw [Matrix.SpecialLinearGroup.coe_pow, e]
  rfl

theorem ne_one (hs : IsCubeRootBlock s) : s ≠ 1 := by
  intro h1
  have h := hs.sq_add_self_add_one
  rw [h1] at h
  have h00 := congrFun (congrFun h 0) 0
  have h3 : (1 : K) + 1 + 1 = 0 := by simpa using h00
  apply hs.three_ne_zero
  calc (3 : K) = 1 + 1 + 1 := by norm_num
    _ = 0 := h3

theorem orderOf_eq_three (hs : IsCubeRootBlock s) : orderOf s = 3 := by
  haveI := Nat.fact_prime_three
  exact orderOf_eq_prime hs.pow_three hs.ne_one

theorem pow_val_eq_one_iff (hs : IsCubeRootBlock s) (x : ZMod 3) : s ^ x.val = 1 ↔ x = 0 := by
  rw [← orderOf_dvd_iff_pow_eq_one, hs.orderOf_eq_three]
  constructor
  · intro h
    have : x.val = 0 := Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt x)
    exact (ZMod.val_eq_zero x).mp this
  · rintro rfl
    simp

theorem trace_eq (hs : IsCubeRootBlock s) :
    Matrix.trace (s : Matrix (Fin 2) (Fin 2) K) = -1 := by
  have hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1 := s.2
  have ch : (s : Matrix (Fin 2) (Fin 2) K) ^ 2 =
      Matrix.trace (s : Matrix (Fin 2) (Fin 2) K) • (s : Matrix (Fin 2) (Fin 2) K) - 1 := by
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
      first | ring1 | linear_combination hd | linear_combination (-1 : K) * hd
  have h := hs.sq_add_self_add_one
  rw [ch] at h
  have h2 : (Matrix.trace (s : Matrix (Fin 2) (Fin 2) K) + 1) •
      (s : Matrix (Fin 2) (Fin 2) K) = 0 := by
    rw [← h]
    module
  rcases smul_eq_zero.mp h2 with h3 | h3
  · linear_combination h3
  · exfalso
    have h0 : (s : Matrix (Fin 2) (Fin 2) K).det = 0 := by rw [h3]; simp
    rw [hdet] at h0
    exact one_ne_zero h0

theorem two_smul_add_one_sq (hs : IsCubeRootBlock s) :
    ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) ^ 2 =
      (-3 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have h := hs.sq_add_self_add_one
  have e : ((2 : K) • (s : Matrix (Fin 2) (Fin 2) K) + 1) ^ 2 =
      (4 : K) • ((s : Matrix (Fin 2) (Fin 2) K) ^ 2 + (s : Matrix (Fin 2) (Fin 2) K) + 1) -
        (3 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
    simp only [sq, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
      Matrix.mul_one]
    module
  rw [e, h]
  module

theorem eq_zero_of_mulVec_pow_eq (hs : IsCubeRootBlock s) {k : ℕ} (hk : ¬ 3 ∣ k)
    {w : Fin 2 → K} (hw : ((s ^ k : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ w = w) : w = 0 := by
  have hsw : (s : Matrix (Fin 2) (Fin 2) K) *ᵥ w = w := by
    have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rw [pow_eq_pow_mod k hs.pow_three] at hw
    rcases hmod with h | h
    · rw [h, pow_one] at hw
      exact hw
    · rw [h] at hw
      have h2 : (s : Matrix (Fin 2) (Fin 2) K) *ᵥ
          (((s ^ 2 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) *ᵥ w) =
            (s : Matrix (Fin 2) (Fin 2) K) *ᵥ w := by rw [hw]
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, ← pow_succ',
        hs.pow_three] at h2
      simpa using h2.symm
  have h := hs.sq_add_self_add_one
  have h3 : (3 : K) • w = 0 := by
    have h0 : ((s : Matrix (Fin 2) (Fin 2) K) ^ 2 + (s : Matrix (Fin 2) (Fin 2) K) + 1) *ᵥ w =
        0 := by
      rw [h]
      simp
    rw [Matrix.add_mulVec, Matrix.add_mulVec, sq, ← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h0
    simp only [hsw] at h0
    calc (3 : K) • w = w + w + w := by module
      _ = 0 := h0
  exact (smul_eq_zero.mp h3).resolve_left hs.three_ne_zero

theorem eq_zero_of_mul_right_eq (hs : IsCubeRootBlock s) {N : Matrix (Fin 2) (Fin 2) K}
    (hN : N * (s : Matrix (Fin 2) (Fin 2) K) = N) : N = 0 := by
  have h := congrArg (fun A => N * A) hs.sq_add_self_add_one
  simp only [mul_add, Matrix.mul_zero, ← mul_assoc, sq, hN, Matrix.mul_one] at h
  have h3 : (3 : K) • N = 0 := by
    rw [← h]
    module
  exact (smul_eq_zero.mp h3).resolve_left hs.three_ne_zero

theorem eq_zero_of_mul_left_eq (hs : IsCubeRootBlock s) {N : Matrix (Fin 2) (Fin 2) K}
    (hN : (s : Matrix (Fin 2) (Fin 2) K) * N = N) : N = 0 := by
  have h := congrArg (fun A => A * N) hs.sq_add_self_add_one
  simp only [add_mul, Matrix.zero_mul, mul_assoc, sq, hN, Matrix.one_mul] at h
  have h3 : (3 : K) • N = 0 := by
    rw [← h]
    module
  exact (smul_eq_zero.mp h3).resolve_left hs.three_ne_zero

theorem commute_iff (hs : IsCubeRootBlock s) {z : Matrix (Fin 2) (Fin 2) K} :
    Commute z (s : Matrix (Fin 2) (Fin 2) K) ↔
      ∃ x y : K, z = x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (s : Matrix (Fin 2) (Fin 2) K) := by
  constructor
  · intro hz
    obtain ⟨v, hv⟩ := hs.exists_cyclicVector
    have E00 := congrFun (congrFun hz.eq 0) 0
    have E01 := congrFun (congrFun hz.eq 0) 1
    have E10 := congrFun (congrFun hz.eq 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at E00 E01 E10
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hv
    obtain ⟨y, h01, h10, hdiag⟩ := exists_proportional_of_minors (p := z 0 0) (q := z 0 1)
      (r := z 1 0) (t := z 1 1) (a := (s : Matrix (Fin 2) (Fin 2) K) 0 0)
      (b := (s : Matrix (Fin 2) (Fin 2) K) 0 1) (c := (s : Matrix (Fin 2) (Fin 2) K) 1 0)
      (d := (s : Matrix (Fin 2) (Fin 2) K) 1 1) (v0 := v 0) (v1 := v 1)
      (by linear_combination E00) (by linear_combination E01) (by linear_combination -E10)
      (sub_ne_zero.mpr hv)
    refine ⟨z 0 0 - y * (s : Matrix (Fin 2) (Fin 2) K) 0 0, y, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;>
      first | linear_combination h01 | linear_combination h10 |
        linear_combination (-1 : K) * hdiag
  · rintro ⟨x, y, rfl⟩
    exact ((Commute.one_left _).smul_left x).add_left ((Commute.refl _).smul_left y)

theorem det_smul_one_add_smul (hs : IsCubeRootBlock s) (x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (s : Matrix (Fin 2) (Fin 2) K)).det =
      x ^ 2 - x * y + y ^ 2 := by
  have htr := hs.trace_eq
  rw [Matrix.trace_fin_two] at htr
  have hd : (s : Matrix (Fin 2) (Fin 2) K).det = 1 := s.2
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.det_fin_two]
  simp
  linear_combination (y ^ 2) * hd + (x * y) * htr

theorem not_three_dvd_card [Finite K] (hs : IsCubeRootBlock s) : ¬ 3 ∣ Nat.card K := by
  intro h
  haveI := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  rw [Nat.card_eq_fintype_card, hcard] at h
  have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  have hp3 : p = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p).symm
  apply hs.three_ne_zero
  have h0 := CharP.cast_eq_zero K p
  rw [hp3] at h0
  exact_mod_cast h0

theorem smul_one_add_smul_pow_card [Finite K] (hs : IsCubeRootBlock s) (x y : K) :
    (x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (s : Matrix (Fin 2) (Fin 2) K)) ^ Nat.card K =
      x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (s : Matrix (Fin 2) (Fin 2) K) ^ Nat.card K := by
  haveI := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  haveI := Fact.mk hp
  have hx : x ^ Fintype.card K = x := FiniteField.pow_card x
  have hy : y ^ Fintype.card K = y := FiniteField.pow_card y
  rw [Nat.card_eq_fintype_card]
  have hc : Commute (x • (1 : Matrix (Fin 2) (Fin 2) K)) (y • (s : Matrix (Fin 2) (Fin 2) K)) :=
    ((Commute.one_left _).smul_left x).smul_right y
  rw [hcard] at hx hy ⊢
  rw [add_pow_char_pow_of_commute (R := Matrix (Fin 2) (Fin 2) K) p (n : ℕ) hc, smul_pow,
    smul_pow, hx, hy, one_pow]

theorem pow_pi_eq_one [Finite K] (hs : IsCubeRootBlock s) {z : SL(2, K)}
    (hz : Commute (z : Matrix (Fin 2) (Fin 2) K) (s : Matrix (Fin 2) (Fin 2) K)) :
    z ^ (if Nat.card K % 3 = 1 then Nat.card K - 1 else Nat.card K + 1) = 1 := by
  obtain ⟨x, y, hxy⟩ := hs.commute_iff.mp hz
  have hq := hs.smul_one_add_smul_pow_card x y
  rw [← hxy] at hq
  have hz_det : (z : Matrix (Fin 2) (Fin 2) K).det = 1 := z.2
  rw [hxy, hs.det_smul_one_add_smul] at hz_det
  have h3q := hs.not_three_dvd_card
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hs3 : s ^ 3 = 1 := hs.pow_three
  have hspow : (s : Matrix (Fin 2) (Fin 2) K) ^ Nat.card K =
      ((s ^ (Nat.card K % 3) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, pow_eq_pow_mod _ hs3]
  by_cases h : Nat.card K % 3 = 1
  · rw [if_pos h]
    rw [h, pow_one] at hspow
    rw [hspow, ← hxy] at hq
    have hzq : z ^ Nat.card K = z := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow]
      exact hq
    have : z ^ (Nat.card K - 1) * z = 1 * z := by
      rw [← pow_succ, Nat.sub_add_cancel hq1, one_mul, hzq]
    exact mul_right_cancel this
  · rw [if_neg h]
    have h2 : Nat.card K % 3 = 2 := by omega
    rw [h2] at hspow
    rw [hspow] at hq
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_succ, hq, hxy]
    have hsq := hs.sq_add_self_add_one
    have hs3' : (s : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
      have := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K)) hs3
      simpa [Matrix.SpecialLinearGroup.coe_pow] using this
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    have hS2 : (s : Matrix (Fin 2) (Fin 2) K) ^ 2 = -(s : Matrix (Fin 2) (Fin 2) K) - 1 := by
      calc (s : Matrix (Fin 2) (Fin 2) K) ^ 2 =
          ((s : Matrix (Fin 2) (Fin 2) K) ^ 2 + (s : Matrix (Fin 2) (Fin 2) K) + 1) -
            (s : Matrix (Fin 2) (Fin 2) K) - 1 := by abel
        _ = -(s : Matrix (Fin 2) (Fin 2) K) - 1 := by rw [hsq]; abel
    have hS3 : (s : Matrix (Fin 2) (Fin 2) K) ^ 2 * (s : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [← pow_succ]
      exact hs3'
    have hx2 : (x * x - x * y + y * y) • (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
      have : x * x - x * y + y * y = 1 := by linear_combination hz_det
      rw [this, one_smul]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
      Matrix.mul_one, hS3]
    rw [hS2]
    refine Eq.trans ?_ hx2
    module

end IsCubeRootBlock

end CFSG.LinearAlgebra
