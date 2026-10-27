module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi.LinA

open Matrix Polynomial

section Basic

variable {K : Type} [Field K]

theorem sq_eq_trace_det (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two] <;> ring

theorem fixed_eq_zero [CharP K 2] {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (hne : M ≠ 1) {m : ℕ} (hm : Odd m) (hMm : M ^ m = 1) {v : Fin 2 → K} (hv : M *ᵥ v = v) :
    v = 0 := by
  by_contra hv0
  have h1 : (M - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]
  have h2 : (M - 1).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, h1⟩
  have h3 : (M - 1).det = M.det - M.trace + 1 := by
    simp [Matrix.det_fin_two, Matrix.trace, Fin.sum_univ_two]
    ring
  have h11 : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
  have htr : M.trace = 0 := by
    have : M.trace = M.det + 1 - (M - 1).det := by rw [h3]; ring
    rw [this, h2, hdet, sub_zero, h11]
  have hsq : M * M = 1 := by
    rw [sq_eq_trace_det, htr, hdet, zero_smul, zero_sub, one_smul, CharTwo.neg_eq]
  obtain ⟨k, rfl⟩ := hm
  apply hne
  have : M ^ (2 * k + 1) = M := by
    rw [pow_succ, pow_mul, sq, hsq, one_pow, one_mul]
  rw [← this, hMm]

theorem exists_eq_of_commute_nonscalar (A M : Matrix (Fin 2) (Fin 2) K)
    (hA : ∀ c : K, A ≠ c • 1) (hM : A * M = M * A) :
    ∃ x y : K, M = x • 1 + y • A := by
  have e11 := congrFun (congrFun hM 0) 0
  have e12 := congrFun (congrFun hM 0) 1
  have e21 := congrFun (congrFun hM 1) 0
  have e22 := congrFun (congrFun hM 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e11 e12 e21 e22
  have hext : ∀ x y : K, M 0 0 = x + y * A 0 0 → M 0 1 = y * A 0 1 → M 1 0 = y * A 1 0 →
      M 1 1 = x + y * A 1 1 → M = x • 1 + y • A := by
    intro x y h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · have hne : A 0 0 ≠ A 1 1 := by
        intro h
        apply hA (A 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc, h]
      have hd : A 0 0 - A 1 1 ≠ 0 := sub_ne_zero.2 hne
      have hm12 : M 0 1 = 0 := by
        have : M 0 1 * (A 0 0 - A 1 1) = 0 := by
          linear_combination e12 - (M 1 1 - M 0 0) * hb
        exact (mul_eq_zero.1 this).resolve_right hd
      have hm21 : M 1 0 = 0 := by
        have : M 1 0 * (A 0 0 - A 1 1) = 0 := by
          linear_combination -e21 + (M 0 0 - M 1 1) * hc
        exact (mul_eq_zero.1 this).resolve_right hd
      refine ⟨M 0 0 - (M 0 0 - M 1 1) / (A 0 0 - A 1 1) * A 0 0,
        (M 0 0 - M 1 1) / (A 0 0 - A 1 1), hext _ _ (by ring) (by rw [hm12, hb]; ring)
        (by rw [hm21, hc]; ring) ?_⟩
      field_simp
      ring
    · have hm12 : M 0 1 = 0 := by
        have : M 0 1 * A 1 0 = 0 := by linear_combination -e11 + M 1 0 * hb
        exact (mul_eq_zero.1 this).resolve_right hc
      refine ⟨M 0 0 - M 1 0 / A 1 0 * A 0 0, M 1 0 / A 1 0,
        hext _ _ (by ring) (by rw [hm12, hb]; ring) (by field_simp) ?_⟩
      field_simp
      linear_combination -e21
  · refine ⟨M 0 0 - M 0 1 / A 0 1 * A 0 0, M 0 1 / A 0 1, hext _ _ (by ring) (by field_simp)
      ?_ ?_⟩
    · field_simp
      linear_combination e11
    · field_simp
      linear_combination e12

theorem commute_of_commute_nonscalar (A M N : Matrix (Fin 2) (Fin 2) K)
    (hA : ∀ c : K, A ≠ c • 1) (hM : A * M = M * A) (hN : A * N = N * A) : M * N = N * M := by
  obtain ⟨x, y, rfl⟩ := exists_eq_of_commute_nonscalar A M hA hM
  obtain ⟨x', y', rfl⟩ := exists_eq_of_commute_nonscalar A N hA hN
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply] <;> ring

end Basic

section Field

variable {K : Type} [Field K] [Finite K]

theorem natCard_eq_pow_three_of_order_three (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) :
    ∃ F : Subfield K, (∀ x : K, x ∈ F ↔ σ x = x) ∧ Nat.card K = Nat.card F ^ 3 := by
  classical
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  set G : Subgroup (K ≃+* K) := Subgroup.zpowers σ with hG
  have : Fintype K := Fintype.ofFinite K
  have hcardG : Nat.card G = 3 := by rw [hG, Nat.card_zpowers, hord]
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcardG]; norm_num)
  haveI : Fintype G := Fintype.ofFinite G
  refine ⟨FixedPoints.subfield G K, fun x => ?_, ?_⟩
  · change x ∈ MulAction.fixedPoints G K ↔ _
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro h g
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x :=
        Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff]; exact h)
      have := hle g.2
      rwa [MulAction.mem_stabilizer_iff] at this
  · have hfr := FixedPoints.finrank_eq_card G K
    have h1 : Module.finrank (FixedPoints.subfield G K) K = 3 := by
      rw [hfr, ← Nat.card_eq_fintype_card, hcardG]
    have h2 := Module.natCard_eq_pow_finrank (K := FixedPoints.subfield G K) (V := K)
    rw [h1] at h2
    exact h2





theorem pow_card_sq_eq_self [CharP K 2] (F : Subfield K) [Finite F] {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hτF : M.trace ∈ F) (ht0 : M.trace ≠ 0) :
    M ^ (Nat.card F) ^ 2 = M := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
  let τ' : F := ⟨M.trace, hτF⟩
  have hτ'0 : τ' ≠ 0 := fun h => ht0 (congrArg Subtype.val h)
  have h2F : (1 : F) + 1 = 0 := Subtype.ext (by simpa using h11)
  let p : F[X] := C (1 : F) * X ^ 2 + C τ' * X + C 1
  have hpm : p.Monic := by
    simp only [p, map_one, one_mul]
    monicity!
  have hpdeg : p.natDegree = 2 := by
    simp only [p]
    exact natDegree_quadratic one_ne_zero
  have hpK : p.map (algebraMap F K) = C (1 : K) * X ^ 2 + C M.trace * X + C 1 := by
    simp [p, τ']
    rfl
  have hpM : aeval M (p.map (algebraMap F K)) = 0 := by
    rw [hpK]
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, map_one]
    have h1 := sq_eq_trace_det M
    rw [hdet] at h1
    have h2 : M.trace • M + M.trace • M = 0 := by
      rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, one_smul, sq]
    rw [h1]
    calc M.trace • M - (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) + M.trace • M + 1
        = M.trace • M + M.trace • M := by rw [one_smul]; abel
      _ = 0 := h2
  have hdvd : p ∣ (X ^ (Nat.card F) ^ 2 - X : F[X]) := by
    by_cases hirr : Irreducible p
    · exact (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X (n := 2)).1
        (by rw [hpdeg])
    · have hroots : p.roots ≠ 0 := fun h0 => hirr
        ((hpm.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [hpdeg])
          (by rw [hpdeg]; norm_num)).2 h0)
      obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
      have hpr : p.eval r = 0 := (mem_roots hpm.ne_zero |>.1 hr)
      simp only [p, eval_add, eval_mul, eval_C, eval_pow, eval_X] at hpr
      have hr1 : r ^ 2 + τ' * r + 1 = 0 := by simpa using hpr
      set s : F := τ' + r with hs
      have hsr : s - r = τ' := by rw [hs]; ring
      have hrs1 : r + s = τ' := by
        rw [hs]
        have : r + r = 0 := CharTwo.add_self_eq_zero r
        calc r + (τ' + r) = τ' + (r + r) := by ring
          _ = τ' := by rw [this, add_zero]
      have hrs2 : r * s = 1 := by
        rw [hs]
        have : r ^ 2 + τ' * r = 1 := by
          have : (1 : F) + 1 = 0 := h2F
          linear_combination hr1 - this
        linear_combination this
      have hfac : p = (X - C r) * (X - C s) := by
        have : (X - C r) * (X - C s) = X ^ 2 - C (r + s) * X + C (r * s) := by
          simp only [C_add, C_mul]; ring
        rw [this, hrs1, hrs2, CharTwo.sub_eq_add]
        simp only [p, map_one, one_mul]
      have hcop : IsCoprime (X - C r) (X - C s) :=
        Polynomial.isCoprime_X_sub_C_of_isUnit_sub (by
          have : r - s ≠ 0 := by
            intro h
            apply hτ'0
            rw [← hsr, ← neg_sub, h, neg_zero]
          exact (Ne.isUnit this))
      have hrN : ∀ x : F, x ^ (Nat.card F) ^ 2 = x := fun x => by
        rw [Nat.card_eq_fintype_card]; exact FiniteField.pow_card_pow 2 x
      rw [hfac]
      refine hcop.mul_dvd ?_ ?_
      · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, hrN, sub_self]
      · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, hrN, sub_self]
  have hker : aeval M (X ^ (Nat.card F) ^ 2 - X : K[X]) = 0 := by
    have h := Polynomial.map_dvd (algebraMap F K) hdvd
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] at h
    obtain ⟨q, hq⟩ := h
    rw [hq, map_mul, hpM, zero_mul]
  have hMunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]; exact isUnit_one
  simp only [map_sub, map_pow, aeval_X] at hker
  exact sub_eq_zero.1 hker


theorem false_of_fixed_trace [CharP K 2] {b : ℕ} (hb : b = padicValNat 3 (Nat.card K ^ 2 - 1))
    (hb1 : 1 ≤ b) (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1)
    (hord : ∀ m : ℕ, M ^ m = 1 → 3 ^ b ∣ m) (hτ : σ M.trace = M.trace) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, hF, hcard⟩ := natCard_eq_pow_three_of_order_three σ hσ3 hσ1
  haveI : Finite F := Finite.of_injective (Subfield.subtype F) Subtype.val_injective
  set N := Nat.card F with hN
  have hτF : M.trace ∈ F := (hF _).2 hτ
  have h3b : 3 ≤ 3 ^ b := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb1
  have hMunit : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]; exact isUnit_one
  by_cases ht0 : M.trace = 0
  · have h1 := sq_eq_trace_det M
    rw [hdet, ht0, zero_smul] at h1
    have hM2 : M ^ 2 = 1 := by
      rw [sq, h1, zero_sub, one_smul, CharTwo.neg_eq]
    have := hord 2 hM2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have hM := pow_card_sq_eq_self F hdet hτF ht0
    have hN2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ (Finite.card_pos)
    have hM1 : M ^ (N ^ 2 - 1) = 1 := by
      have h1 : M ^ (N ^ 2 - 1) * M = 1 * M := by
        rw [← pow_succ, Nat.sub_add_cancel hN2, one_mul]; exact hM
      exact (hMunit.mul_left_inj).1 h1
    have hdvd := hord _ hM1
    have hN1 : 1 < N := Finite.one_lt_card
    have hq : Nat.card K ^ 2 - 1 = (N ^ 2) ^ 3 - 1 ^ 3 := by
      rw [hcard, ← pow_mul, ← pow_mul, one_pow]
    have hlt : 1 < N ^ 2 := by nlinarith
    have h3dvd : 3 ∣ N ^ 2 - 1 := (dvd_pow_self 3 (by omega)).trans hdvd
    have h3ndvd : ¬ 3 ∣ N ^ 2 := by
      intro h
      have := (Nat.dvd_sub_iff_right (by omega) h).2 h3dvd
      omega
    have hlte := padicValNat.pow_sub_pow (p := 3) (by decide) hlt (by simpa using h3dvd) h3ndvd
      (n := 3) (by norm_num)
    rw [← hq] at hlte
    have hle : b ≤ padicValNat 3 (N ^ 2 - 1) :=
      (padicValNat_dvd_iff_le (by omega)).1 hdvd
    have h33 : padicValNat 3 3 = 1 := by simp
    rw [h33, ← hb] at hlte
    omega

end Field

end CFSG.HardMathSupport.Curtis.UnitaryLevi.LinA
