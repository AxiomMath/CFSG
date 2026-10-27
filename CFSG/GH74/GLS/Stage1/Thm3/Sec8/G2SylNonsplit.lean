module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl

namespace Nonsplit

open QuadraticAlgebra

section Rep

variable {K : Type*} [CommRing K]

def repMat (z : QuadraticAlgebra K (-1 : K) 0) : Matrix (Fin 2) (Fin 2) K :=
  !![z.re, -z.im; z.im, z.re]

theorem repMat_mul (z w : QuadraticAlgebra K (-1 : K) 0) :
    repMat (z * w) = repMat z * repMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem repMat_one : repMat (1 : QuadraticAlgebra K (-1 : K) 0) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat]

theorem repMat_neg_one : repMat (-1 : QuadraticAlgebra K (-1 : K) 0) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat]

def repHom : QuadraticAlgebra K (-1 : K) 0 →* Matrix (Fin 2) (Fin 2) K where
  toFun := repMat
  map_one' := repMat_one
  map_mul' := repMat_mul

theorem repMat_pow (z : QuadraticAlgebra K (-1 : K) 0) (k : ℕ) :
    repMat (z ^ k) = repMat z ^ k :=
  map_pow repHom z k

theorem det_repMat (z : QuadraticAlgebra K (-1 : K) 0) :
    (repMat z).det = z.re * z.re + z.im * z.im := by
  simp [repMat, Matrix.det_fin_two]

theorem conj_repMat (z : QuadraticAlgebra K (-1 : K) 0) :
    !![(1 : K), 0; 0, -1] * repMat z * !![(1 : K), 0; 0, -1] = repMat (star z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem conj_mul_repMat (z : QuadraticAlgebra K (-1 : K) 0) :
    !![(1 : K), 0; 0, -1] * repMat z = repMat (star z) * !![(1 : K), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem delta_repMat (z : QuadraticAlgebra K (-1 : K) 0) :
    !![(-1 : K), 0; 0, 1] * repMat z * !![(-1 : K), 0; 0, 1] = repMat (star z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem delta_repMat_conj (z : QuadraticAlgebra K (-1 : K) 0) :
    !![(-1 : K), 0; 0, 1] * (repMat z * !![(1 : K), 0; 0, -1]) * !![(-1 : K), 0; 0, 1] =
      repMat (star z) * !![(1 : K), 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem adjugate_repMat (z : QuadraticAlgebra K (-1 : K) 0) :
    (repMat z).adjugate = repMat (star z) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [repMat, Matrix.adjugate_fin_two]

end Rep

section Frobenius

variable {K : Type*} [Field K] [Finite K]

theorem pow_card_eq_star (hK : Nat.card K % 4 = 3) (z : QuadraticAlgebra K (-1 : K) 0) :
    z ^ Nat.card K = star z := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  obtain ⟨f, hfp, hq⟩ := FiniteField.card K p
  rw [Nat.card_eq_fintype_card] at hK ⊢
  have : CharP (QuadraticAlgebra K (-1 : K) 0) p :=
    charP_of_injective_algebraMap
      (algebraMap_injective (R := K) (a := (-1 : K)) (b := (0 : K))) p
  have hxq : ∀ x : K, x ^ (p ^ (f : ℕ)) = x := fun x => by
    rw [← hq]; exact FiniteField.pow_card x
  have hω2 : (QuadraticAlgebra.omega : QuadraticAlgebra K (-1 : K) 0) ^ 2 = -1 := by
    rw [sq, omega_mul_omega_eq_mk]; ext <;> simp
  have hω4 : (QuadraticAlgebra.omega : QuadraticAlgebra K (-1 : K) 0) ^ 4 = 1 := by
    calc (QuadraticAlgebra.omega : QuadraticAlgebra K (-1 : K) 0) ^ 4
        = (QuadraticAlgebra.omega ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hω2]; norm_num
  have hω3 : (QuadraticAlgebra.omega : QuadraticAlgebra K (-1 : K) 0) ^ 3
      = -QuadraticAlgebra.omega := by
    rw [pow_succ, hω2]; ring
  obtain ⟨t, ht⟩ : ∃ t, Fintype.card K = 4 * t + 3 := ⟨Fintype.card K / 4, by omega⟩
  have hωq : (QuadraticAlgebra.omega : QuadraticAlgebra K (-1 : K) 0) ^ (p ^ (f : ℕ))
      = -QuadraticAlgebra.omega := by
    rw [← hq, ht, pow_add, pow_mul, hω4, one_pow, one_mul, hω3]
  have hz : z = algebraMap K _ z.re + algebraMap K _ z.im * QuadraticAlgebra.omega := by
    ext <;> simp
  calc z ^ Fintype.card K
      = (algebraMap K _ z.re + algebraMap K _ z.im * QuadraticAlgebra.omega) ^ (p ^ (f : ℕ)) := by
        rw [← hz, hq]
    _ = algebraMap K _ z.re + algebraMap K _ z.im * (-QuadraticAlgebra.omega) := by
        rw [add_pow_char_pow, mul_pow, hωq, ← map_pow, ← map_pow, hxq, hxq]
    _ = star z := by ext <;> simp

end Frobenius

section Sigma

variable {K : Type*} [Field K] [Finite K]

instance : Finite (QuadraticAlgebra K (-1 : K) 0) :=
  Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd _ _).symm

omit [Finite K] in
theorem natCard_quadraticAlgebra :
    Nat.card (QuadraticAlgebra K (-1 : K) 0) = Nat.card K ^ 2 := by
  rw [Nat.card_congr (QuadraticAlgebra.equivProd _ _), Nat.card_prod, sq]

theorem exists_sigma [Fact (¬ IsSquare (-1 : K))] (hK : Nat.card K % 4 = 3) :
    ∃ σ : QuadraticAlgebra K (-1 : K) 0, σ ^ (Nat.card K + 1) = -1 ∧
      σ ^ 2 ^ ((Nat.card K + 1).factorization 2) = -1 := by
  set q := Nat.card K with hq_def
  set n := (q + 1).factorization 2 with hn_def
  have hq1 : q + 1 ≠ 0 := Nat.succ_ne_zero q
  set r := (q + 1) / 2 ^ n with hr_def
  have hr : q + 1 = 2 ^ n * r := (Nat.ordProj_mul_ordCompl_eq_self (q + 1) 2).symm
  have hr_odd : Odd r := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hq1)
  obtain ⟨s, hs⟩ : ∃ s, q = 2 * s + 1 := ⟨q / 2, by omega⟩
  have hs_odd : Odd s := by rw [Nat.odd_iff]; omega
  have hN : Nat.card (QuadraticAlgebra K (-1 : K) 0)ˣ = 2 ^ (n + 1) * (s * r) := by
    rw [Nat.card_units, natCard_quadraticAlgebra]
    have h1 : 1 ≤ q := by omega
    have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h3 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      zify [h1, h2]; ring
    rw [h3, hr, show q - 1 = 2 * s by omega]
    ring
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (QuadraticAlgebra K (-1 : K) 0)ˣ)
  have hm0 : s * r ≠ 0 := by
    have : 0 < s * r := Nat.mul_pos hs_odd.pos hr_odd.pos
    omega
  have hdvd : s * r ∣ orderOf g := by
    rw [hg, hN]; exact Dvd.intro_left _ rfl
  set σ : QuadraticAlgebra K (-1 : K) 0 := ((g ^ (s * r) : (QuadraticAlgebra K (-1 : K) 0)ˣ) :
    QuadraticAlgebra K (-1 : K) 0) with hσ_def
  have hord : orderOf σ = 2 ^ (n + 1) := by
    rw [hσ_def, orderOf_units, orderOf_pow_of_dvd hm0 hdvd, hg, hN,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hσ1 : σ ^ 2 ^ (n + 1) = 1 := by rw [← hord]; exact pow_orderOf_eq_one σ
  refine ⟨σ, ?_, ?_⟩
  · have hsq : σ ^ (q + 1) * σ ^ (q + 1) = 1 := by
      rw [← pow_add]
      have : q + 1 + (q + 1) = 2 ^ (n + 1) * r := by
        rw [pow_succ]; linarith [hr]
      rw [this, pow_mul, hσ1, one_pow]
    refine (mul_self_eq_one_iff.mp hsq).resolve_left ?_
    intro hx
    have h1 : 2 ^ (n + 1) ∣ q + 1 := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hx
    have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hq1).1 h1
    omega
  · have hsq : σ ^ 2 ^ n * σ ^ 2 ^ n = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ']; exact hσ1
    refine (mul_self_eq_one_iff.mp hsq).resolve_left ?_
    intro hx
    have h1 : 2 ^ (n + 1) ∣ 2 ^ n := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hx
    have h2 := Nat.le_of_dvd (by positivity) h1
    have h3 : 2 ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega

end Sigma

section Assembly

variable {K : Type*} [CommRing K]

@[expose] def mkSL (M : Matrix (Fin 2) (Fin 2) K) (h : M.det = 1) :
    Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨M, h⟩

@[simp] theorem coe_mkSL (M : Matrix (Fin 2) (Fin 2) K) (h : M.det = 1) :
    (mkSL M h : Matrix (Fin 2) (Fin 2) K) = M := rfl

theorem exists_quaternion_of_sigma (q n s : ℕ) (hq : q = 2 * s + 1) (hn : 1 ≤ n)
    (σ : QuadraticAlgebra K (-1 : K) 0)
    (hfrob : σ ^ q = star σ) (h1 : σ ^ (q + 1) = -1) (h2 : σ ^ (2 ^ n) = -1) :
    ∃ c w : Matrix.SpecialLinearGroup (Fin 2) K,
      c ^ (2 ^ n) = 1 ∧ c ^ (2 ^ (n - 1)) = -1 ∧ w * w = -1 ∧ w * c * w⁻¹ = c⁻¹ ∧
      (!![(-1 : K), 0; 0, 1] * (c : Matrix (Fin 2) (Fin 2) K) * !![(-1 : K), 0; 0, 1] =
          ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ∧
      (!![(-1 : K), 0; 0, 1] * (w : Matrix (Fin 2) (Fin 2) K) * !![(-1 : K), 0; 0, 1] =
          ((c ^ s * w : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  have hnorm : σ.re * σ.re + σ.im * σ.im = -1 := by
    have h : σ * star σ = -1 := by rw [← hfrob, ← pow_succ']; exact h1
    have := congrArg QuadraticAlgebra.re h
    simpa using this
  have hdet1 : (repMat σ).det = -1 := by rw [det_repMat]; exact hnorm
  have hc : (repMat (σ ^ 2)).det = 1 := by
    rw [pow_two, repMat_mul, Matrix.det_mul, hdet1]; norm_num
  have hw : (repMat σ * !![(1 : K), 0; 0, -1]).det = 1 := by
    rw [Matrix.det_mul, hdet1]; simp [Matrix.det_fin_two]
  have hn' : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine ⟨mkSL (repMat (σ ^ 2)) hc, mkSL (repMat σ * !![(1 : K), 0; 0, -1]) hw,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, coe_mkSL, Matrix.SpecialLinearGroup.coe_one]
    rw [← repMat_pow, pow_right_comm, h2, neg_one_sq, repMat_one]
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_pow, coe_mkSL, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    rw [← repMat_pow, ← pow_mul, ← hn', h2, repMat_neg_one]
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_mkSL, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    calc repMat σ * !![(1 : K), 0; 0, -1] * (repMat σ * !![(1 : K), 0; 0, -1])
        = repMat σ * (!![(1 : K), 0; 0, -1] * repMat σ * !![(1 : K), 0; 0, -1]) := by
          simp only [Matrix.mul_assoc]
      _ = -1 := by
          rw [conj_repMat, ← repMat_mul, ← hfrob, ← pow_succ', h1, repMat_neg_one]
  · rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_mkSL, Matrix.SpecialLinearGroup.coe_inv,
      adjugate_repMat]
    calc repMat σ * !![(1 : K), 0; 0, -1] * repMat (σ ^ 2)
        = repMat σ * (!![(1 : K), 0; 0, -1] * repMat (σ ^ 2)) := by
          simp only [Matrix.mul_assoc]
      _ = repMat (σ * star (σ ^ 2)) * !![(1 : K), 0; 0, -1] := by
          rw [conj_mul_repMat, ← Matrix.mul_assoc, ← repMat_mul]
      _ = repMat (star (σ ^ 2)) * (repMat σ * !![(1 : K), 0; 0, -1]) := by
          rw [← Matrix.mul_assoc, ← repMat_mul, mul_comm]
  · simp only [Matrix.SpecialLinearGroup.coe_inv, coe_mkSL, adjugate_repMat]
    exact delta_repMat _
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow, coe_mkSL]
    rw [delta_repMat_conj, ← repMat_pow, ← Matrix.mul_assoc, ← repMat_mul, ← pow_mul, ← pow_succ,
      ← hq, hfrob]

end Assembly

end Nonsplit

open Nonsplit

theorem exists_nonsplit_quaternion (K : Type) [Field K] [Finite K] (hK : Nat.card K % 4 = 3) :
    ∃ (n s : ℕ) (c w : Matrix.SpecialLinearGroup (Fin 2) K),
      (Nat.card K + 1).factorization 2 = n ∧ 2 ≤ n ∧ Odd s ∧
      c ^ (2 ^ n) = 1 ∧ c ^ (2 ^ (n - 1)) = -1 ∧ w * w = -1 ∧ w * c * w⁻¹ = c⁻¹ ∧
      (!![(-1 : K), 0; 0, 1] * (c : Matrix (Fin 2) (Fin 2) K) * !![(-1 : K), 0; 0, 1] =
          ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) ∧
      (!![(-1 : K), 0; 0, 1] * (w : Matrix (Fin 2) (Fin 2) K) * !![(-1 : K), 0; 0, 1] =
          ((c ^ s * w : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) := by
  have hnsq : ¬ IsSquare (-1 : K) := by
    have : Fintype K := Fintype.ofFinite K
    intro h
    have h' := FiniteField.isSquare_neg_one_iff.mp h
    rw [← Nat.card_eq_fintype_card] at h'
    omega
  have : Fact (¬ IsSquare (-1 : K)) := ⟨hnsq⟩
  obtain ⟨σ, h1, h2⟩ := exists_sigma hK
  obtain ⟨s, hs⟩ : ∃ s, Nat.card K = 2 * s + 1 := ⟨Nat.card K / 2, by omega⟩
  have hs_odd : Odd s := by rw [Nat.odd_iff]; omega
  have hn2 : 2 ≤ (Nat.card K + 1).factorization 2 := by
    rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.succ_ne_zero _)]
    exact Nat.dvd_of_mod_eq_zero (by omega)
  obtain ⟨c, w, hc, hc2, hw, hwc, hcδ, hwδ⟩ := exists_quaternion_of_sigma (Nat.card K)
    ((Nat.card K + 1).factorization 2) s hs (by omega) σ (pow_card_eq_star hK σ) h1 h2
  exact ⟨_, s, c, w, rfl, hn2, hs_odd, hc, hc2, hw, hwc, hcδ, hwδ⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl
