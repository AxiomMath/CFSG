module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8ModTora

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Matrix
open scoped CharTwo

private lemma sec12S8Mod_tor_charP_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 16) :
    CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hcp, m, hp, hcard⟩ := FiniteField.card' K
  have hcard16 : Fintype.card K = 16 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hpdvd : p ∣ 16 := by
    rw [← hcard16, hcard]
    exact dvd_pow_self p m.ne_zero
  have hp2 : p = 2 := by
    have h : p ∣ 2 ^ 4 := by simpa using hpdvd
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    exact le_antisymm (Nat.le_of_dvd (by norm_num) h2) hp.two_le
  rwa [hp2] at hcp

private lemma sec12S8Mod_tor_primRoot {K : Type} [Field K] [Finite K] (hK : Nat.card K = 16)
    {n : ℕ} (hn : n = 3 ∨ n = 5) : ∃ ζ : K, IsPrimitiveRoot ζ n := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hζ
  have hcard : Nat.card Kˣ = 15 := by rw [Nat.card_units, hK]
  have hprim : IsPrimitiveRoot ζ 15 := by rw [IsPrimitiveRoot.iff_orderOf, hord, hcard]
  rcases hn with rfl | rfl
  · refine ⟨((ζ ^ (15 / 3) : Kˣ) : K), ?_⟩
    have h := hprim.pow_of_dvd (by norm_num : 15 / 3 ≠ 0) (by norm_num : 15 / 3 ∣ 15)
    rw [show 15 / (15 / 3) = 3 by norm_num] at h
    exact IsPrimitiveRoot.coe_units_iff.mpr h
  · refine ⟨((ζ ^ (15 / 5) : Kˣ) : K), ?_⟩
    have h := hprim.pow_of_dvd (by norm_num : 15 / 5 ≠ 0) (by norm_num : 15 / 5 ∣ 15)
    rw [show 15 / (15 / 5) = 5 by norm_num] at h
    exact IsPrimitiveRoot.coe_units_iff.mpr h

private lemma sec12S8Mod_tor_charpoly_aeval {K : Type} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (hdet : A.det = 1) :
    A ^ 2 - A.trace • A + 1 = 0 := by
  have hCH := Matrix.aeval_self_charpoly A
  rw [Matrix.charpoly_fin_two, hdet] at hCH
  have hdiag : ∀ a : K, diagonal ((algebraMap K (Fin 2 → K)) a) =
      a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro a
    rw [Matrix.smul_one_eq_diagonal]
    congr 1
  have h : (Polynomial.aeval A) (Polynomial.X ^ 2 - Polynomial.C A.trace * Polynomial.X +
      Polynomial.C 1) = A ^ 2 - A.trace • A + 1 := by
    simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Matrix.algebraMap_eq_diagonal]
    rw [hdiag A.trace, hdiag 1, Matrix.smul_mul, Matrix.one_mul, one_smul]
  rw [h] at hCH
  exact hCH

private lemma sec12S8Mod_tor_det_aeval_prod {K : Type} [Field K]
    (A : Matrix (Fin 2) (Fin 2) K) (s : Finset K) (f : K → Polynomial K) :
    (Polynomial.aeval A (∏ ζ ∈ s, f ζ)).det =
      ∏ ζ ∈ s, (Polynomial.aeval A (f ζ)).det := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert ζ s hζ ih => rw [Finset.prod_insert hζ, map_mul, Matrix.det_mul, ih,
      Finset.prod_insert hζ]

private lemma sec12S8Mod_tor_eq_one_of_sq {G : Type} [Monoid G] {x : G} {n : ℕ}
    (hn : n = 3 ∨ n = 5) (h2 : x ^ 2 = 1) (hn1 : x ^ n = 1) : x = 1 := by
  rcases hn with rfl | rfl
  · rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, h2, one_mul, pow_one] at hn1
    exact hn1
  · rw [show (5 : ℕ) = 2 + 2 + 1 by norm_num, pow_add, pow_add, h2, one_mul, one_mul,
      pow_one] at hn1
    exact hn1

theorem sec12S8Mod_tor_diag {K : Type} [Field K] [Finite K] (hK : Nat.card K = 16) {n : ℕ}
    (hn : n = 3 ∨ n = 5) (M : SpecialLinearGroup (Fin 2) K) (hM : M ^ n = 1) (hM1 : M ≠ 1) :
    ∃ (P : Matrix (Fin 2) (Fin 2) K) (μ : K), IsUnit P.det ∧ μ ^ n = 1 ∧ μ ≠ 1 ∧
      (M : Matrix (Fin 2) (Fin 2) K) * P = P * Matrix.diagonal ![μ, μ⁻¹] := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := sec12S8Mod_tor_charP_two hK
  have hnpos : 0 < n := by rcases hn with h | h <;> omega
  obtain ⟨ζ, hζ⟩ := sec12S8Mod_tor_primRoot hK hn
  have hfac := Polynomial.X_pow_sub_one_eq_prod (R := K) hnpos hζ
  set A : Matrix (Fin 2) (Fin 2) K := (M : Matrix (Fin 2) (Fin 2) K) with hA
  have hAn : A ^ n = 1 := by
    rw [hA, ← SpecialLinearGroup.coe_pow, hM, SpecialLinearGroup.coe_one]
  have hdet : A.det = 1 := by rw [hA]; exact SpecialLinearGroup.det_coe M
  have halg : ∀ ζ : K, (algebraMap K (Matrix (Fin 2) (Fin 2) K)) ζ = ζ • 1 := by
    intro ζ
    rw [Matrix.algebraMap_eq_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
  have hterm : ∀ ζ : K, Polynomial.aeval A (Polynomial.X - Polynomial.C ζ) = A - ζ • 1 := by
    intro ζ
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, halg ζ]
  have hprod : (Polynomial.aeval A (∏ ζ ∈ Polynomial.nthRootsFinset n (1 : K),
      (Polynomial.X - Polynomial.C ζ))).det = 0 := by
    have h := congrArg (Polynomial.aeval A) hfac
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hAn, sub_self] at h
    rw [← h, Matrix.det_zero]
  have hproddet : (∏ ζ ∈ Polynomial.nthRootsFinset n (1 : K), (A - ζ • 1).det) = 0 := by
    have h := sec12S8Mod_tor_det_aeval_prod A (Polynomial.nthRootsFinset n (1 : K))
      (fun ζ => Polynomial.X - Polynomial.C ζ)
    rw [hprod] at h
    rw [Finset.prod_congr rfl (fun ζ _ => by rw [hterm ζ])] at h
    exact h.symm
  obtain ⟨μ, hμmem, hμdet⟩ := Finset.prod_eq_zero_iff.mp hproddet
  have hμn : μ ^ n = 1 := (Polynomial.mem_nthRootsFinset hnpos (1 : K)).mp hμmem
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow hnpos.ne'] at hμn
    exact one_ne_zero hμn.symm
  obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμdet
  have hAv : A *ᵥ v = μ • v := by
    have h := hv0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hcp : A.charpoly = Polynomial.X ^ 2 - Polynomial.C A.trace * Polynomial.X +
      Polynomial.C 1 := by rw [Matrix.charpoly_fin_two, hdet]
  have hscalar : ∀ a : K, Matrix.scalar (Fin 2) a = a • (1 : Matrix (Fin 2) (Fin 2) K) :=
    fun a => by rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hrootμ : A.charpoly.eval μ = 0 := by
    rw [Matrix.eval_charpoly, hscalar μ]
    have hsub : μ • (1 : Matrix (Fin 2) (Fin 2) K) - A = -(A - μ • 1) := (neg_sub _ _).symm
    rw [hsub, Matrix.det_neg]
    simp [hμdet]
  have hevalμ : μ ^ 2 - A.trace * μ + 1 = 0 := by
    have h := hrootμ
    rw [hcp] at h
    simpa using h
  have hevalν : (μ⁻¹) ^ 2 - A.trace * μ⁻¹ + 1 = 0 := by
    have h : μ ^ 2 - A.trace * μ + 1 = 0 := hevalμ
    have hthis : (μ⁻¹) ^ 2 - A.trace * μ⁻¹ + 1 =
        (μ⁻¹) ^ 2 * (μ ^ 2 - A.trace * μ + 1) := by
      field_simp [hμ0]
      ring
    rw [hthis, h, mul_zero]
  have hrootν : A.charpoly.eval (μ⁻¹) = 0 := by
    rw [hcp]
    simpa using hevalν
  have hdν : (A - μ⁻¹ • 1).det = 0 := by
    have h := hrootν
    rw [Matrix.eval_charpoly, hscalar (μ⁻¹)] at h
    have hsub : μ⁻¹ • (1 : Matrix (Fin 2) (Fin 2) K) - A = -(A - μ⁻¹ • 1) :=
      (neg_sub _ _).symm
    rw [hsub, Matrix.det_neg] at h
    simpa using h
  obtain ⟨v', hv'ne, hv'0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdν
  have hAv' : A *ᵥ v' = μ⁻¹ • v' := by
    have h := hv'0
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
    exact h
  have hμ1 : μ ≠ 1 := by
    intro h
    have ht : A.trace = 0 := by
      have h2 := hevalμ
      rw [h] at h2
      simp only [one_pow, mul_one] at h2
      rw [CharTwo.sub_eq_add, add_assoc, add_comm A.trace 1, ← add_assoc,
        CharTwo.add_self_eq_zero, zero_add] at h2
      exact h2
    have hA2 : A ^ 2 = 1 := by
      have h2 := sec12S8Mod_tor_charpoly_aeval A hdet
      rw [ht, zero_smul, sub_zero] at h2
      have hone : (1 : Matrix (Fin 2) (Fin 2) K) + 1 = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
      calc A ^ 2 = A ^ 2 + (1 + 1) := by rw [hone, add_zero]
        _ = (A ^ 2 + 1) + 1 := by rw [← add_assoc]
        _ = 0 + 1 := by rw [h2]
        _ = 1 := zero_add 1
    have hM2 : M ^ 2 = 1 := by
      apply Subtype.ext
      rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one, ← hA]
      exact hA2
    exact hM1 (sec12S8Mod_tor_eq_one_of_sq hn hM2 hM)
  let P : Matrix (Fin 2) (Fin 2) K := !![v 0, v' 0; v 1, v' 1]
  have hcol1 : ∀ i : Fin 2, A i 0 * v 0 + A i 1 * v 1 = μ * v i := by
    intro i
    have h := congrFun hAv i
    simpa [Matrix.mulVec, Fin.sum_univ_two] using h
  have hcol2 : ∀ i : Fin 2, A i 0 * v' 0 + A i 1 * v' 1 = μ⁻¹ * v' i := by
    intro i
    have h := congrFun hAv' i
    simpa [Matrix.mulVec, Fin.sum_univ_two] using h
  have hAP : A * P = P * Matrix.diagonal ![μ, μ⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_diagonal, hcol1, hcol2] <;>
      ring
  have hPdet : IsUnit P.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_cols_iff_isUnit]
    have hμν : μ ≠ μ⁻¹ := by
      intro h
      have h2 : μ ^ 2 = 1 := by
        have hh := mul_inv_cancel₀ hμ0
        rw [← h] at hh
        simpa [pow_two] using hh
      have hz : (μ + 1) ^ 2 = 0 := by
        rw [CharTwo.add_sq, h2]
        simp
      have hz2 : (μ + 1) ^ 2 = (0 : K) ^ 2 := by
        rw [hz, zero_pow (show (2 : ℕ) ≠ 0 by norm_num)]
      have hzero : μ + 1 = 0 := CharTwo.sq_inj.mp hz2
      exact hμ1 (CharTwo.add_eq_zero.mp hzero)
    have hli : LinearIndependent K ![v, v'] := by
      refine Module.End.eigenvectors_linearIndependent' (Matrix.mulVecLin A) ![μ, μ⁻¹] ?_
        ![v, v'] ?_
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · intro i
        fin_cases i
        · exact ⟨by simpa [Matrix.mulVecLin_apply] using hAv, hvne⟩
        · exact ⟨by simpa [Matrix.mulVecLin_apply] using hAv', hv'ne⟩
    have hPcol : P.col = ![v, v'] := by
      ext j i
      fin_cases j <;> fin_cases i <;> simp [P, Matrix.col]
    rwa [hPcol]
  refine ⟨P, μ, hPdet, hμn, hμ1, ?_⟩
  rwa [hA] at hAP

theorem sec12S8Mod_torus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 16)
    (g h : SpecialLinearGroup (Fin 2) K) (hg5 : g ^ 5 = 1) (hg1 : g ≠ 1) (hh3 : h ^ 3 = 1)
    (hh1 : h ≠ 1) :
    ∃ c w r : SpecialLinearGroup (Fin 2) K, c * g = g * c ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧
      w * g * w⁻¹ = g⁻¹ ∧ w * c * w⁻¹ = c⁻¹ ∧ r * h * r⁻¹ = c := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := sec12S8Mod_tor_charP_two hK
  obtain ⟨P, lam, hPunit, hlam5, hlam1, hgP⟩ := sec12S8Mod_tor_diag hK (Or.inr rfl) g hg5 hg1
  obtain ⟨Q, ω, hQunit, hω3, hω1, hhQ⟩ := sec12S8Mod_tor_diag hK (Or.inl rfl) h hh3 hh1
  have hPne : P.det ≠ 0 := isUnit_iff_ne_zero.mp hPunit
  have hQne : Q.det ≠ 0 := isUnit_iff_ne_zero.mp hQunit
  have hlam0 : lam ≠ 0 := by
    intro hh
    rw [hh, zero_pow (show (5 : ℕ) ≠ 0 by norm_num)] at hlam5
    exact one_ne_zero hlam5.symm
  have hω0 : ω ≠ 0 := by
    intro hh
    rw [hh, zero_pow (show (3 : ℕ) ≠ 0 by norm_num)] at hω3
    exact one_ne_zero hω3.symm
  let Dlam : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![lam, lam⁻¹]
  let Dω : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![ω, ω⁻¹]
  let S : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]
  let T : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![Q.det / P.det, 1]
  have hg : (g : Matrix (Fin 2) (Fin 2) K) = P * Dlam * P⁻¹ := by
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) * P * P⁻¹ = (g : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one]
    rw [← h1, hgP]
  have hh : (h : Matrix (Fin 2) (Fin 2) K) = Q * Dω * Q⁻¹ := by
    have h1 : (h : Matrix (Fin 2) (Fin 2) K) * Q * Q⁻¹ = (h : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Q hQunit, Matrix.mul_one]
    rw [← h1, hhQ]
  have hdetDlam : Dlam.det = 1 := by
    show (Matrix.diagonal ![lam, lam⁻¹]).det = 1
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using mul_inv_cancel₀ hlam0
  have hdetDω : Dω.det = 1 := by
    show (Matrix.diagonal ![ω, ω⁻¹]).det = 1
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simpa using mul_inv_cancel₀ hω0
  have hdetS : S.det = 1 := by
    show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Matrix.det_fin_two_of]
    simp
  have hdetT : T.det = Q.det / P.det := by
    show (Matrix.diagonal ![Q.det / P.det, 1]).det = Q.det / P.det
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp
  have hunitDlam : IsUnit Dlam.det := by rw [hdetDlam]; exact isUnit_one
  have hunitDω : IsUnit Dω.det := by rw [hdetDω]; exact isUnit_one
  have hunitS : IsUnit S.det := by rw [hdetS]; exact isUnit_one
  have hunitT : IsUnit T.det := by
    rw [hdetT]; exact isUnit_iff_ne_zero.mpr (div_ne_zero hQne hPne)
  have hDlaminv : Dlam⁻¹ = Matrix.diagonal ![lam⁻¹, lam] := by
    show (Matrix.diagonal ![lam, lam⁻¹])⁻¹ = Matrix.diagonal ![lam⁻¹, lam]
    exact sec12S8Mod_tora_diag_inv hlam0
  have hDωinv : Dω⁻¹ = Matrix.diagonal ![ω⁻¹, ω] := by
    show (Matrix.diagonal ![ω, ω⁻¹])⁻¹ = Matrix.diagonal ![ω⁻¹, ω]
    exact sec12S8Mod_tora_diag_inv hω0
  have hS2 : S * S = 1 := by
    show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hSinv : S⁻¹ = S := Matrix.inv_eq_right_inv hS2
  have hSlam : S * Dlam * S = Dlam⁻¹ := by
    rw [hDlaminv]
    show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![lam, lam⁻¹] *
        !![0, 1; 1, 0] = Matrix.diagonal ![lam⁻¹, lam]
    simp [Matrix.diagonal_fin_two, Matrix.mul_fin_two]
  have hSω : S * Dω * S = Dω⁻¹ := by
    rw [hDωinv]
    show (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * Matrix.diagonal ![ω, ω⁻¹] *
        !![0, 1; 1, 0] = Matrix.diagonal ![ω⁻¹, ω]
    simp [Matrix.diagonal_fin_two, Matrix.mul_fin_two]
  have hDcomm : Dω * Dlam = Dlam * Dω := by
    show Matrix.diagonal ![ω, ω⁻¹] * Matrix.diagonal ![lam, lam⁻¹] =
      Matrix.diagonal ![lam, lam⁻¹] * Matrix.diagonal ![ω, ω⁻¹]
    exact sec12S8Mod_tora_diag_comm _ _
  have hDω3 : Dω ^ 3 = 1 := by
    show (Matrix.diagonal ![ω, ω⁻¹]) ^ 3 = 1
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [Pi.pow_apply, hω3, inv_pow]
  have hTDω : T * Dω * T⁻¹ = Dω := by
    have hcomm : T * Dω = Dω * T := by
      show Matrix.diagonal ![Q.det / P.det, 1] * Matrix.diagonal ![ω, ω⁻¹] =
        Matrix.diagonal ![ω, ω⁻¹] * Matrix.diagonal ![Q.det / P.det, 1]
      exact sec12S8Mod_tora_diag_comm _ _
    rw [hcomm, Matrix.mul_assoc, Matrix.mul_nonsing_inv T hunitT, Matrix.mul_one]
  have hdetc : (P * Dω * P⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetDω, mul_one, mul_comm,
      Matrix.det_nonsing_inv_mul_det P hPunit]
  have hdetw : (P * S * P⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetS, mul_one, mul_comm,
      Matrix.det_nonsing_inv_mul_det P hPunit]
  have hdetr : (P * T * Q⁻¹).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetT]
    have hQinv : Q⁻¹.det = (Q.det)⁻¹ := by
      rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    rw [hQinv]
    field_simp [hPne, hQne]
  have hrinv : (P * T * Q⁻¹)⁻¹ = Q * T⁻¹ * P⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    calc (P * T * Q⁻¹) * (Q * T⁻¹ * P⁻¹)
        = P * T * (Q⁻¹ * Q) * T⁻¹ * P⁻¹ := by noncomm_ring
      _ = P * T * 1 * T⁻¹ * P⁻¹ := by rw [Matrix.nonsing_inv_mul Q hQunit]
      _ = P * (T * T⁻¹) * P⁻¹ := by noncomm_ring
      _ = P * 1 * P⁻¹ := by rw [Matrix.mul_nonsing_inv T hunitT]
      _ = 1 := by rw [Matrix.mul_one, Matrix.mul_nonsing_inv P hPunit]
  have hL2 : (P * T * Q⁻¹) * (Q * Dω * Q⁻¹) * (Q * T⁻¹ * P⁻¹) = P * Dω * P⁻¹ := by
    calc (P * T * Q⁻¹) * (Q * Dω * Q⁻¹) * (Q * T⁻¹ * P⁻¹)
        = P * T * (Q⁻¹ * Q) * Dω * (Q⁻¹ * Q) * T⁻¹ * P⁻¹ := by noncomm_ring
      _ = P * T * 1 * Dω * 1 * T⁻¹ * P⁻¹ := by rw [Matrix.nonsing_inv_mul Q hQunit]
      _ = P * (T * Dω * T⁻¹) * P⁻¹ := by noncomm_ring
      _ = P * Dω * P⁻¹ := by rw [hTDω]
  let c : SpecialLinearGroup (Fin 2) K := ⟨P * Dω * P⁻¹, hdetc⟩
  let w : SpecialLinearGroup (Fin 2) K := ⟨P * S * P⁻¹, hdetw⟩
  let r : SpecialLinearGroup (Fin 2) K := ⟨P * T * Q⁻¹, hdetr⟩
  refine ⟨c, w, r, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hg]
    change (P * Dω * P⁻¹) * (P * Dlam * P⁻¹) = (P * Dlam * P⁻¹) * (P * Dω * P⁻¹)
    rw [sec12S8Mod_tora_conj_mul hPunit, sec12S8Mod_tora_conj_mul hPunit, hDcomm]
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_pow, SpecialLinearGroup.coe_one]
    change (P * Dω * P⁻¹) ^ 3 = 1
    rw [sec12S8Mod_tora_conj_pow hPunit 3, hDω3, Matrix.mul_one,
      Matrix.mul_nonsing_inv P hPunit]
  · intro hc
    have hmat : (P * Dω * P⁻¹) = 1 := by
      have h := congrArg (fun x : SpecialLinearGroup (Fin 2) K =>
        (x : Matrix (Fin 2) (Fin 2) K)) hc
      simpa [SpecialLinearGroup.coe_one] using h
    have hDω1 : Dω = 1 := by
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => P⁻¹ * M * P) hmat
      rw [Matrix.mul_one] at h
      rw [show P⁻¹ * (P * Dω * P⁻¹) * P = (P⁻¹ * P) * Dω * (P⁻¹ * P) by noncomm_ring,
        Matrix.nonsing_inv_mul P hPunit] at h
      simpa using h
    have hω : ω = 1 := by
      have h00 := congrFun (congrFun hDω1 0) 0
      simpa [Dω] using h00
    exact hω1 hω
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, sec12S8Mod_tora_coe_inv w,
      sec12S8Mod_tora_coe_inv g, hg]
    change (P * S * P⁻¹) * (P * Dlam * P⁻¹) * (P * S * P⁻¹)⁻¹ = (P * Dlam * P⁻¹)⁻¹
    rw [sec12S8Mod_tora_conj_inv hPunit hunitS, hSinv, sec12S8Mod_tora_conj_mul hPunit,
      sec12S8Mod_tora_conj_mul hPunit, hSlam, sec12S8Mod_tora_conj_inv hPunit hunitDlam]
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, sec12S8Mod_tora_coe_inv w,
      sec12S8Mod_tora_coe_inv c]
    change (P * S * P⁻¹) * (P * Dω * P⁻¹) * (P * S * P⁻¹)⁻¹ = (P * Dω * P⁻¹)⁻¹
    rw [sec12S8Mod_tora_conj_inv hPunit hunitS, hSinv, sec12S8Mod_tora_conj_mul hPunit,
      sec12S8Mod_tora_conj_mul hPunit, hSω, sec12S8Mod_tora_conj_inv hPunit hunitDω]
  · apply Subtype.ext
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, sec12S8Mod_tora_coe_inv r, hh]
    change (P * T * Q⁻¹) * (Q * Dω * Q⁻¹) * (P * T * Q⁻¹)⁻¹ = P * Dω * P⁻¹
    rw [hrinv, hL2]

end CFSG.OddStandard.SmallF3.Omega
