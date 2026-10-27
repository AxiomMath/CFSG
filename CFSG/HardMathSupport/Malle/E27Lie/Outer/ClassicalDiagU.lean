module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryPSU

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

open scoped Classical in
theorem exists_perfect_three_dvd_autFix_of_diag [Finite K] (hℓ3 : ℓ ≠ 3)
    (hq : (4 ≤ ℓ ^ f ∧ 4 ≤ n) ∨ (ℓ ^ f = 2 ∧ 10 ≤ n)) (y : primeFormUnitary h (idGram K n))
    (c : Kˣ) (hyp : (y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c) :
    ∃ R : Subgroup (primeFormP h (idGram K n)),
      R ≤ autFix (primeFormConjHom h (idGram K n) y) ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R := by
  have hℓ := h.prime
  have : CharP K ℓ := h.charP
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y h3K hyp
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) = Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (Matrix.toLin'_apply' _).symm
  have hdeg : (minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K))).natDegree ≤ 3 := by
    have hdvd : minpoly K ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) ∣ (X ^ 3 - C (c : K) : K[X]) := by
      refine minpoly.dvd K _ ?_
      rw [hX]
      exact SPLCell.aeval_linEnd_X_pow_sub_C c hyp
    have hne0 : (X ^ 3 - C (c : K) : K[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
    have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [natDegree_X_pow_sub_C] at h4
  have hfr : Module.finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hgood : ∃ a : primaryFactors ((toLinU h n y : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)), IsGoodBlock h (toLinU h n y) a := by
    rcases hq with ⟨hq4, hn4⟩ | ⟨hq2, hn10⟩
    · obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 1) hx hdeg (by omega)
      exact ⟨a, isGoodBlock_of_numeric a (by omega) (fun _ => hq4) (fun _ => by omega)⟩
    · obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 3) hx hdeg (by omega)
      exact ⟨a, isGoodBlock_of_numeric a (by omega) (fun e => by omega) (fun e => by omega)⟩
  obtain ⟨a, ha⟩ := hgood
  obtain ⟨Q, hQc, hQd, hQ, hQ3⟩ := exists_quasisimple_three_dvd_block h3K hℓ3 hx a ha
  exact exists_perfect_three_dvd_autFix_of_quasisimple y Q hQc hQd hQ hQ3

theorem primeFormConjHom_eq_one_iff' (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A = 1 ↔ A ∈ idScalarKernel h n := by
  have key := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne).2.2.1 ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  rw [key]
  constructor
  · rintro ⟨-, c, hc, hA⟩
    exact ⟨c, (pow_succ_eq_one_iff_norm h c).mpr hc, hA⟩
  · rintro ⟨c, hc, hA⟩
    exact ⟨rfl, c, (pow_succ_eq_one_iff_norm h c).mp hc, hA⟩

theorem exists_scalar_of_conjHom_pow_three (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (y : primeFormUnitary h (idGram K n))
    (h3 : primeFormConjHom h (idGram K n) y ^ 3 = 1) :
    ∃ c : Kˣ, (y : GL (Fin n) K) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
  have h1 : primeFormConjHom h (idGram K n) (y ^ 3) = 1 := by rw [map_pow]; exact h3
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff' hn hne (y ^ 3)).1 h1
  exact ⟨c, by simpa using hc⟩

end CFSG.HardMathSupport.Malle.E27Lie
