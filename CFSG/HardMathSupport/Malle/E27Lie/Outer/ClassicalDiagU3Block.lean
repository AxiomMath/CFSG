module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryPSU

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni

namespace CFSG.HardMathSupport.Malle.E27Lie

open scoped Classical in
theorem exists_mult_two_or_finrank_le_degree {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {x : Module.End K V} (hx : Squarefree (minpoly K x)) :
    (∃ a : primaryFactors x, 2 ≤ primaryMultiplicity x (a : K[X])) ∨
      Module.finrank K V ≤ (minpoly K x).natDegree := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hle, hlt⟩ := hcon
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  have h1 : Module.finrank K V ≤ ∑ a : primaryFactors x, (a : K[X]).natDegree := by
    refine hsum.le.trans (Finset.sum_le_sum fun a _ => ?_)
    have := hle a
    nlinarith
  have hprod := prod_primaryFactors hx
  have hne : ∀ a ∈ primaryFactors x, a ≠ 0 := fun a ha =>
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor a
      (Multiset.mem_toFinset.1 ha)).ne_zero
  have hdeg' : (minpoly K x).natDegree = ∑ a ∈ primaryFactors x, a.natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ hne]
  have h2 : ∑ a : primaryFactors x, (a : K[X]).natDegree = ∑ a ∈ primaryFactors x, a.natDegree :=
    Finset.sum_coe_sort (primaryFactors x) fun a => a.natDegree
  rw [h2, ← hdeg'] at h1
  omega

section Det

variable {F : Type} [Field F]

theorem det_eq_of_minpoly_toLin_three (M : Matrix (Fin 3) (Fin 3) F) (c : F)
    (hmin : minpoly F (Matrix.toLin' M) = X ^ 3 - C c) : M.det = c := by
  have hch : (Matrix.toLin' M).charpoly = X ^ 3 - C c := by
    have hd : minpoly F (Matrix.toLin' M) ∣ (Matrix.toLin' M).charpoly :=
      LinearMap.minpoly_dvd_charpoly _
    rw [hmin] at hd
    have hmon : (Matrix.toLin' M).charpoly.Monic := LinearMap.charpoly_monic _
    have hnd : (Matrix.toLin' M).charpoly.natDegree = 3 := by
      rw [LinearMap.charpoly_natDegree, Module.finrank_fin_fun]
    exact eq_of_monic_of_dvd_of_natDegree_le (monic_X_pow_sub_C _ (by norm_num)) hmon hd
      (by rw [hnd, natDegree_X_pow_sub_C])
  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Matrix.toLin' M)
  rw [LinearMap.det_toLin', hch, Module.finrank_fin_fun] at hdet
  rw [hdet]
  simp [coeff_sub, coeff_X_pow, coeff_C]
  ring

end Det

variable {ℓ f : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

theorem unitary_three_block_or_det [Finite F] (hℓ3 : ℓ ≠ 3) (hq : 4 ≤ ℓ ^ f)
    (y : primeFormUnitary h (idGram F 3)) (c : Fˣ)
    (hyc : (y : GL (Fin 3) F) ^ 3 = GeneralLinearGroup.scalar (Fin 3) c) :
    (∃ R : Subgroup (primeFormP h (idGram F 3)),
      R ≤ autFix (primeFormConjHom h (idGram F 3) y) ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R) ∨
    ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = c := by
  classical
  have hℓ := h.prime
  have : CharP F ℓ := h.charP
  have h3K : ((3 : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y h3K hyc
  have hX : ((toLinU h 3 y : LinearMap.GeneralLinearGroup F (Fin 3 → F)) :
      Module.End F (Fin 3 → F)) = Matrix.toLin' ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    (Matrix.toLin'_apply' _).symm
  rcases exists_mult_two_or_finrank_le_degree hx with ⟨a, ha⟩ | hdeg
  · left
    have hgood := isGoodBlock_of_numeric a ha (fun _ => hq) (fun _ => by omega)
    obtain ⟨Q, hQc, hQd, hQ, hQ3⟩ := exists_quasisimple_three_dvd_block h3K hℓ3 hx a hgood
    exact exists_perfect_three_dvd_autFix_of_quasisimple y Q hQc hQd hQ hQ3
  · right
    rw [Module.finrank_fin_fun] at hdeg
    rw [hX] at hdeg hx
    have hdvd : minpoly F (Matrix.toLin' ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∣
        (X ^ 3 - C (c : F) : F[X]) :=
      minpoly.dvd F _ (SPLCell.aeval_linEnd_X_pow_sub_C c hyc)
    have hint : IsIntegral F (Matrix.toLin' ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
      Algebra.IsIntegral.isIntegral _
    exact det_eq_of_minpoly_toLin_three _ _
      ((eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
        (monic_X_pow_sub_C _ (by norm_num)) hdvd (by rw [natDegree_X_pow_sub_C]; omega)).symm)

theorem norm_det_eq_one (y : primeFormUnitary h (idGram F 3)) :
    h.norm ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 := by
  have hy := mem_primeFormUnitary.mp y.2
  have := congrArg Matrix.det hy
  simp only [idGram, Units.val_one, Matrix.mul_one, Matrix.det_mul, Matrix.det_transpose] at this
  have h2 : ((((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)).det =
      h.bar ((y : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [h2, Matrix.det_one] at this
  rw [UnitaryFieldData.norm, mul_comm]
  exact this

theorem norm_eq_one_of_norm_cube_eq_one [Finite F] (hg : 3 ∣ ℓ ^ f + 1) (b : F) (hb : b ≠ 0)
    (hN : h.norm (b ^ 3) = 1) : h.norm b = 1 := by
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
  have := Fintype.ofFinite F
  have hcard : Fintype.card F = (ℓ ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card, pow_mul']
  have hb1 : b ^ ((ℓ ^ f) ^ 2 - 1) = 1 := by
    rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one b hb
  set q := ℓ ^ f with hq
  have hnorm : ∀ x : F, h.norm x = x ^ (q + 1) := fun x => by
    rw [h.norm_eq_pow]
  rw [hnorm] at hN ⊢
  set w := b ^ (q + 1) with hw
  have hw3 : w ^ 3 = 1 := by rw [hw, ← pow_mul, mul_comm, pow_mul]; simpa using hN
  have hwq1 : w ^ (q - 1) = 1 := by
    rw [hw, ← pow_mul]
    have : (q + 1) * (q - 1) = q ^ 2 - 1 := by
      zify [hq1, (by nlinarith : 1 ≤ q ^ 2)]
      ring
    rw [this]; exact hb1
  have hwq : w ^ (q + 1) = 1 := by
    obtain ⟨k, hk⟩ := hg
    rw [hk, pow_mul, hw3, one_pow]
  have hw2 : w ^ 2 = 1 := by
    have : w ^ (q + 1) = w ^ (q - 1) * w ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hwq1, one_mul] at this
    rw [← this, hwq]
  calc w = w * w ^ 2 := by rw [hw2, mul_one]
    _ = 1 := by rw [← pow_succ']; exact hw3

end CFSG.HardMathSupport.Malle.E27Lie
