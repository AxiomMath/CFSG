module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.UnitaryPSU

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.FOC CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Curtis.Coordinator
  CFSG.HardMathSupport.Curtis.Coordinator.SPLCell.Uni

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {ℓ f n : ℕ} {F : Type} [Field F] {h : UnitaryFieldData ℓ f F}

theorem card_units_eq_three_of_pow_eq_two (h : UnitaryFieldData ℓ f F) (hq : ℓ ^ f = 2) :
    Nat.card Fˣ = 3 := by
  have hfin := h.finite
  have : Fintype F := Fintype.ofFinite F
  have h4 : Nat.card F = 4 := by
    rw [h.card, pow_mul', hq]
    norm_num
  rw [Nat.card_units, h4]

theorem no_cube_root_of_card_units_three (h3 : Nat.card Fˣ = 3) {c : Fˣ} (hc : c ≠ 1) (x : F) :
    x ^ 3 ≠ (c : F) := by
  intro hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact c.ne_zero (by rw [← hx]; norm_num)
  have hu : (Units.mk0 x hx0) ^ 3 = c := Units.ext (by simpa using hx)
  have h1 : (Units.mk0 x hx0) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 x hx0)
    rwa [h3] at this
  exact hc (hu.symm.trans h1)

theorem irreducible_X_pow_three_sub_C (h3 : Nat.card Fˣ = 3) {c : Fˣ} (hc : c ≠ 1) :
    Irreducible (X ^ 3 - C (c : F) : F[X]) := by
  have hm : (X ^ 3 - C (c : F) : F[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hd : (X ^ 3 - C (c : F) : F[X]).natDegree = 3 := natDegree_X_pow_sub_C
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [mem_roots hm.ne_zero, IsRoot.def] at hx
  apply no_cube_root_of_card_units_three h3 hc x
  simpa [sub_eq_zero] using hx

theorem exists_perfect_three_dvd_autFix_of_unitary_two [Finite F] (hq : ℓ ^ f = 2)
    (hn : n = 6 ∨ n = 9) (y : primeFormUnitary h (idGram F n)) (c : Fˣ) (hc : c ≠ 1)
    (hyp : (y : GL (Fin n) F) ^ 3 = GeneralLinearGroup.scalar (Fin n) c) :
    ∃ R : Subgroup (primeFormP h (idGram F n)),
      R ≤ autFix (primeFormConjHom h (idGram F n) y) ∧ ⁅R, R⁆ = R ∧ 3 ∣ Nat.card R := by
  have hℓ := h.prime
  have : CharP F ℓ := h.charP
  have hℓ3 : ℓ ≠ 3 := by
    intro h3
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3K : ((3 : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F ℓ]
    intro hd
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 hd)
  have hx := squarefree_minpoly_toLinU_of_pow_scalar y h3K hyp
  have hX : ((toLinU h n y : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) = Matrix.toLin' ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    (Matrix.toLin'_apply' _).symm
  have hdvd : minpoly F ((toLinU h n y : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) ∣ (X ^ 3 - C (c : F) : F[X]) := by
    refine minpoly.dvd F _ ?_
    rw [hX]
    exact SPLCell.aeval_linEnd_X_pow_sub_C c hyp
  have hne0 : (X ^ 3 - C (c : F) : F[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have hdeg : (minpoly F ((toLinU h n y : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F))).natDegree ≤ 3 := by
    have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
    rwa [natDegree_X_pow_sub_C] at h4
  have hirr := irreducible_X_pow_three_sub_C (card_units_eq_three_of_pow_eq_two h hq) hc
  have hfr : Module.finrank F (Fin n → F) = n := Module.finrank_fin_fun F
  obtain ⟨a, ha⟩ := exists_primaryMultiplicity_gt (M := 1) hx hdeg (by omega)
  have haeq : (a : F[X]) = X ^ 3 - C (c : F) := by
    obtain ⟨hai, ham, hadvd⟩ := mem_primaryFactors.mp a.2
    exact eq_of_monic_of_associated ham (monic_X_pow_sub_C _ (by norm_num))
      (hai.associated_of_dvd hirr (hadvd.trans hdvd))
  have hadeg : (a : F[X]).natDegree = 3 := by rw [haeq, natDegree_X_pow_sub_C]
  have hpow : ℓ ^ (f * (a : F[X]).natDegree) = 8 := by
    rw [hadeg, pow_mul, hq]
    norm_num
  have hgood : IsGoodBlock h (toLinU h n y) a :=
    isGoodBlock_of_numeric' a (by omega) (fun _ => by omega) (fun _ => by omega)
  obtain ⟨Q, hQc, hQd, hQ, hQ3⟩ := exists_quasisimple_three_dvd_block h3K hℓ3 hx a hgood
  exact exists_perfect_three_dvd_autFix_of_quasisimple y Q hQc hQd hQ hQ3

end CFSG.HardMathSupport.Malle.E27Lie
