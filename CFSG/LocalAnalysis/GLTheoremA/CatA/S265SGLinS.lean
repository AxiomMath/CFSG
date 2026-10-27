module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGLinCore
import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open Polynomial Module
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary

theorem SG.exists_sl2_split {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 4 ≤ n)
    (hF : 3 ∣ Nat.card F - 1) {Bt : Subgroup (Matrix.SpecialLinearGroup (Fin n) F)}
    (hB3 : ∀ y ∈ Bt, y ^ 3 = 1) (hBc : ∀ y ∈ Bt, ∀ z ∈ Bt, y * z = z * y)
    {d : Matrix.SpecialLinearGroup (Fin n) F} (hd : d ∈ Bt) :
    ∃ A Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) F), IsSimpleGroup A ∧
      (∃ u w : A, u * w ≠ w * u) ∧ 3 ∣ Nat.card A ∧ Y ≤ Bt ∧ d ∈ Y ∧ Y.relIndex Bt ≤ 3 ∧
      ∀ y ∈ Y, ∀ z ∈ A, y * z = z * y := by
  classical
  set T := Matrix.toLin' (d : Matrix (Fin n) (Fin n) F)
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h3 : ((3 : ℕ) : F) ≠ 0 := by
    rw [Nat.cast_ofNat, show (3 : F) = 2 + 1 by norm_num, h2, zero_add]; exact one_ne_zero
  have hT3 : T ^ 3 = 1 := by
    change ((slGL n F d : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hB3 d hd, map_one, Units.val_one]
  have hX3 : aeval T (X ^ 3 - C 1 : F[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hT3, sub_self]
  have hsq : Squarefree (minpoly F T) := squarefree_minpoly_of_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (1 : F) h3 one_ne_zero).squarefree hX3
  have hdeg : (minpoly F T).natDegree ≤ 3 :=
    (natDegree_le_of_dvd (minpoly.dvd F T hX3) (X_pow_sub_C_ne_zero (by norm_num) 1)).trans
      natDegree_X_pow_sub_C.le
  obtain ⟨a, ha, hm⟩ : ∃ a ∈ primaryFactors T, 2 ≤ primaryMultiplicity T a := by
    by_contra! hne
    have hsum := finrank_eq_sum_degree_mul_multiplicity hsq
    rw [Module.finrank_fin_fun] at hsum
    have hle : ∑ a : primaryFactors T, (a : F[X]).natDegree * primaryMultiplicity T a ≤
        ∑ a : primaryFactors T, (a : F[X]).natDegree :=
      Finset.sum_le_sum fun a _ => mul_le_of_le_one_right (Nat.zero_le _) (by
        have := hne a a.2; omega)
    rw [Finset.sum_coe_sort (primaryFactors T) fun a => a.natDegree,
      ← natDegree_prod _ _ fun a ha => (monic_of_mem_primaryFactors ha).ne_zero,
      prod_primaryFactors hsq] at hle
    omega
  obtain ⟨ω, hω⟩ : ∃ ω : F, IsPrimitiveRoot ω 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [Nat.card_units]; exact hF)
    exact ⟨u, IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)⟩
  haveI : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
  exact SG.exists_sl2_of_primaryBlock hB3 hBc hd hd ha hm
    (hω.map_of_injective (algebraMap F (AdjoinRoot a)).injective) (AdjoinRoot.root a)
    fun v => (coe_root_smul_primaryComponent T a v).symm

end CFSG.LocalAnalysis.GLTheoremA.S265

end
