module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.LargeExtraspecial.O62SL4

public section

namespace CFSG.LinearAlgebra.F2OrderNineFixed

open Polynomial Module
open CFSG.RankThree.PartOne.KCPrimary

theorem isCoprime_cyclotomic_nine_X_pow_three_sub_one :
    IsCoprime (cyclotomic 9 (ZMod 2)) (X ^ 3 - 1 : (ZMod 2)[X]) := by
  refine CFSG.LargeExtraspecial.O62.irreducible_cyclotomic_nine.coprime_iff_not_dvd.mpr ?_
  rintro ⟨q, hq⟩
  have hdeg : (X ^ 3 - 1 : (ZMod 2)[X]).natDegree = 3 := by
    simpa using (natDegree_X_pow_sub_C (n := 3) (r := (1 : ZMod 2)))
  have h0 : (X ^ 3 - 1 : (ZMod 2)[X]) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    omega
  have hle := natDegree_le_of_dvd ⟨q, hq⟩ h0
  rw [hdeg] at hle
  rw [natDegree_cyclotomic, show Nat.totient 9 = 6 by decide] at hle
  omega

theorem finrank_ker_cube_sub_one_eq_two
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 8) (y : Module.End (ZMod 2) V)
    (hy9 : y ^ 9 = 1) (hy3 : y ^ 3 ≠ 1) :
    Module.finrank (ZMod 2) (LinearMap.ker (y ^ 3 - 1)) = 2 := by
  let Φ : (ZMod 2)[X] := cyclotomic 9 (ZMod 2)
  let U : Submodule (ZMod 2) V := LinearMap.ker (aeval y Φ)
  let W : Submodule (ZMod 2) V := LinearMap.ker (aeval y (X ^ 3 - 1 : (ZMod 2)[X]))
  have hΦmul : Φ * (X ^ 3 - 1 : (ZMod 2)[X]) = X ^ 9 - 1 := by
    dsimp only [Φ]
    have := cyclotomic_prime_pow_mul_X_pow_sub_one (ZMod 2) 3 1
    norm_num at this
    exact this
  have hΦdvd : Φ ∣ minpoly (ZMod 2) y := by
    by_contra hΦ
    have hcop : IsCoprime Φ (minpoly (ZMod 2) y) :=
      (CFSG.LargeExtraspecial.O62.irreducible_cyclotomic_nine.coprime_iff_not_dvd).mpr hΦ
    have hann : aeval y (X ^ 9 - 1 : (ZMod 2)[X]) = 0 := by
      have h : aeval y (X ^ 9 - 1 : (ZMod 2)[X]) = y ^ 9 - 1 := by simp
      rw [h, hy9, sub_self]
    have hμ9 : minpoly (ZMod 2) y ∣ Φ * (X ^ 3 - 1 : (ZMod 2)[X]) := by
      rw [hΦmul]
      exact minpoly.dvd (ZMod 2) y hann
    have hμ3 : minpoly (ZMod 2) y ∣ (X ^ 3 - 1 : (ZMod 2)[X]) :=
      hcop.symm.dvd_of_dvd_mul_left hμ9
    obtain ⟨r, hr⟩ := hμ3
    have hzero : aeval y (X ^ 3 - 1 : (ZMod 2)[X]) = 0 := by
      rw [hr, map_mul, minpoly.aeval, zero_mul]
    have : y ^ 3 - 1 = 0 := by simpa using hzero
    exact hy3 (sub_eq_zero.mp this)
  have hcopΦ : IsCoprime Φ (X ^ 3 - 1 : (ZMod 2)[X]) := by
    simpa only [Φ] using isCoprime_cyclotomic_nine_X_pow_three_sub_one
  have hsup : U ⊔ W = ⊤ := by
    change LinearMap.ker (aeval y Φ) ⊔ LinearMap.ker (aeval y (X ^ 3 - 1 : (ZMod 2)[X])) = ⊤
    rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime y hcopΦ, hΦmul]
    simp [hy9]
  have hdisj : Disjoint U W := by
    change Disjoint (LinearMap.ker (aeval y Φ)) (LinearMap.ker (aeval y (X ^ 3 - 1 : (ZMod 2)[X])))
    exact disjoint_ker_aeval_of_isCoprime y hcopΦ
  have hcompl : IsCompl U W := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  have hW_ne_top : W ≠ ⊤ := by
    intro hWtop
    have hzero : aeval y (X ^ 3 - 1 : (ZMod 2)[X]) = 0 := by
      rw [← LinearMap.ker_eq_top]
      exact hWtop
    have : y ^ 3 - 1 = 0 := by simpa using hzero
    exact hy3 (sub_eq_zero.mp this)
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    apply hW_ne_top
    rw [hU, bot_sup_eq] at hsup
    exact hsup
  have : Fact (Irreducible Φ) := ⟨by
    dsimp only [Φ]
    exact CFSG.LargeExtraspecial.O62.irreducible_cyclotomic_nine⟩
  have hdimU : Module.finrank (ZMod 2) (primaryComponent y Φ) =
      Φ.natDegree * Module.finrank (AdjoinRoot Φ) (primaryComponent y Φ) :=
    finrank_primaryComponent y Φ
  have hΦdeg : Φ.natDegree = 6 := by
    dsimp only [Φ]
    rw [natDegree_cyclotomic]
    decide
  have hdvd : 6 ∣ Module.finrank (ZMod 2) U := by
    change 6 ∣ Module.finrank (ZMod 2) (primaryComponent y Φ)
    rw [hdimU, hΦdeg]
    exact dvd_mul_right _ _
  have hU_pos : 0 < Module.finrank (ZMod 2) U := by
    have h1 : 1 ≤ Module.finrank (ZMod 2) U := Submodule.one_le_finrank_iff.mpr hU_ne_bot
    omega
  have hU_le : Module.finrank (ZMod 2) U ≤ 8 := by
    have := Submodule.finrank_le (R := ZMod 2) (M := V) U
    omega
  obtain ⟨k, hk⟩ := hdvd
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, mul_zero] at hk
      omega
    · exact hpos
  have hk_le : k ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ k := by omega
    have h3 : 12 ≤ 6 * k := Nat.mul_le_mul_left 6 h2
    omega
  have hU6 : Module.finrank (ZMod 2) U = 6 := by
    rw [hk, show k = 1 by omega, mul_one]
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hW2 : Module.finrank (ZMod 2) W = 2 := by
    rw [hV, hU6] at hsum
    omega
  have hW_eq : W = LinearMap.ker (y ^ 3 - 1) := by
    change LinearMap.ker (aeval y (X ^ 3 - 1 : (ZMod 2)[X])) = LinearMap.ker (y ^ 3 - 1)
    congr 1
    simp
  rw [hW_eq] at hW2
  exact hW2

end CFSG.LinearAlgebra.F2OrderNineFixed
