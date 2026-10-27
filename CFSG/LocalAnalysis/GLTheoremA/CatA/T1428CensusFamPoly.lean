module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.OrthL2.Struct

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private theorem dvd_X_pow_three_sub_one_of_mem_primaryFactors {y : Module.End K V} (hy : y ^ 3 = 1)
    {h : K[X]} (hh : h ∈ primaryFactors y) : h ∣ (X ^ 3 - 1 : K[X]) := by
  have hroot : aeval y (X ^ 3 - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, hy, sub_self]
  exact (mem_primaryFactors.mp hh).2.2.trans (minpoly.dvd K y hroot)

private theorem dvd_cyclotomic_three_of_pow_three {y : Module.End K V} (hy : y ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors y) (hne1 : h ≠ X - 1) : h ∣ (X ^ 2 + X + 1 : K[X]) := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have hdvd := dvd_X_pow_three_sub_one_of_mem_primaryFactors hy hh
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * (X ^ 2 + X + 1) := by ring
  rw [hfac] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · exact absurd (eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one h1)) hne1
  · exact h2

private theorem eq_or_eq_reciprocal_of_pow_three {y : Module.End K V} (hy : y ^ 3 = 1) {a b : K[X]}
    (ha : a ∈ primaryFactors y) (hb : b ∈ primaryFactors y) (ha1 : a ≠ X - 1)
    (hb1 : b ≠ X - 1) : b = a ∨ b = reciprocalPolynomial a := by
  by_cases hba : b = a
  · exact Or.inl hba
  right
  have hairr := irreducible_of_mem_primaryFactors ha
  have hbirr := irreducible_of_mem_primaryFactors hb
  have hamon := monic_of_mem_primaryFactors ha
  have hbmon := monic_of_mem_primaryFactors hb
  have haΦ := dvd_cyclotomic_three_of_pow_three hy ha ha1
  have hbΦ := dvd_cyclotomic_three_of_pow_three hy hb hb1
  have hΦdeg : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hΦmon : (X ^ 2 + X + 1 : K[X]).Monic := by monicity!
  have hcop : IsCoprime a b := isCoprime_of_mem_primaryFactors ha hb (Ne.symm hba)
  have habΦ : a * b ∣ (X ^ 2 + X + 1 : K[X]) := hcop.mul_dvd haΦ hbΦ
  have hapos : 0 < a.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hairr)
  have hbpos : 0 < b.natDegree :=
    natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hbirr)
  have hmul : (a * b).natDegree = a.natDegree + b.natDegree := Monic.natDegree_mul hamon hbmon
  have hle : (a * b).natDegree ≤ 2 := by
    have := natDegree_le_of_dvd habΦ hΦmon.ne_zero
    omega
  have hda : a.natDegree = 1 := by omega
  have hdb : b.natDegree = 1 := by omega
  have hab : a * b = X ^ 2 + X + 1 :=
    eq_of_monic_of_dvd_of_natDegree_le (hamon.mul hbmon) hΦmon habΦ (by omega) |>.symm
  have hform_a : a = X + C (a.coeff 0) := hamon.eq_X_add_C hda
  have hform_b : b = X + C (b.coeff 0) := hbmon.eq_X_add_C hdb
  have h00 : a.coeff 0 * b.coeff 0 = 1 := by
    have := congrArg (fun p : K[X] => p.coeff 0) hab
    simpa [mul_coeff_zero] using this
  have ha0 : a.coeff 0 ≠ 0 := fun h => by simp [h] at h00
  have hb0 : b.coeff 0 = (a.coeff 0)⁻¹ := eq_inv_of_mul_eq_one_right h00
  conv_rhs => rw [hform_a, CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2.reciprocalPolynomial_X_add_C ha0]
  rw [hform_b, hb0]

private theorem coeff_zero_ne_zero_of_pow_three {y : Module.End K V} (hy : y ^ 3 = 1) {h : K[X]}
    (hh : h ∈ primaryFactors y) : h.coeff 0 ≠ 0 := by
  intro h0
  have hd := dvd_X_pow_three_sub_one_of_mem_primaryFactors hy hh
  have := Polynomial.eval_dvd (x := (0 : K)) hd
  rw [← Polynomial.coeff_zero_eq_eval_zero, h0, zero_dvd_iff] at this
  simp at this

private theorem reciprocalPolynomial_reciprocalPolynomial_of_pow_three {y : Module.End K V}
    (hy : y ^ 3 = 1) {h : K[X]} (hh : h ∈ primaryFactors y) :
    reciprocalPolynomial (reciprocalPolynomial h) = h :=
  reciprocalPolynomial_reciprocalPolynomial (monic_of_mem_primaryFactors hh)
    (coeff_zero_ne_zero_of_pow_three hy hh)

private theorem reciprocalOrbit_eq_of_pow_three {y : Module.End K V} (hy : y ^ 3 = 1) {a b : K[X]}
    (ha : a ∈ primaryFactors y) (hb : b ∈ primaryFactors y) (ha1 : a ≠ X - 1)
    (hb1 : b ≠ X - 1) :
    ({b, reciprocalPolynomial b} : Set K[X]) = {a, reciprocalPolynomial a} := by
  rcases eq_or_eq_reciprocal_of_pow_three hy ha hb ha1 hb1 with rfl | rfl
  · rfl
  · rw [reciprocalPolynomial_reciprocalPolynomial_of_pow_three hy ha, Set.pair_comm]

theorem exists_eq_of_three_reciprocalOrbits {y : Module.End K V} (hy : y ^ 3 = 1)
    {O₁ O₂ O₃ : Set K[X]}
    (h₁ : ∃ h ∈ primaryFactors y, ({h, reciprocalPolynomial h} : Set K[X]) = O₁)
    (h₂ : ∃ h ∈ primaryFactors y, ({h, reciprocalPolynomial h} : Set K[X]) = O₂)
    (h₃ : ∃ h ∈ primaryFactors y, ({h, reciprocalPolynomial h} : Set K[X]) = O₃) :
    O₁ = O₂ ∨ O₁ = O₃ ∨ O₂ = O₃ := by
  obtain ⟨a, ha, rfl⟩ := h₁
  obtain ⟨b, hb, rfl⟩ := h₂
  obtain ⟨c, hc, rfl⟩ := h₃
  by_cases ha1 : a = X - 1
  · by_cases hb1 : b = X - 1
    · left
      subst ha1
      subst hb1
      rfl
    · by_cases hc1 : c = X - 1
      · right
        left
        subst ha1
        subst hc1
        rfl
      · right
        right
        exact reciprocalOrbit_eq_of_pow_three hy hc hb hc1 hb1
  · by_cases hb1 : b = X - 1
    · by_cases hc1 : c = X - 1
      · right
        right
        subst hb1
        subst hc1
        rfl
      · right
        left
        exact reciprocalOrbit_eq_of_pow_three hy hc ha hc1 ha1
    · left
      exact reciprocalOrbit_eq_of_pow_three hy hb ha hb1 ha1

end CFSG.LocalAnalysis.GLTheoremA.T1428
