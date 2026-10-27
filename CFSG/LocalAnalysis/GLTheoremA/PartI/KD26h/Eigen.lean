module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

open scoped Classical in
theorem exists_primaryMultiplicity_ge_two {F : Type} [Field F] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {M : Matrix (Fin p) (Fin p) F} {c : F}
    (hM : M ^ p = Matrix.scalar (Fin p) c) (hdet : M.det = 1) (hc : c ≠ 1)
    (hx : Squarefree (minpoly F (Matrix.toLin' M))) :
    ∃ a : primaryFactors (Matrix.toLin' M),
      2 ≤ primaryMultiplicity (Matrix.toLin' M) (a : F[X]) := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ a : primaryFactors (Matrix.toLin' M),
      primaryMultiplicity (Matrix.toLin' M) (a : F[X]) ≤ 1 := fun a => Nat.lt_succ_iff.mp (hcon a)
  set x := Matrix.toLin' M with hxdef
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  rw [Module.finrank_fin_fun] at hsum
  have h1 : p ≤ ∑ a : primaryFactors x, (a : F[X]).natDegree := by
    refine hsum.le.trans (Finset.sum_le_sum fun a _ => ?_)
    have := hle a
    nlinarith
  have hprod := prod_primaryFactors hx
  have hne : ∀ a ∈ primaryFactors x, a ≠ 0 := fun a ha =>
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor a
      (Multiset.mem_toFinset.1 ha)).ne_zero
  have hdeg : (minpoly F x).natDegree = ∑ a ∈ primaryFactors x, a.natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ hne]
  have h2 : ∑ a : primaryFactors x, (a : F[X]).natDegree = ∑ a ∈ primaryFactors x, a.natDegree :=
    Finset.sum_coe_sort (primaryFactors x) fun a => a.natDegree
  have hmp : p ≤ (minpoly F x).natDegree := by
    rw [hdeg, ← h2]
    exact h1
  have hmonic : (minpoly F x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hX : aeval x (X ^ p - C c) = 0 := by
    have hx' : x = Matrix.toLinAlgEquiv' M :=
      (CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin' M).symm
    rw [hx']
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [← map_pow, hM]
    rw [show (algebraMap F (Module.End F (Fin p → F)) c) =
      Matrix.toLinAlgEquiv' (Matrix.scalar (Fin p) c) from by
        rw [← AlgEquiv.commutes Matrix.toLinAlgEquiv' c]; rfl]
    exact sub_self _
  have hdvd2 : minpoly F x ∣ (X ^ p - C c : F[X]) := minpoly.dvd F x hX
  have hmin : X ^ p - C c = minpoly F x :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic (monic_X_pow_sub_C c hp.ne_zero) hdvd2
      (by rw [natDegree_X_pow_sub_C]; exact hmp)
  have hdvd1 : minpoly F x ∣ x.charpoly := LinearMap.minpoly_dvd_charpoly x
  have hcp : x.charpoly = X ^ p - C c := by
    have hc2 : x.charpoly = minpoly F x :=
      Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic (LinearMap.charpoly_monic x) hdvd1
        (by rw [LinearMap.charpoly_natDegree, Module.finrank_fin_fun]; exact hmp)
    exact hc2.trans hmin.symm
  have hcpM : M.charpoly = X ^ p - C c := by
    rw [← Matrix.charpoly_toLin' M]
    exact hcp
  have hdetc := Matrix.det_eq_sign_charpoly_coeff M
  rw [hcpM, Fintype.card_fin, hdet] at hdetc
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hc0 : (X ^ p - C c : F[X]).coeff 0 = -c := by
    rw [coeff_sub, coeff_X_pow, coeff_C_zero, if_neg hp.ne_zero.symm]
    ring
  rw [hc0, hodd.neg_one_pow] at hdetc
  apply hc
  linear_combination -hdetc

end CFSG.LocalAnalysis.GLTheoremA
