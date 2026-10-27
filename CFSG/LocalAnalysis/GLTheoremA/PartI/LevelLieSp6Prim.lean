module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

open Polynomial CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

variable {K : Type} [Field K]

theorem charP_two_of_card_two [Finite K] (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hk' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime hk'

theorem two_eq_zero_of_card_two [Finite K] (hK : Nat.card K = 2) : (2 : K) = 0 := by
  haveI := charP_two_of_card_two hK
  exact CharP.cast_eq_zero K 2

theorem eq_zero_or_one_of_card_two [Finite K] (hK : Nat.card K = 2) (a : K) : a = 0 ∨ a = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hk' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  have hs : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [hk', Finset.card_pair h01]
  have hu := Finset.eq_univ_of_card _ hs
  have ha : a ∈ ({0, 1} : Finset K) := by rw [hu]; exact Finset.mem_univ a
  simpa using ha

noncomputable abbrev X2K : K[X] := X ^ 2 + X + 1

theorem X2K_monic : (X2K : K[X]).Monic := by unfold X2K; monicity!

theorem X2K_irreducible [Finite K] (hK : Nat.card K = 2) : Irreducible (X2K : K[X]) := by
  have hm : (X2K : K[X]).Monic := X2K_monic
  have hd : (X2K : K[X]).natDegree = 2 := by unfold X2K; compute_degree!
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
  refine Multiset.eq_zero_of_forall_notMem fun a ha => ?_
  rw [mem_roots (by unfold X2K; exact hm.ne_zero), IsRoot, eval_add, eval_add, eval_pow, eval_X,
    eval_one] at ha
  have h2 := two_eq_zero_of_card_two (K := K) hK
  rcases eq_zero_or_one_of_card_two hK a with rfl | rfl
  · simp at ha
  · have h1 : (1 : K) = 0 := by linear_combination ha - h2
    exact one_ne_zero h1

theorem X_sub_one_irreducible : Irreducible (X - 1 : K[X]) :=
  irreducible_of_degree_eq_one (by compute_degree!)

theorem X_cube_sub_one_K : (X ^ 3 - 1 : K[X]) = (X - 1) * X2K := by
  unfold X2K; ring

theorem reciprocal_X_sub_one [Finite K] (hK : Nat.card K = 2) :
    reciprocalPolynomial (X - 1 : K[X]) = X - 1 := by
  have h2 : (-1 : K) = 1 := by
    haveI := charP_two_of_card_two hK
    exact (neg_one_eq_one_iff).2 (ringChar.eq K 2)
  unfold reciprocalPolynomial
  have hd : (X - 1 : K[X]).natDegree = 1 := by compute_degree!
  have hc0 : (X - 1 : K[X]).coeff 0 = 1 := by simp [h2]
  rw [hc0, inv_one, C_1, one_mul]
  ext n
  rw [coeff_reverse, hd]
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h2'
  · simp [revAt_le, coeff_X, coeff_one, coeff_sub, h2]
  · simp [revAt_le, coeff_X, coeff_one, coeff_sub, Nat.sub_zero, h2]
  · rw [revAt_eq_self_of_lt (by omega)] <;>
    simp [coeff_X, coeff_one, coeff_sub, h2, show n ≠ 0 by omega, show n ≠ 1 by omega]

theorem reciprocal_X2K : reciprocalPolynomial (X2K : K[X]) = X2K := by
  have hd : (X2K : K[X]).natDegree = 2 := by unfold X2K; compute_degree!
  have hc0 : (X2K : K[X]).coeff 0 = 1 := by unfold X2K; simp [coeff_X, coeff_one]
  unfold reciprocalPolynomial
  rw [hc0, inv_one, C_1, one_mul]
  ext n
  rw [coeff_reverse, hd]
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | rfl | h3
  · simp [revAt_le, X2K, coeff_X, coeff_one, coeff_X_pow]
  · simp [revAt_le, X2K, coeff_X, coeff_one, coeff_X_pow]
  · simp [revAt_le, X2K, coeff_X, coeff_one, coeff_X_pow]
  · rw [revAt_eq_self_of_lt (by omega)] <;>
    simp [X2K, coeff_X, coeff_one, coeff_X_pow, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega]

theorem primaryFactor_cases [Finite K] (hK : Nat.card K = 2) (x : StatedSp 3 K)
    (hx : x ^ 3 = 1) {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) :
    h = X - 1 ∨ h = X2K := by
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.1 hh
  have hann : aeval (spEnd x) (X ^ 3 - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    exact spEnd_pow hx
  have hmin : minpoly K (spEnd x) ∣ X ^ 3 - 1 := minpoly.dvd _ _ hann
  have hdiv : h ∣ (X - 1) * X2K := by
    rw [← X_cube_sub_one_K]
    exact hdvd.trans hmin
  have hprime : Prime h := hirr.prime
  rcases hprime.dvd_or_dvd hdiv with h1 | h2
  · left
    have hass := hirr.associated_of_dvd X_sub_one_irreducible h1
    have hm1 : (X - 1 : K[X]).Monic := by simpa using monic_X_sub_C (1 : K)
    exact eq_of_monic_of_associated hmon hm1 hass
  · right
    have hass := hirr.associated_of_dvd (X2K_irreducible hK) h2
    exact eq_of_monic_of_associated hmon X2K_monic hass

theorem reciprocal_of_primaryFactor [Finite K] (hK : Nat.card K = 2) (x : StatedSp 3 K)
    (hx : x ^ 3 = 1) {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) :
    reciprocalPolynomial h = h := by
  rcases primaryFactor_cases hK x hx hh with rfl | rfl
  · exact reciprocal_X_sub_one hK
  · exact reciprocal_X2K

theorem reciprocalOrbit_singleton [Finite K] (hK : Nat.card K = 2) (x : StatedSp 3 K)
    (hx : x ^ 3 = 1) {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) :
    ({h, reciprocalPolynomial h} : Set K[X]) = {h} := by
  rw [reciprocal_of_primaryFactor hK x hx hh, Set.pair_eq_singleton]

theorem finrank_sixDim [Finite K] (hK : Nat.card K = 2) :
    Module.finrank K (Fin 3 ⊕ Fin 3 → K) = 6 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]

theorem eq_one_of_fixed_finrank_six [Finite K] (hK : Nat.card K = 2) (x : StatedSp 3 K)
    (h : Module.finrank K (primaryComponent (spEnd x) (X - 1 : K[X])) = 6) : x = 1 := by
  have htop : primaryComponent (spEnd x) (X - 1 : K[X]) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [h, finrank_sixDim hK])
  have hid : spEnd x = 1 := by
    apply LinearMap.ext
    intro v
    have hv : v ∈ primaryComponent (spEnd x) (X - 1 : K[X]) := by rw [htop]; trivial
    rw [mem_primaryComponent] at hv
    simp only [map_sub, aeval_X, aeval_one, LinearMap.sub_apply, Module.End.one_apply,
      sub_eq_zero] at hv
    exact hv
  apply spLin_injective
  rw [map_one]
  exact Units.ext (by simpa using hid)

end CFSG.LocalAnalysis.GLTheoremA.LevelLieSp6

end
