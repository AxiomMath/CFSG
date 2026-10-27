module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Symp
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Unitary
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpFamily

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar

section Cyc3

variable (K : Type) [Field K]

@[expose] noncomputable def cyc3' (K : Type) [Field K] : K[X] := X ^ 2 + X + 1

theorem natDegree_cyc3' : (cyc3' K).natDegree = 2 := by
  unfold cyc3'
  compute_degree!

theorem monic_cyc3' : (cyc3' K).Monic := by
  unfold cyc3'
  monicity!

variable {K} in
theorem irreducible_cyc3' (hK : Nat.card K = 2) : Irreducible (cyc3' K) := by
  have := charP_two_of_card hK
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_cyc3']
    decide
  · intro a ha
    rcases eq_zero_or_one_of_card hK a with rfl | rfl
    · simp [cyc3', IsRoot] at ha
    · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3 : (1 : K) ^ 2 + 1 + 1 = 1 := by
        rw [one_pow, add_assoc, ← two_mul, h2, zero_mul, add_zero]
      simp only [cyc3', IsRoot, eval_add, eval_pow, eval_X, eval_one] at ha
      rw [h3] at ha
      exact one_ne_zero ha

theorem cyc3'_ne_X_sub_one : cyc3' K ≠ X - 1 := fun h => by
  have := congrArg natDegree h
  rw [natDegree_cyc3', ← C_1, natDegree_X_sub_C] at this
  omega

theorem reciprocal_cyc3' : reciprocalPolynomial (cyc3' K) = cyc3' K := by
  have h0 : (cyc3' K).coeff 0 = 1 := by simp [cyc3']
  rw [reciprocalPolynomial, h0, inv_one, map_one, one_mul]
  ext n
  rw [coeff_reverse, natDegree_cyc3']
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | rfl | hn
  · rw [revAt_le (by norm_num)]
    simp [cyc3', coeff_X, coeff_one]
  · rw [revAt_le (by norm_num)]
  · rw [revAt_le (by norm_num)]
    simp [cyc3', coeff_X, coeff_one]
  · rw [revAt_eq_self_of_lt hn]

end Cyc3

section Factors

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_X_sub_one_or_cyc3' (hK : Nat.card K = 2) {x : StatedSp r K} (hx3 : x ^ 3 = 1)
    {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) : h = X - 1 ∨ h = cyc3' K := by
  have hdvd : h ∣ X ^ 3 - 1 := (mem_primaryFactors.mp hh).2.2.trans
    (minpoly.dvd K (spEnd x)
      (by rw [map_sub, map_pow, aeval_X, map_one, spEnd_pow hx3, sub_self]))
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * cyc3' K := by
    unfold cyc3'
    ring
  rw [hfac] at hdvd
  have hirr := irreducible_of_mem_primaryFactors hh
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · left
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh)
      CFSG.RankThree.Classical.monic_X_sub_one
      (hirr.associated_of_dvd CFSG.RankThree.Classical.irreducible_X_sub_one h1)
  · right
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (monic_cyc3' K)
      (hirr.associated_of_dvd (irreducible_cyc3' hK) h2)

theorem noNormalPPrime_spSupported_fixed (hK : Nat.card K = 2) (hr : 3 ≤ r) {x : StatedSp r K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) :
    NoNormalPPrime 3 (spSupported x ({X - 1} : Set K[X])) := by
  have blocks := spBlocks_three_two hK hr hx3 hx1
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  have h := noNormalPPrime_three_sesqUnitaryGroup_alt hK hB blocks.fixed_nondegenerate
  exact (noNormalPPrime_top_iff _).1 (noNormalPPrime_top_of_mulEquiv φ h)

theorem noNormalPPrime_spSupported_selfDual (hK : Nat.card K = 2) (hr : 3 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (a : primaryFactors (spEnd x))
    (ha : (a : K[X]) = cyc3' K) :
    NoNormalPPrime 3 (spSupported x ({(a : K[X])} : Set K[X])) := by
  have blocks := spBlocks_three_two hK hr hx3 hx1
  obtain ⟨d, hdeg, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
    (blocks.selfDual a (by rw [ha]; exact cyc3'_ne_X_sub_one K)
      (by rw [ha]; exact reciprocal_cyc3' K)).exists_half
  have hd : d = 1 := by
    have := natDegree_cyc3' (K := K)
    rw [ha] at hdeg
    omega
  subst hd
  have h := noNormalPPrime_three_sesqUnitaryGroup hE (f := 1 * 1) (by norm_num) hHf hHfl
  exact (noNormalPPrime_top_iff _).1 (noNormalPPrime_top_of_mulEquiv φ h)

theorem noNormalPPrime_spSupported_orbit (hK : Nat.card K = 2) (hr : 3 ≤ r) {x : StatedSp r K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (a : primaryFactors (spEnd x)) :
    NoNormalPPrime 3
      (spSupported x ({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X])) := by
  rcases eq_X_sub_one_or_cyc3' hK hx3 a.2 with h1 | h1
  · rw [h1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    exact noNormalPPrime_spSupported_fixed hK hr hx3 hx1 (h1 ▸ a.2)
  · rw [h1, reciprocal_cyc3', Set.pair_eq_singleton]
    exact h1 ▸ noNormalPPrime_spSupported_selfDual hK hr hx3 hx1 a h1

theorem noNormalPPrime_three_centralizer_statedSp (hK : Nat.card K = 2) (hr : 3 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    NoNormalPPrime 3 (Subgroup.centralizer ({x} : Set (StatedSp r K))) := by
  classical
  have blocks := spBlocks_three_two hK hr hx3 hx1
  obtain ⟨hcomm, hind, hsup⟩ := blocks.directProduct
  haveI : Finite (reciprocalOrbits (spEnd x)) := ((Finset.finite_toSet _).image _).to_subtype
  rw [← hsup]
  refine noNormalPPrime_iSup (fun i j hij a b ha hb => ?_) hind (fun i => ?_)
  · exact hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  · obtain ⟨O, hO⟩ := i
    obtain ⟨h, hh, rfl⟩ := hO
    exact noNormalPPrime_spSupported_orbit hK hr hx3 hx1 ⟨h, hh⟩

end Factors

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
