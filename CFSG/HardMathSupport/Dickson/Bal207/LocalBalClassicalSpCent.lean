module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.SpTwoAux.Centralizer
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

section Cyc3

variable {K : Type} [Field K] [Finite K]

theorem irreducible_cyc3_eight (hK : Nat.card K = 8) : Irreducible (W2.cyc3' K) := by
  have h2K : CharP K 2 := charP_two_of_card_eight hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 8 := by rw [← Nat.card_eq_fintype_card, hK]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [W2.natDegree_cyc3']
    decide
  · intro a ha
    simp only [W2.cyc3', IsRoot, eval_add, eval_pow, eval_X, eval_one] at ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    have h3 : a ^ 3 = 1 := by
      have : a ^ 3 - 1 = (a - 1) * (a ^ 2 + a + 1) := by ring
      rw [ha, mul_zero] at this
      exact sub_eq_zero.1 this
    have h7 : a ^ 7 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one a ha0
      rwa [hcard] at this
    have ha1 : a = 1 := by
      calc a = a * (a ^ 3) ^ 2 := by rw [h3]; ring
        _ = a ^ 7 := by ring
        _ = 1 := h7
    subst ha1
    exact one_ne_zero (by linear_combination ha - h2)

end Cyc3

section Factors

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem eq_X_sub_one_or_cyc3_eight (hK : Nat.card K = 8) {x : StatedSp r K} (hx3 : x ^ 3 = 1)
    {h : K[X]} (hh : h ∈ primaryFactors (spEnd x)) : h = X - 1 ∨ h = W2.cyc3' K := by
  have hdvd : h ∣ X ^ 3 - 1 := (mem_primaryFactors.mp hh).2.2.trans
    (minpoly.dvd K (spEnd x)
      (by rw [map_sub, map_pow, aeval_X, map_one, spEnd_pow hx3, sub_self]))
  have hfac : (X ^ 3 - 1 : K[X]) = (X - 1) * W2.cyc3' K := by
    unfold W2.cyc3'
    ring
  rw [hfac] at hdvd
  have hirr := irreducible_of_mem_primaryFactors hh
  rcases hirr.prime.dvd_or_dvd hdvd with h1 | h2
  · left
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh)
      CFSG.RankThree.Classical.monic_X_sub_one
      (hirr.associated_of_dvd CFSG.RankThree.Classical.irreducible_X_sub_one h1)
  · right
    exact eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (W2.monic_cyc3' K)
      (hirr.associated_of_dvd (irreducible_cyc3_eight hK) h2)

theorem spBlocks_three_eight (hK : Nat.card K = 8) (hr : 1 ≤ r) {x : StatedSp r K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) : SpPrimaryBlocks 2 3 3 x (proj r K x) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  have hℓ : Nat.Prime 2 := Nat.prime_two
  have ha1 : proj r K x ≠ 1 := fun h =>
    hx1 (KCSymplectic.eq_one_of_proj_eq_one_of_pow_eq_one hr (by omega) hp h hx3)
  have ha : orderOf (proj r K x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx3, map_one]) ha1
  have hxp : orderOf x = 3 := have : Fact (Nat.Prime 3) := ⟨hp⟩; orderOf_eq_prime hx3 hx1
  exact (symplectic_cross_prime_primary_centralizer_blocks hℓ (by omega) hK' hp (by omega)
    (by omega) hr (proj r K x) ha).2 x rfl hxp

theorem noNormalPPrime_spSupported_fixed_eight (hK : Nat.card K = 8) (hr : 1 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hmem : (X - 1 : K[X]) ∈ primaryFactors (spEnd x)) :
    NoNormalPPrime 3 (spSupported x ({X - 1} : Set K[X])) := by
  have blocks := spBlocks_three_eight hK hr hx3 hx1
  obtain ⟨φ, -⟩ := blocks.fixedFactor hmem
  have hB : ((spForm r K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
    fun v => spForm_isAlt (v : Fin r ⊕ Fin r → K)
  have h := noNormalPPrime_three_sesqUnitaryGroup_alt_eight hK hB blocks.fixed_nondegenerate
  exact (W2.noNormalPPrime_top_iff _).1 (W2.noNormalPPrime_top_of_mulEquiv φ h)

theorem noNormalPPrime_spSupported_selfDual_eight (hK : Nat.card K = 8) (hr : 1 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (a : primaryFactors (spEnd x))
    (ha : (a : K[X]) = W2.cyc3' K) :
    NoNormalPPrime 3 (spSupported x ({(a : K[X])} : Set K[X])) := by
  have blocks := spBlocks_three_eight hK hr hx3 hx1
  obtain ⟨d, hdeg, -, σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
    (blocks.selfDual a (by rw [ha]; exact W2.cyc3'_ne_X_sub_one K)
      (by rw [ha]; exact W2.reciprocal_cyc3' K)).exists_half
  have hd : d = 1 := by
    have := W2.natDegree_cyc3' (K := K)
    rw [ha] at hdeg
    omega
  subst hd
  have h := noNormalPPrime_three_sesqUnitaryGroup_eight hE (f := 3 * 1) (by norm_num) hHf hHfl
  exact (W2.noNormalPPrime_top_iff _).1 (W2.noNormalPPrime_top_of_mulEquiv φ h)

theorem noNormalPPrime_spSupported_orbit_eight (hK : Nat.card K = 8) (hr : 1 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (a : primaryFactors (spEnd x)) :
    NoNormalPPrime 3
      (spSupported x ({(a : K[X]), reciprocalPolynomial (a : K[X])} : Set K[X])) := by
  rcases eq_X_sub_one_or_cyc3_eight hK hx3 a.2 with h1 | h1
  · rw [h1, CFSG.RankThree.Classical.reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
    exact noNormalPPrime_spSupported_fixed_eight hK hr hx3 hx1 (h1 ▸ a.2)
  · rw [h1, W2.reciprocal_cyc3', Set.pair_eq_singleton]
    exact h1 ▸ noNormalPPrime_spSupported_selfDual_eight hK hr hx3 hx1 a h1

theorem noNormalPPrime_three_centralizer_statedSp_eight (hK : Nat.card K = 8) (hr : 1 ≤ r)
    {x : StatedSp r K} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    NoNormalPPrime 3 (Subgroup.centralizer ({x} : Set (StatedSp r K))) := by
  classical
  have blocks := spBlocks_three_eight hK hr hx3 hx1
  obtain ⟨hcomm, hind, hsup⟩ := blocks.directProduct
  haveI : Finite (reciprocalOrbits (spEnd x)) := ((Finset.finite_toSet _).image _).to_subtype
  rw [← hsup]
  refine W2.noNormalPPrime_iSup (fun i j hij a b ha hb => ?_) hind (fun i => ?_)
  · exact hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  · obtain ⟨O, hO⟩ := i
    obtain ⟨h, hh, rfl⟩ := hO
    exact noNormalPPrime_spSupported_orbit_eight hK hr hx3 hx1 ⟨h, hh⟩

theorem proj_injective_of_charP_two [CharP K 2] (r : ℕ) : Function.Injective (proj r K) := by
  have hker : (proj r K).ker = ⊥ :=
    eq_bot_iff.2 ((CFSG.RankThree.PartOne.KCSpFull.ker_proj_le_center).trans
      (center_statedSp_eq_bot_of_charP_two r).le)
  exact (MonoidHom.ker_eq_bot_iff _).1 hker

theorem proj_injective_eight (hK : Nat.card K = 8) (r : ℕ) : Function.Injective (proj r K) :=
  have : CharP K 2 := charP_two_of_card_eight hK
  proj_injective_of_charP_two r

theorem noNormalPPrime_three_centralizer_statedProj_eight (hK : Nat.card K = 8) (hr : 1 ≤ r)
    {t : StatedProj (StatedSp r K)} (ht : orderOf t = 3) :
    NoNormalPPrime 3 (Subgroup.centralizer ({t} : Set (StatedProj (StatedSp r K)))) := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  obtain ⟨⟨x, ⟨hxa, hxp⟩, -⟩, hblocks⟩ :=
    symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two (by omega) hK'
      Nat.prime_three (by omega) (by omega) hr t ht
  have hx3 : x ^ 3 = 1 := by rw [← hxp]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hxp
    omega
  have blocks := hblocks x hxa hxp
  rw [blocks.centralizer_eq, W2.noNormalPPrime_map_iff _ (proj_injective_eight hK r)]
  exact noNormalPPrime_three_centralizer_statedSp_eight hK hr hx3 hx1

end Factors

end CFSG.HardMathSupport.Dickson.Bal207

end
