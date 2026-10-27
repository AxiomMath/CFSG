module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusCentOrthMain
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.FixedFour
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Polynomial Module CFSG.AGLEmbedding.ToralCensus CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal

theorem _root_.CFSG.AGLEmbedding.ToralCensus.PerfectNoncycThreeIn.perfectThreeIn
    {G : Type*} [Group G] {C : Subgroup G} (h : PerfectNoncycThreeIn C) : PerfectThreeIn C := by
  obtain ⟨V, hVC, hV, Q, hQV, hQ, hnc⟩ := h
  have hne : ∃ g : Q, g ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hnc (@isCyclic_of_subsingleton _ _ ⟨fun a b => by rw [hall a, hall b]⟩)
  obtain ⟨g, hg⟩ := hne
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ) g
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hg hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  set y : Q := g ^ 3 ^ k with hy
  have hord : orderOf y = 3 := by
    rw [hy, orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (hn ▸ pow_dvd_pow 3 (by omega)), hn,
      pow_succ, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have h3 : y ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one y
  refine ⟨V, hVC, hV, (y : G), hQV y.2, by rw [← Subgroup.coe_pow, h3, Subgroup.coe_one],
    fun h1 => ?_⟩
  have : y = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hord
  omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem perfectThreeIn_isometryCentralizer_card_two (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) {r : ℕ} (hdim : finrank K V = 2 * r)
    (hmax : ∃ U : Submodule K V, finrank K U = r ∧ ∀ u ∈ U, Q u = 0) (hr : 4 ≤ r)
    (hres : ¬ (r = 4 ∧ (finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 2))) :
    PerfectThreeIn (isometryCentralizer Q x) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  by_cases h6 : 6 ≤ finrank K (fixedSpace x)
  · exact (perfectNoncycThreeIn_orthFixed hx h6).perfectThreeIn.mono
      (supportedBlock_le_isometryCentralizer _)
  obtain ⟨h, hh, hX, hrecX, hdeg, hdeg1, hsum⟩ := exists_orth_factor hx (by omega)
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨hirr, hmon, hdvd⟩ := orth_dvd_of_mem hx hh hX
  have hhq : h = X ^ 2 + X + 1 := eq_of_monic_of_associated hmon monic_X_sq_add_X_add_one
    (hirr.associated_of_dvd
      (CFSG.HardMathSupport.Curtis.Coordinator.irreducible_X_sq_add_X_add_one_of_card_eq_two hK)
      hdvd)
  have hself : h = reciprocalPolynomial h := by
    by_contra hne
    have := hdeg1 hne
    rw [hhq, natDegree_X_sq_add_X_add_one] at this
    omega
  by_cases hm4 : 4 ≤ primaryMultiplicity x.toLinearMap h
  · exact (perfectNoncycThreeIn_orthSelfDual hx hh hX hself hdeg (by omega)
      (by omega)).perfectThreeIn.mono (supportedBlock_le_isometryCentralizer _)
  · have h54 : r = 5 ∧ finrank K (fixedSpace x) = 4 := by omega
    exact perfectThreeIn_isometryCentralizer_fixedFour hK hx (by omega)
      (by rw [h54.1] at hmax; exact hmax) h54.2

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
