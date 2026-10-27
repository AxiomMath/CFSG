module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.Centralizer
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.AGLEmbedding.ToralCensus
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem not_exists_totallySingular_fixed_minus (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) [Fintype V] {r m : ℕ}
    (hS : ∑ v : V, chi (Q v) = -(2 : ℤ) ^ r)
    (hfix : finrank K (fixedSpace x) + 2 * m = 2 * r) (hm : Even m) :
    ¬ ∃ W : Submodule K V, W ≤ fixedSpace x ∧ finrank K W = r - m ∧ ∀ w ∈ W, Q w = 0 := by
  classical
  rintro ⟨W, hWle, hWdim, hWQ⟩
  set V₁ := fixedSpace x with hV₁
  let Q₁ : QuadraticForm K V₁ := Q.comp V₁.subtype
  have hB₁ : (polarBilin Q₁).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have : Finite V₁ := Module.finite_of_finite K
  have : Fintype V₁ := Fintype.ofFinite V₁
  let W' : Submodule K V₁ := W.comap V₁.subtype
  have hW'dim : finrank K W' = r - m := by
    rw [← hWdim]
    exact (Submodule.comapSubtypeEquivOfLe hWle).finrank_eq
  have hS₁ : ∑ v : V₁, chi (Q₁ v) = 2 ^ (r - m) := by
    rw [charSum_eq_of_totallySingular hK hB₁ (U := W') (fun w hw => hWQ w hw) (by omega),
      Module.natCard_eq_pow_finrank (K := K), hK, hW'dim]
    norm_cast
  have hmod := charSum_modEq_fixed Q x (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    hx.mem v) hx.pow_eq_one
  have hsub : ∑ v ∈ Finset.univ.filter (fun v => x v = v), chi (Q v) = ∑ v : V₁, chi (Q₁ v) :=
    Finset.sum_subtype (p := (· ∈ V₁)) _ (fun v => by simp [hV₁, mem_fixedSpace]) _
  rw [hS, hsub, hS₁] at hmod
  have hz := (ZMod.intCast_eq_intCast_iff _ _ 3).mpr hmod
  obtain ⟨k, hk⟩ := hm
  have hrm : r = (r - m) + (k + k) := by omega
  generalize r - m = a at hrm hz
  subst hrm
  push_cast at hz
  have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
  have h2k : (2 : ZMod 3) ^ (k + k) = 1 := by
    rw [← two_mul, pow_mul, h4, one_pow]
  rw [pow_add, h2k, mul_one] at hz
  have h2a : (2 : ZMod 3) ^ a ≠ 0 := pow_ne_zero _ (by decide)
  have hne : ∀ y : ZMod 3, y ≠ 0 → -y ≠ y := by decide
  exact hne _ h2a hz

theorem perfectThreeIn_isometryCentralizer_minus (hK : Nat.card K = 2)
    (hx : OddOrderIsometry Q 3 x) [Fintype V] {r : ℕ} (hdim : finrank K V = 2 * r)
    (hr : r = 4 ∨ r = 5) (hS : ∑ v : V, chi (Q v) = -(2 : ℤ) ^ r) (hx1 : x ≠ 1)
    (hd : finrank K (fixedSpace x) ≠ 2 * r - 6) :
    PerfectThreeIn (isometryCentralizer Q x) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V))
    fun g h hgh => LinearEquiv.ext (congrFun hgh)
  have hlt : finrank K (fixedSpace x) < finrank K V := by
    apply Submodule.finrank_lt
    intro htop
    apply hx1
    refine LinearEquiv.ext fun v => ?_
    have : v ∈ fixedSpace x := htop ▸ Submodule.mem_top
    exact mem_fixedSpace.mp this
  by_cases h6 : 6 ≤ finrank K (fixedSpace x)
  · exact (perfectNoncycThreeIn_orthFixed hx h6).perfectThreeIn.mono
      (supportedBlock_le_isometryCentralizer _)
  obtain ⟨h, hh, hX, hrecX, hdeg, hdeg1, hsum⟩ := exists_orth_factor hx hlt
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
  · have h42 : r = 4 ∧ finrank K (fixedSpace x) = 4 := by omega
    obtain ⟨rfl, hfix4⟩ := h42
    have hts := not_exists_totallySingular_fixed_minus hK hx (r := 4) (m := 2) hS
      (by omega) (by decide)
    exact (perfectThreeIn_orthFixed_of_card_two_minus hx hfix4 (by simpa using hts)).mono
      (supportedBlock_le_isometryCentralizer _)

end Minus

end CFSG.HardMathSupport.Curtis.UnitaryLevi
