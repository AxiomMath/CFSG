module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualDecomp
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.CharSum
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualEichler

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem res_exists_move_of_mem_V2 (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ u ∈ T, Q u = 0)
    {W : Submodule K V} (hWts : ∀ w ∈ W, Q w = 0) (hWx : ∀ w ∈ W, x w ∈ W) {w : V}
    (hwW : w ∈ W) (hw0 : w ≠ 0) (hw2 : x (x w) + x w + w = 0) :
    ∃ g : V ≃ₗ[K] V, g ∈ isometryCentralizer Q x ∧
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧ ∃ w ∈ W, g w ∉ W := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ := res_polarBilin_nondegenerate hx
  have hQw : Q w = 0 := hWts w hwW
  obtain ⟨c', hc'⟩ := exists_polar_ne_zero hQ hw0
  obtain ⟨hcV2, hcpol⟩ := res_projV2 hx c'
  set c := x c' + x (x c') with hc
  have hwc : polar Q w c = 1 := by
    rw [hcpol w hw2]
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK (polar Q w c') with h | h
    · exact absurd h hc'
    · exact h
  set a := c + Q c • w with ha
  have hww : polar Q w w = 0 := CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQw
  have hwa : polar Q w a = 1 := by
    rw [ha, polar_add_right, polar_smul_right, hwc, hww, smul_zero, add_zero]
  have hQa : Q a = 0 := by
    rw [ha, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQw, polar_smul_right, polar_comm Q c w,
      hwc]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
    exact CharTwo.add_self_eq_zero _
  have hPa : x (x a) + x a + a = 0 := by
    have : x (x a) + x a + a = (x (x c) + x c + c) + Q c • (x (x w) + x w + w) := by
      simp only [ha, map_add, map_smul]
      module
    rw [this, hcV2, hw2]
    simp
  have hxa3 : x (x (x a)) = a := res_x_cube hx a
  have hQb : Q (x a) = 0 := by rw [res_map_x hx, hQa]
  have hsum : x (x a) = a + x a := by
    rw [← sub_eq_zero]
    have : x (x a) - (a + x a) = (x (x a) + x a + a) - (2 : K) • (a + x a) := by module
    rw [this, hPa, h2]
    simp
  have hQab : Q (a + x a) = 0 := by rw [← hsum, res_map_x hx, hQb]
  have hab : polar Q a (x a) = 0 := by
    have h := QuadraticMap.map_add Q a (x a)
    rw [hQab, hQa, hQb] at h
    simpa using h.symm
  set g := eichler Q a (x a) with hg
  have hconj : x * g * x⁻¹ = g := by
    rw [hg, eichler_conj hx.mem, hsum]
    refine LinearEquiv.ext fun v => ?_
    have hP : polar Q (x a) (a + x a) = 0 := by
      rw [polar_add_right, polar_comm Q (x a) a, hab,
        CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQb, add_zero]
    rw [res_eichler_apply hQb hQab hP, res_eichler_apply hQa hQb hab, polar_add_right,
      ← sub_eq_zero]
    have : v + polar Q v (x a) • (a + x a) + (polar Q v a + polar Q v (x a)) • x a -
        (v + polar Q v a • x a + polar Q v (x a) • a) = (2 : K) • (polar Q v (x a) • x a) := by
      module
    rw [this, h2, zero_smul]
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q a (x a)
  refine ⟨g, res_mem_isometryCentralizer_of_conj hgO hconj,
    res_eichler_mem_commutator hQ hT a (x a), ⟨1, res_eichler_pow_two hab⟩, w, hwW, ?_⟩
  intro hgw
  have hgwv : g w = w + x a + polar Q w (x a) • a := by
    rw [hg, res_eichler_apply hQa hQb hab, hwa, one_smul]
  have hmem : x a + polar Q w (x a) • a ∈ W := by
    have := W.sub_mem hgw hwW
    have e : g w - w = x a + polar Q w (x a) • a := by rw [hgwv]; module
    rwa [e] at this
  have haW : a ∈ W := by
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK (polar Q w (x a)) with h | h
    · rw [h, zero_smul, add_zero] at hmem
      have := hWx _ (hWx _ hmem)
      rwa [hxa3] at this
    · rw [h, one_smul] at hmem
      have e : x a + a = x (x a) := by rw [hsum, add_comm]
      rw [e] at hmem
      have := hWx _ hmem
      rwa [hxa3] at this
  have hz : polar Q w a = 0 := by
    have := QuadraticMap.map_add Q w a
    rw [hWts _ (W.add_mem hwW haW), hQw, hQa] at this
    simpa using this.symm
  rw [hwa] at hz
  exact one_ne_zero hz

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
