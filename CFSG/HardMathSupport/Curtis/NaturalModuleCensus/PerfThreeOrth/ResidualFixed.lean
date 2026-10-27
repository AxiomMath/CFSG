module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth.ResidualCount

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}

theorem res_exists_move_of_fixed_four (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hdim : finrank K V = 8)
    (hmax : ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (hfix : finrank K (fixedSpace x) = 4) {W : Submodule K V} (hWts : ∀ w ∈ W, Q w = 0) {w : V}
    (hwW : w ∈ W) (hw0 : w ≠ 0) (hwx : x w = w) :
    ∃ g : V ≃ₗ[K] V, g ∈ isometryCentralizer Q x ∧
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧ ∃ w ∈ W, g w ∉ W := by
  have hQ := res_polarBilin_nondegenerate hx
  have hT := res_exists_three_of_four hmax
  have hQw : Q w = 0 := hWts w hwW
  have hww : polar Q w w = 0 := CFSG.ClassicalGroups.Orthogonal.polar_self_eq_zero hQw
  obtain ⟨c', hc'⟩ := exists_polar_ne_zero hQ hw0
  obtain ⟨hcfix, hcpol⟩ := res_projV1 hx c'
  set c := c' + x c' + x (x c') with hc
  have hwc : polar Q w c = 1 := by
    rw [hcpol w hwx]
    rcases eq_zero_or_eq_one_of_natCard_eq_two hK (polar Q w c') with h | h
    · exact absurd h hc'
    · exact h
  set a := c + Q c • w with ha
  have hwa : polar Q w a = 1 := by
    rw [ha, polar_add_right, polar_smul_right, hwc, hww, smul_zero, add_zero]
  have hax : x a = a := by rw [ha, map_add, map_smul, hcfix, hwx]
  have hQa : Q a = 0 := by
    rw [ha, QuadraticMap.map_add Q, QuadraticMap.map_smul, hQw, polar_smul_right, polar_comm Q c w,
      hwc]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨s₁, s₂, hx₁, hx₂, hQ₁, hQ₂, h₁w, h₁a, h₂w, h₂a, h₁₂⟩ :=
    res_exists_two_singular hK hx hdim hmax hfix hwx hax hQw hQa hwa
  obtain ⟨s, hsx, hQs, hsw, hsa, hsW⟩ : ∃ s, x s = s ∧ Q s = 0 ∧ polar Q s w = 0 ∧
      polar Q s a = 0 ∧ s ∉ W := by
    by_cases h₁W : s₁ ∈ W
    · refine ⟨s₂, hx₂, hQ₂, h₂w, h₂a, fun h₂W => h₁₂ ?_⟩
      have := QuadraticMap.map_add Q s₁ s₂
      rw [hWts _ (W.add_mem h₁W h₂W), hWts _ h₁W, hWts _ h₂W] at this
      simpa using this.symm
    · exact ⟨s₁, hx₁, hQ₁, h₁w, h₁a, h₁W⟩
  have has : polar Q a s = 0 := by rw [polar_comm, hsa]
  have hws : polar Q w s = 0 := by rw [polar_comm, hsw]
  set g := eichler Q a s with hg
  have hconj : x * g * x⁻¹ = g := by
    rw [hg, eichler_conj hx.mem, hax, hsx]
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q a s
  refine ⟨g, res_mem_isometryCentralizer_of_conj hgO hconj,
    res_eichler_mem_commutator hQ hT a s, ⟨1, res_eichler_pow_two has⟩, w, hwW, fun hgw => hsW ?_⟩
  have hgwv : g w = w + s := by
    rw [hg, res_eichler_apply hQa hQs has, hwa, hws, one_smul, zero_smul, add_zero]
  have := W.sub_mem hgw hwW
  rwa [hgwv, add_sub_cancel_left] at this

theorem res_exists_move_of_fixed (hK : Nat.card K = 2) (hx : OddOrderIsometry Q 3 x)
    (hdim : finrank K V = 8)
    (hmax : ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0)
    (hfix : finrank K (fixedSpace x) = 4 ∨ finrank K (fixedSpace x) = 2)
    {W : Submodule K V} (hWts : ∀ w ∈ W, Q w = 0) {w : V} (hwW : w ∈ W) (hw0 : w ≠ 0)
    (hwx : x w = w) :
    ∃ g : V ≃ₗ[K] V, g ∈ isometryCentralizer Q x ∧
      g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      (∃ k : ℕ, g ^ (2 ^ k) = 1) ∧ ∃ w ∈ W, g w ∉ W := by
  rcases hfix with h4 | h2
  · exact res_exists_move_of_fixed_four hK hx hdim hmax h4 hWts hwW hw0 hwx
  · exfalso
    refine not_exists_totallySingular_fixed_of_odd hK hx (r := 4) (m := 3) hdim hmax (by omega)
      (by decide) ⟨Submodule.span K {w}, ?_, ?_, ?_⟩
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 (mem_fixedSpace.2 hwx)
    · rw [finrank_span_singleton hw0]
    · intro v hv
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [QuadraticMap.map_smul, hWts w hwW, smul_zero]

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
