module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

section CharTwo

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem res_add_self (K : Type) [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    (w : V) : w + w = 0 := by
  rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]

theorem res_eichler_apply {u w : V} (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0)
    (v : V) : eichler Q u w v = v + polar Q v u • w + polar Q v w • u := by
  rw [eichler_apply hu huw, hw, zero_mul, add_zero, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]

theorem res_eichler_pow_two {u w : V} (huw : polar Q u w = 0) :
    eichler Q u w ^ (2 ^ 1) = 1 := by
  rw [pow_one, pow_two, eichler_mul huw huw, res_add_self K, eichler_zero_right]

omit [CharP K 2] in
theorem res_mem_isometryCentralizer_of_conj {x g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h : x * g * x⁻¹ = g) :
    g ∈ isometryCentralizer Q x := by
  refine mem_isometryCentralizer.2 ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg, fun v => ?_⟩
  have := congrArg (fun f : V ≃ₗ[K] V => f (x v)) h
  simp only [LinearEquiv.mul_apply] at this
  rw [← this]
  simp

end CharTwo

section Finite

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [CharP K 2] in
theorem res_eichler_mem_commutator (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (u w : V) :
    eichler Q u w ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have h := (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT).1
  have h' : CFSG.RankThree.Classical2.orthDerived Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := rfl
  rw [← h', h]
  exact eichler_mem_elementaryGroup Q u w

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem res_exists_le_finrank_eq (T : Submodule K V) {n : ℕ} (hn : n ≤ finrank K T) :
    ∃ T' ≤ T, finrank K T' = n := by
  classical
  obtain ⟨s, hs, hli⟩ := exists_finset_linearIndependent_of_le_finrank (R := K) (M := T) hn
  refine ⟨(Submodule.span K (s : Set T)).map T.subtype, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Submodule.finrank_map_subtype_eq, finrank_span_finset_eq_card hli, hs]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem res_polarBilin_nondegenerate {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    (polarBilin Q).Nondegenerate :=
  ⟨fun v hv => hx.regular v fun w => by simpa [polarBilin_apply_apply] using hv w,
   fun v hv => hx.regular v fun w => by
    rw [QuadraticMap.polar_comm]; simpa [polarBilin_apply_apply] using hv w⟩

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem res_exists_three_of_four
    (hmax : ∃ U : Submodule K V, finrank K U = 4 ∧ ∀ u ∈ U, Q u = 0) :
    ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 := by
  obtain ⟨U, hU, hUQ⟩ := hmax
  obtain ⟨T, hTU, hT⟩ := res_exists_le_finrank_eq U (n := 3) (by omega)
  exact ⟨T, hT, fun u hu => hUQ u (hTU hu)⟩

end Finite

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.PerfThreeOrth
