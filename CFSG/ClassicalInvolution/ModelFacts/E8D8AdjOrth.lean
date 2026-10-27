module

public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E8D8

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {ι : Type*}

omit [FiniteDimensional K V] in
theorem polar_eq_zero_of_mem_sup {U : ι → Submodule K V} {s : Finset ι} {y : V}
    (h : ∀ k ∈ s, ∀ x ∈ U k, polar Q x y = 0) {x : V} (hx : x ∈ s.sup U) : polar Q x y = 0 := by
  have hle : s.sup U ≤ LinearMap.ker ((polarBilin Q).flip y) :=
    Finset.sup_le fun k hk x hxk => by
      rw [LinearMap.mem_ker]
      simpa [polarBilin_apply_apply] using h k hk x hxk
  have := hle hx
  rw [LinearMap.mem_ker] at this
  simpa [polarBilin_apply_apply] using this

theorem finrank_sup_eq_sum_of_orth (U : ι → Submodule K V) (hnd : ∀ k, PolarNondegOn Q (U k))
    (hor : ∀ k l, k ≠ l → ∀ x ∈ U k, ∀ y ∈ U l, polar Q x y = 0) (s : Finset ι) :
    Module.finrank K ↥(s.sup U) = ∑ k ∈ s, Module.finrank K ↥(U k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.sup_insert]
    have hdis : Disjoint (U a) (s.sup U) := by
      rw [Submodule.disjoint_def]
      intro x hxa hxs
      refine hnd a x hxa fun y hy => ?_
      exact polar_eq_zero_of_mem_sup (fun k hk z hz => hor k a (fun h => ha (h ▸ hk)) z hz y hy) hxs
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U a) (s.sup U)
    rw [hdis.eq_bot, finrank_bot] at h1
    omega

theorem sum_finrank_le_of_orth [Fintype ι] (U : ι → Submodule K V)
    (hnd : ∀ k, PolarNondegOn Q (U k))
    (hor : ∀ k l, k ≠ l → ∀ x ∈ U k, ∀ y ∈ U l, polar Q x y = 0) :
    ∑ k, Module.finrank K ↥(U k) ≤ Module.finrank K V := by
  rw [← finrank_sup_eq_sum_of_orth U hnd hor Finset.univ]
  exact Submodule.finrank_le _

end CFSG.ClassicalInvolution.ModelFacts.E8D8
