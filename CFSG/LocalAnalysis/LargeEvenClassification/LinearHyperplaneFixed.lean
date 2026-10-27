module

public import CFSG.LocalAnalysis.LargeEvenClassification.SemisimpleRank
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.LargeEvenClassification.Helpers

universe fieldUniverse actingUniverse spaceUniverse

@[expose] def linearHyperplaneFixedVectors {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type actingUniverse} [CommGroup Acting] {Space : Type spaceUniverse}
    [AddCommGroup Space] [Module ScalarField Space] [Module (MonoidAlgebra ScalarField Acting) Space]
    (prime : ℕ) : Set Space :=
  {vector | ∃ Hyperplane : Subgroup Acting, Hyperplane.index ≤ prime ∧
    ∀ element : Hyperplane, (MonoidAlgebra.of ScalarField Acting) element.val • vector = vector}

theorem semisimple_hyperplane_fixed_span {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type actingUniverse} [CommGroup Acting] [Finite Acting]
    {Space : Type spaceUniverse} [AddCommGroup Space] [Module ScalarField Space]
    [Module (MonoidAlgebra ScalarField Acting) Space]
    [IsScalarTower ScalarField (MonoidAlgebra ScalarField Acting) Space]
    [IsSemisimpleModule (MonoidAlgebra ScalarField Acting) Space]
    {prime : ℕ} (hprime : prime.Prime) (hexponent : ∀ element : Acting, element ^ prime = 1) :
    Submodule.span ScalarField (linearHyperplaneFixedVectors (ScalarField := ScalarField)
      (Acting := Acting) (Space := Space) prime) = ⊤ := by
  let span := Submodule.span ScalarField
    (linearHyperplaneFixedVectors (ScalarField := ScalarField) (Acting := Acting) (Space := Space) prime)
  have hstable : ∀ scalar : MonoidAlgebra ScalarField Acting, ∀ vector : Space,
      vector ∈ span → scalar • vector ∈ span := by
    intro scalar vector hvector
    induction hvector using Submodule.span_induction with
    | mem vector hvector =>
        obtain ⟨Hyperplane, hindex, hfixed⟩ := hvector
        apply Submodule.subset_span
        refine ⟨Hyperplane, hindex, ?_⟩
        intro element
        rw [smul_comm, hfixed element]
    | zero => rw [smul_zero]; exact span.zero_mem
    | add first second _ _ hfirst hsecond => rw [smul_add]; exact span.add_mem hfirst hsecond
    | smul coefficient vector _ hvector => rw [smul_comm]; exact span.smul_mem coefficient hvector
  let algebraSpan : Submodule (MonoidAlgebra ScalarField Acting) Space := {
    carrier := span
    zero_mem' := span.zero_mem
    add_mem' := span.add_mem
    smul_mem' := hstable }
  have hsummands : ∀ Summand : Submodule (MonoidAlgebra ScalarField Acting) Space,
      IsSimpleModule (MonoidAlgebra ScalarField Acting) Summand → ∀ vector : Summand,
        (vector : Space) ∈ span := by
    intro Summand hsimple vector
    let := hsimple
    let action := groupAlgebraModuleAction (ScalarField := ScalarField) (Acting := Acting) Summand
    let : IsCyclic action.range := simple_groupAlgebra_action_cyclic Summand
    have hcardDivides := cyclic_action_card_dvd_exponent action hexponent
    have hkernelIndex : action.ker.index = Nat.card action.range := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange action).toEquiv
    have hkernelBound : action.ker.index ≤ prime :=
      hkernelIndex ▸ Nat.le_of_dvd hprime.pos hcardDivides
    apply Submodule.subset_span
    refine ⟨action.ker, hkernelBound, ?_⟩
    intro element
    have hfixed := congrArg (fun automorphism : Summand ≃ₗ[ScalarField] Summand => automorphism vector)
      element.property
    exact congrArg (fun entry : Summand => (entry : Space)) hfixed
  have htop := IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ScalarField Acting) Space
  have hgenerates : sSup {Summand : Submodule (MonoidAlgebra ScalarField Acting) Space |
      IsSimpleModule (MonoidAlgebra ScalarField Acting) Summand} ≤ algebraSpan := by
    apply sSup_le
    intro Summand hsimple vector hvector
    exact hsummands Summand hsimple ⟨vector, hvector⟩
  apply top_unique
  intro vector _
  rw [htop] at hgenerates
  exact hgenerates Submodule.mem_top

end CFSG.LargeEvenClassification.Helpers
