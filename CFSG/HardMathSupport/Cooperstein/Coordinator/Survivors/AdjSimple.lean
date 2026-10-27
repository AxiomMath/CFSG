module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjGen
public import CFSG.Quasithin.Background.SmithCurtisChev

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem


variable {τ : Tag} (K : Type) [Field K]

variable (τ) in
@[expose] def adjRep : Representation K (adjointGroup τ K) (RootModule τ K) :=
  (Units.coeHom (Module.End K (RootModule τ K))).comp (adjointGroup τ K).subtype

variable {K}

theorem adjRep_apply (g : adjointGroup τ K) :
    adjRep τ K g = ((g : ModGL τ K) : Module.End K (RootModule τ K)) := rfl

theorem adjRep_xC (i : Fin τ.rank) (c : K) : adjRep τ K (xC τ K i c) = xOp τ K i c := rfl

theorem adjRep_yC (i : Fin τ.rank) (c : K) : adjRep τ K (yC τ K i c) = yOp τ K i c := rfl

theorem adjRep_nC (i : Fin τ.rank) :
    adjRep τ K (nC τ K i) = (weylElt τ K i 1 : Module.End K (RootModule τ K)) := rfl

section Span

variable [CharP K 2] {θ : Fin τ.rank → ℤ}

theorem weylElt_one_rootVec' (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (weylElt τ K i 1 : Module.End K (RootModule τ K)) (rootVec τ K α) =
      rootVec τ K (reflect τ i α) := by
  rw [weylElt_rootVec i 1 hα]
  simp [CharTwo.neg_eq]

abbrev spanθ (θ : Fin τ.rank → ℤ) : Submodule K (RootModule τ K) :=
  orbitSpan (adjRep τ K) (rootVec τ K θ)

theorem span_reflect (i : Fin τ.rank) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h : rootVec τ K α ∈ spanθ θ) : rootVec τ K (reflect τ i α) ∈ spanθ (K := K) θ := by
  have := orbitSpan_stable (adjRep τ K) (rootVec τ K θ) (nC τ K i) h
  rwa [adjRep_nC, weylElt_one_rootVec' i hα] at this

theorem span_foldr (l : List (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (h : rootVec τ K α ∈ spanθ θ) :
    IsRoot τ (l.foldr (reflect τ) α) ∧ rootVec τ K (l.foldr (reflect τ) α) ∈ spanθ (K := K) θ := by
  induction l with
  | nil => exact ⟨hα, h⟩
  | cons i l ih =>
    rw [List.foldr_cons]
    exact ⟨.reflect i ih.1, span_reflect i ih.1 ih.2⟩

theorem span_all_roots (hθ : IsRoot τ θ) {words : Fin τ.rank → List (Fin τ.rank)}
    (hwords : ∀ j, (words j).foldr (reflect τ) θ = Pi.single j 1) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : rootVec τ K α ∈ spanθ (K := K) θ := by
  induction hα with
  | basis j =>
    have := span_foldr (K := K) (words j) hθ (mem_orbitSpan_self (adjRep τ K) _)
    rw [hwords j] at this
    exact this.2
  | reflect i hv ih => exact span_reflect i hv ih

theorem span_hVec (hθ : IsRoot τ θ) {words : Fin τ.rank → List (Fin τ.rank)}
    (hwords : ∀ j, (words j).foldr (reflect τ) θ = Pi.single j 1) (i : Fin τ.rank) :
    hVec τ K i ∈ spanθ (K := K) θ := by
  have h2 := span_all_roots (K := K) hθ hwords (isRoot_single τ i)
  have h3 := span_all_roots (K := K) hθ hwords (isRoot_neg_single τ i)
  have h1 := orbitSpan_stable (adjRep τ K) (rootVec τ K θ) (yC τ K i 1) h2
  rw [adjRep_yC, yOp_rootVec_single_eq] at h1
  have := sub_mem (sub_mem h1 h2) h3
  simpa [add_assoc] using this

theorem orbitSpan_adjRep (hθ : IsRoot τ θ) {words : Fin τ.rank → List (Fin τ.rank)}
    (hwords : ∀ j, (words j).foldr (reflect τ) θ = Pi.single j 1) :
    spanθ (K := K) θ = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  refine adj_induction (P := fun v => v ∈ spanθ (K := K) θ) (zero_mem _) (fun _ _ => add_mem)
    (fun c _ h => Submodule.smul_mem _ c h) (span_hVec hθ hwords) (fun α => ?_) v
  by_cases hα : IsRoot τ α
  · exact span_all_roots hθ hwords hα
  · rw [rootVec_eq_zero hα]; exact zero_mem _

end Span

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
