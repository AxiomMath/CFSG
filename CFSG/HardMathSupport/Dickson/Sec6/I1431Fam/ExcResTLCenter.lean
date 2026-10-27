module

public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

set_option linter.unusedSectionVars false


theorem excTL_not_comm_negRoot {τ : Tag} {K : Type} [Field K] {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) {u : K} (hu : u ≠ 0) :
    ∃ ε : K, pinnedX τ K (-β) ε * pinnedX τ K β u ≠ pinnedX τ K β u * pinnedX τ K (-β) ε := by
  obtain ⟨ε, hεε, hv⟩ := exists_rootSL2_vSL_eq (K := K) hβ
  refine ⟨ε, fun heq => hu ?_⟩
  have hss : ∀ x : K, (pinnedData τ β).2.2 • ((pinnedData τ β).2.2 • x) = x := by
    intro x
    rcases pinnedSign_eq τ β with h | h <;> rw [h] <;> simp
  have e1 : pinnedX τ K (-β) ε = rootSL2 τ K β (vSL 1) := by rw [hv 1, mul_one]
  have e2 : pinnedX τ K β u = rootSL2 τ K β (uSL ((pinnedData τ β).2.2 • u)) := by
    rw [rootSL2_uSL_eq, hss]
  rw [e1, e2, ← map_mul, ← map_mul] at heq
  have h := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0)
    (rootSL2_injective_of_field β heq)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  simp [vSL, uSL, Matrix.mul_apply, Fin.sum_univ_two] at h
  rcases h with h | h
  · exfalso
    rcases pinnedSign_eq τ β with hs | hs <;> rw [hs] at h <;> simp at h
  · exact h

@[expose] def excTLElt {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (c : K) : ↥(componentRootSpan K χ i) :=
  ⟨pinnedX τ K α c, pinnedX_mem_rootSpan hα c⟩

theorem excTLElt_coe {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (c : K) :
    ((excTLElt hα c : ↥(componentRootSpan K χ i)) : (Module.End K (RootModule τ K))ˣ) =
      pinnedX τ K α c := rfl

@[expose] def excTLHom {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) :
    Multiplicative K →* ↥(componentRootSpan K χ i) :=
  MonoidHom.mk' (fun s => excTLElt hα (Multiplicative.toAdd s)) fun a b =>
    Subtype.ext (by
      change pinnedX τ K α (Multiplicative.toAdd (a * b)) = _
      rw [toAdd_mul, pinnedX_add]
      rfl)

theorem excTLHom_coe {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (s : Multiplicative K) :
    excTLHom hα s = excTLElt hα (Multiplicative.toAdd s) := rfl

theorem excTL_elt_not_central {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {β : Fin τ.rank → ℤ} (hβ : β ∈ componentRoots χ i) (hnβ : -β ∈ componentRoots χ i) {u : K}
    (hu : u ≠ 0) : excTLElt hβ u ∉ Subgroup.center ↥(componentRootSpan K χ i) := by
  intro hcen
  obtain ⟨ε, hε⟩ := excTL_not_comm_negRoot (K := K) ((isRootComponent_componentRoots i).isRoot β hβ) hu
  exact hε (congrArg Subtype.val (Subgroup.mem_center_iff.1 hcen (excTLElt hnβ ε)))

end CFSG.HardMathSupport.Dickson.Sec6.I1431
