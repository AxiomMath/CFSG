module

public import CFSG.Blueprint.ChevalleyStringsInputs

public section

namespace CFSG.Blueprint.Chevalley

variable {τ : Tag} {R : Type*} [CommRing R]

theorem rootVec_eq_basisVec_of_isRoot {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    rootVec τ R β = Finsupp.single (Sum.inr ⟨β, hβ⟩) 1 :=
  dite_eq_left hβ

theorem xOp_apply_hVec (i j : Fin τ.rank) (c : R) :
    xOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1) := by
  change xOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [xOp, Finsupp.linearCombination_single, one_smul]

theorem yOp_apply_hVec (i j : Fin τ.rank) (c : R) :
    yOp τ R i c (hVec τ R j) =
      hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1) := by
  change yOp τ R i c (Finsupp.single (Sum.inl j) 1) = _
  rw [yOp, Finsupp.linearCombination_single, one_smul]

theorem xOp_apply_rootVec_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) := by
  rw [rootVec_eq_basisVec_of_isRoot (isRoot_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

theorem xOp_apply_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
      rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) := by
  rw [rootVec_eq_basisVec_of_isRoot (isRoot_neg_single τ i), xOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i).symm).trans (ite_eq_left rfl)

theorem yOp_apply_rootVec_neg_single (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (-Pi.single i 1)) = rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_eq_basisVec_of_isRoot (isRoot_neg_single τ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact ite_eq_left rfl

theorem yOp_apply_rootVec_single (i : Fin τ.rank) (c : R) :
    yOp τ R i c (rootVec τ R (Pi.single i 1)) =
      rootVec τ R (Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1) := by
  rw [rootVec_eq_basisVec_of_isRoot (isRoot_single τ i), yOp, Finsupp.linearCombination_single,
    one_smul]
  exact (ite_eq_right (single_ne_neg_single i)).trans (ite_eq_left rfl)

theorem xOp_apply_rootVec_of_ne (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    xOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringUp τ i α + 1),
        (((stringDown τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α + (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_basisVec_of_isRoot hα, xOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₁).trans (ite_eq_right h₂)

theorem yOp_apply_rootVec_of_ne (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    yOp τ R i c (rootVec τ R α) =
      ∑ k ∈ Finset.range (stringDown τ i α + 1),
        (((stringUp τ i α + k).choose k : R) * c ^ k) •
          rootVec τ R (α - (k : ℤ) • Pi.single i 1) := by
  rw [rootVec_eq_basisVec_of_isRoot hα, yOp, Finsupp.linearCombination_single, one_smul]
  exact (ite_eq_right h₂).trans (ite_eq_right h₁)

theorem simple_root_operators (i : Fin τ.rank) (c : R) :
    (∀ j, xOp τ R i c (hVec τ R j) =
        hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (Pi.single i 1)) ∧
      (∀ j, yOp τ R i c (hVec τ R j) =
        hVec τ R j + (((τ.cartan j i).natAbs : R) * c) • rootVec τ R (-Pi.single i 1)) ∧
      xOp τ R i c (rootVec τ R (Pi.single i 1)) = rootVec τ R (Pi.single i 1) ∧
      xOp τ R i c (rootVec τ R (-Pi.single i 1)) =
        rootVec τ R (-Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (Pi.single i 1) ∧
      yOp τ R i c (rootVec τ R (-Pi.single i 1)) = rootVec τ R (-Pi.single i 1) ∧
      yOp τ R i c (rootVec τ R (Pi.single i 1)) =
        rootVec τ R (Pi.single i 1) + c • hVec τ R i + c ^ 2 • rootVec τ R (-Pi.single i 1) ∧
      (∀ α : Fin τ.rank → ℤ, IsRoot τ α → α ≠ Pi.single i 1 → α ≠ -Pi.single i 1 →
        xOp τ R i c (rootVec τ R α) =
          ∑ k ∈ Finset.range (stringUp τ i α + 1),
            (((stringDown τ i α + k).choose k : R) * c ^ k) •
              rootVec τ R (α + (k : ℤ) • Pi.single i 1)) ∧
      (∀ α : Fin τ.rank → ℤ, IsRoot τ α → α ≠ Pi.single i 1 → α ≠ -Pi.single i 1 →
        yOp τ R i c (rootVec τ R α) =
          ∑ k ∈ Finset.range (stringDown τ i α + 1),
            (((stringUp τ i α + k).choose k : R) * c ^ k) •
              rootVec τ R (α - (k : ℤ) • Pi.single i 1)) ∧
      ∀ f g : Module.End R (RootModule τ R),
        (∀ b, f (Finsupp.single b 1) = g (Finsupp.single b 1)) → f = g :=
  ⟨fun j => xOp_apply_hVec i j c, fun j => yOp_apply_hVec i j c, xOp_apply_rootVec_single i c,
    xOp_apply_rootVec_neg_single i c, yOp_apply_rootVec_neg_single i c,
    yOp_apply_rootVec_single i c, fun _ hα h₁ h₂ => xOp_apply_rootVec_of_ne i c hα h₁ h₂,
    fun _ hα h₁ h₂ => yOp_apply_rootVec_of_ne i c hα h₁ h₂,
    fun _ _ h => Finsupp.basisSingleOne.ext fun b => h b⟩

end CFSG.Blueprint.Chevalley
