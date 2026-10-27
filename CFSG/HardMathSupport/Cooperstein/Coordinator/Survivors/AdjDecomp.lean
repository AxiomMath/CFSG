module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjGen

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Blueprint.Chevalley


variable {τ : Tag} {F : Type} [Field F]

@[expose] def coordRLin (β : Fin τ.rank → ℤ) : RootModule τ F →ₗ[F] F where
  toFun v := coordR v β
  map_add' v w := coordR_add v w β
  map_smul' c v := coordR_smul c v β

@[expose] def Bop (τ : Tag) (F : Type) [Field F] (i : Fin τ.rank) :
    Module.End F (RootModule τ F) :=
  (coordRLin (τ := τ) (F := F) (-Pi.single i 1)).smulRight (rootVec τ F (Pi.single i 1))

theorem Bop_apply (i : Fin τ.rank) (v : RootModule τ F) :
    Bop τ F i v = coordR v (-Pi.single i 1) • rootVec τ F (Pi.single i 1) := rfl

variable {θ : Fin τ.rank → ℤ}

theorem xOp_eq_decomp (H : AdjHyp τ θ) (i : Fin τ.rank) (c : F) (v : RootModule τ F) :
    xOp τ F i c v = v + c • (Dop τ F i v - Bop τ F i v) + c ^ 2 • Bop τ F i v := by
  refine adj_induction (P := fun v => xOp τ F i c v =
    v + c • (Dop τ F i v - Bop τ F i v) + c ^ 2 • Bop τ F i v) ?_ ?_ ?_ ?_ ?_ v
  · simp
  · intro v w hv hw
    simp only [map_add, hv, hw, smul_add, smul_sub]
    abel
  · intro a v hv
    simp only [map_smul, hv, smul_add, smul_sub, smul_comm c a, smul_comm (c ^ 2) a]
  · intro j
    rw [xOp_hVec_eq, Dop_hVec, Bop_apply, coordR_hVec, zero_smul]
    simp only [sub_zero, smul_zero, add_zero, smul_smul, mul_comm]
  · intro α
    by_cases hα : IsRoot τ α
    swap
    · rw [rootVec_eq_zero hα]; simp
    by_cases h1 : α = Pi.single i 1
    · subst h1
      rw [xOp_rootVec_single_eq, Dop_rootVec_single, Bop_apply,
        coordR_rootVec (isRoot_single τ i), if_neg (single_ne_neg_single i)]
      simp
    by_cases h2 : α = -Pi.single i 1
    · subst h2
      rw [xOp_rootVec_neg_single_eq, Dop_rootVec_neg_single, Bop_apply,
        coordR_rootVec (isRoot_neg_single τ i), if_pos rfl]
      simp only [one_smul, add_sub_cancel_right]
    · rw [Bop_apply, coordR_rootVec hα, if_neg (fun h => h2 h), zero_smul,
        Dop_rootVec_of_ne H i hα h1 h2]
      by_cases hr : IsRoot τ (α + Pi.single i 1)
      · rw [xOp_rootVec_of_up_one H i c hα h1 h2 hr]
        simp
      · rw [xOp_rootVec_of_up_zero H i c hα h1 h2 hr, rootVec_eq_zero hr]
        simp

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
