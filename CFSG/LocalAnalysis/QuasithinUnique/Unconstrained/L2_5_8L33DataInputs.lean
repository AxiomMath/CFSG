module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsTauInputs

public section

namespace CFSG.QuasithinUnique.Unc25L33
open CFSG.QuasithinUnique.Unc25K1

@[expose] def sa : R9 := ⟨0, 0, 1, 0, 1, 1, 2, 1, 0⟩

@[expose] def sb : R9 := ⟨2, 0, 0, 0, 0, 2, 0, 2, 0⟩

@[expose] def rpw (x : R9) : ℕ → R9
  | 0 => rone
  | n + 1 => rmul x (rpw x n)

@[expose] def P0R : List R9 :=
  (List.range 8).flatMap fun i => (List.range 2).map fun j => rmul (rpw sa i) (rpw sb j)

@[expose] def invsP0 : List R9 := P0R.filter fun x => x != rone && rmul x x == rone

@[expose] def W3 : List R9 := [⟨1, 0, 1, 1, 1, 2, 0, 0, 1⟩, ⟨0, 1, 1, 2, 1, 1, 2, 1, 2⟩]

@[expose] def NormProp (g : R9) : Prop :=
  (∃ p ∈ P0R, rmul g sa = rmul p g) → (∃ q ∈ P0R, rmul g sb = rmul q g) → g ∈ P0R

instance (g : R9) : Decidable (NormProp g) := by
  unfold NormProp
  infer_instance

@[expose] def CentProp (g : R9) : Prop :=
  ∀ t ∈ invsP0, ∀ s ∈ invsP0, rmul g t = rmul t g → rmul g s = rmul s g → t ≠ s →
    rmul t s = rmul s t → g = rone ∨ g = t ∨ g = s ∨ g = rmul t s

instance (g : R9) : Decidable (CentProp g) := by
  unfold CentProp
  infer_instance

@[expose] def FixProp (g : R9) : Prop :=
  ∀ t ∈ invsP0, ∀ s ∈ invsP0, rmul g (rcof t) = rmul t g → rmul g (rcof s) = rmul s g → t ≠ s →
    rmul t s = rmul s t →
      (∃ p ∈ P0R, rmul g (rcof sa) = rmul p g) ∧ (∃ q ∈ P0R, rmul g (rcof sb) = rmul q g)

instance (g : R9) : Decidable (FixProp g) := by
  unfold FixProp
  infer_instance

end CFSG.QuasithinUnique.Unc25L33
