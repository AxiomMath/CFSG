module

public import CFSG.GroupTheory.PCore.Defs
public import CFSG.Open.LocalVocabulary

public section

open Subgroup

namespace CFSG.ABGLocalTools

structure QGroupStabilityFacts (q : ℕ) (H : Type*) [Group H] : Prop where
  layer : ∃ (J : Subgroup (H ⧸ oddCore H)) (F : Type) (_ : Field F) (_ : Finite F),
    J.Normal ∧ Nat.card F = q ∧ Nonempty (J ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      IsPGroup 2 (centralizer (J : Set (H ⧸ oddCore H)))

end CFSG.ABGLocalTools
