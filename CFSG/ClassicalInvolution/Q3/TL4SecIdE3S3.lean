module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

@[expose] def SecIdE3MuS3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Thm6RBelow 3 (Nat.card Y) →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      EdgelessMember3 R S t → MuS3Member R → ¬ TightInO2 t →
        ((¬ TightActs3 R t ∧ (Thm6Exit Y ∨ TightTwisted Y t)) ∨
          Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) →
        IsSimpleGroup ↥(genFittingFStar Y) ∧ (genFittingFStar Y).index ∣ 6 ∧ ¬ TightTwisted Y t

end CFSG.ClassicalInvolution.Q3.TL4
