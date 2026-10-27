module

public import CFSG.ClassicalInvolution.Q3.TL4ModelFacts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

@[expose] def SecIdE3S3NoTwist : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    EdgelessMember3 R S t → MuS3Member R → ¬ TightInO2 t → TightTwisted Y t →
      ((¬ TightActs3 R t ∧ Thm6Exit (Y ⧸ Subgroup.center Y)) ∨
        Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) → False

end CFSG.ClassicalInvolution.Q3.TL4
