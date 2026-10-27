module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
public import CFSG.Quasithin.Background.B4Models

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

@[expose] def AsB42A57 : Prop :=
  ∀ (S : Type) [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut S)) (m : ℕ), Bridge.Alt57.Ctx G L m →
      XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤ → IsFFStarOffender G A →
      (m = 5 ∧ BinaryNaturalSL L ⊤ ⊥ 2 2) ∨ AlternatingNatural L ⊤ ⊥ m ∨
        (m = 7 ∧ Nat.card S = 2 ^ 4)

end CFSG.QuasithinUnique
