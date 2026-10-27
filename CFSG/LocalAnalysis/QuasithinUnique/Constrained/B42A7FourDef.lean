module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Quasithin CFSG.Open

@[expose] def AsB42A7Four : Prop :=
  ∀ (S : Type) [CommGroup S] [Finite S], (∀ s : S, s ^ 2 = 1) →
    ∀ (G L A : Subgroup (MulAut S)), Bridge.Alt57.Ctx G L 7 →
      XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤ → IsFFStarOffender G A → Nat.card S = 2 ^ 4 →
      ∀ π : ↥(alternatingGroup (Fin 7)) ≃* ↥L,
        AltConjTo 7 ((A.subgroupOf L).comap π.toMonoidHom) kleinRegular7

end CFSG.QuasithinUnique
