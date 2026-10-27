module

public import CFSG.CGT.Foote82.FPrimeDefs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

@[expose] def Thm66F : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V] (G S L : Subgroup (GLV V)),
    CFSG.Assembly.KProper CFSG.Assembly.InCatalog ↥G → Setup6Irr G S L → IsFPrimeModule L →
      L = G ∨
      (∃ n k : ℕ, 6 ≤ n ∧ 1 ≤ k ∧ Nonempty (↥L ≃* alternatingGroup (Fin n)) ∧
        IsAltHeartFor (layerIn G) (n + 2 * k)) ∨
      (Nonempty (↥L ≃* alternatingGroup (Fin 6)) ∧ IsOmegaMinusFor (layerIn G) 2)

end CFSG.CGT.Foote82
