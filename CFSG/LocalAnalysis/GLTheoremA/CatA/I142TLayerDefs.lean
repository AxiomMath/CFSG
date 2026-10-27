module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142TTransfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I142T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

@[expose] def LayerFixTyped : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (p : ℕ), p.Prime → p ≠ 2 →
    ∀ E : Subgroup (MulAut S), IsElemAbelian p E →
    ∀ X : Subgroup S, (∀ a : ↥E, X.map (E.subtype a).toMonoidHom = X) →
      (∀ K : Subgroup S, IsComponentOf K X → I142N.CPlus (↥K ⧸ Subgroup.center ↥K)) →
        I142N.GoodA E.subtype (GLALayer X) ∧ TypesA E.subtype (GLALayer X)

end CFSG.LocalAnalysis.GLTheoremA.I142T
