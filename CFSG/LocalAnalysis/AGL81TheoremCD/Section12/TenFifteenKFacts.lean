module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

@[expose] def KFactLieParabolicClass : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → IsClassicalTwoOrG2 Y →
    ∀ P : Subgroup Y, IsParabolicTwo ⊤ P → ∀ α : MulAut Y, Nat.Coprime (orderOf α) 6 →
      ∃ y : Y, P.map α.toMonoidHom = P.map (MulAut.conj y).toMonoidHom

@[expose] def KFactLieOutDerived : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsSimpleGroup Y → IsClassicalTwoOrG2 Y →
    ∀ d : ℕ, d.Prime → 5 ≤ d →
    (∃ T : Subgroup Y, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ ∧
      ¬ d ∣ Nat.card (Subgroup.normalizer (T : Set Y))) →
    Nat.Coprime (Nat.card (commutator (Outer Y))) (2 * d)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
