module

public import CFSG.Blueprint.Chevalley
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open CFSG.Blueprint.Chevalley

@[expose] def E8Witness : Prop :=
  ∀ (F : Type) [Field F] [Finite F], orderOf ((Nat.card F : ℕ) : ZMod 5) = 4 →
    ∃ (E : Subgroup (adjointGroup Tag.E8 F)) (g : adjointGroup Tag.E8 F),
      IsElemAbelian 5 E ∧ g ^ 5 = 1 ∧ (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧ ∃ x ∈ E, g * x ≠ x * g

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega
