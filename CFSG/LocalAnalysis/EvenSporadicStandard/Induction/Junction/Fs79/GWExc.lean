module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Defs
public import CFSG.Milestones.LR_dihedral_simple_recognition

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup

theorem excType_of_dihedral_sylow {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X)
    (S : Sylow 2 (X ⧸ center X)) {j : ℕ} (hj : 1 ≤ j)
    (hS : Nonempty (↥(S : Subgroup (X ⧸ center X)) ≃* DihedralGroup (2 ^ j))) : ExcType X := by
  have : IsSimpleGroup (X ⧸ center X) := hq.2.1
  have h := CFSG.Milestones.lr_dihedral_simple_recognition (X ⧸ center X) hq.2.2 S (j + 1)
    (by omega) (by simpa using hS)
  rcases h with ⟨p, f, hp, hp2, -, hmodel⟩ | h7
  · exact Or.inr ⟨p, f, hp, hp2, Or.inl ⟨by decide, hmodel⟩⟩
  · exact Or.inl h7

end CFSG.EvenSporadicStandard.Induction.Junction
