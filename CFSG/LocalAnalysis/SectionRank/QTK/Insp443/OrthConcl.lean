module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.ConclKLeft
public import CFSG.Quasithin.EmptyFaithful.S151CLG2Lift

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Blueprint CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch4.E443
open scoped IsMulCommutative

theorem conclKLeft_of_binaryOrthogonalFour {X : Type} [Group X] [Finite X]
    {L V MK : Subgroup X} {m : ℕ} (hm : 1 ≤ m) (hpsl : IsPSL 2 2 (2 * m) (ModO2 L))
    [IsMulCommutative ↥V] (hO : BinaryOrthogonalFour (V := ↥V) (autOn L V) ⊤ ⊥ m) :
    ConclKLeft X L V MK := by
  have hn : 2 ≤ 2 * m := by omega
  have hQ : CFSG.IsQuasisimple (ModO2 L) :=
    CFSG.Quasithin.CLG2.isQuasisimple_of_isPSL_two_two hn hpsl
  have hshape : Shape443 (ModO2 L) :=
    Or.inl ⟨2 * m, hn, Or.inl ⟨by decide, hpsl⟩⟩
  refine ⟨hQ, hshape, Or.inr (Or.inl ⟨m, hm, ?_, ⟨inferInstance, hO⟩⟩)⟩
  exact Or.inl ⟨by decide, hpsl⟩

end CFSG.SectionRank.QTK.Insp443

end
