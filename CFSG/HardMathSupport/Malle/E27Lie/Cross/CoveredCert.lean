module

public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Covered
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.ExcSuzuki
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.ExcTits

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

open CFSG.HardMathSupport.Foote.E27 CFSG.AGLEmbedding TauCeti

section Certs


@[expose] def InnerCoveredExc (i : LieTypeIndex) : Prop :=
  (∃ m : ℕ, i = .suzuki m) ∨ i = .tits

theorem false_of_innerCoveredAll {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (d : ValidLieTypeIndex)
    (hd : InnerCovered d.1 ∨ InnerCoveredExc d.1)
    (e : Nonempty (↥K ≃* (CFSGIndex.lie d).Group)) : False := by
  rcases hd with hd | ⟨m, hm⟩ | hm
  · exact false_of_innerCovered h hz d hd e
  · obtain ⟨i, hv⟩ := d
    cases hm
    exact false_of_suzuki h hz hv e
  · obtain ⟨i, hv⟩ := d
    cases hm
    exact false_of_tits h hz e

end Certs

end CFSG.HardMathSupport.Malle.E27Lie
