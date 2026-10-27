module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.InnerCoveredExcCross
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.InnerCoveredReeF4
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.ExcSuzuki
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.ExcTits

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.HardMathSupport.Foote.E27 TauCeti

@[expose] def InnerCoveredExcCrossOpen (i : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p ≠ 3 ∧ (i = .F4 q ∨ i = .E6 q ∨ i = .twistedE6 q ∨
    i = .E7 q ∨ i = .E8 q ∨ i = .trialityD4 q)

section


theorem false_of_exc_cross_of_open
    (leaf : ∀ {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X},
      E27Config X K R T z → z ∈ K → ∀ d : ValidLieTypeIndex, InnerCoveredExcCrossOpen d.1 →
        Nonempty (↥K ≃* (CFSGIndex.lie d).Group) → False)
    {X : Type} [Group X] [Finite X] {K R T : Subgroup X} {z : X}
    (h : E27Config X K R T z) (hz : z ∈ K) (d : ValidLieTypeIndex)
    (hd : InnerCoveredExcCross d.1) (e : Nonempty (↥K ≃* (CFSGIndex.lie d).Group)) : False := by
  obtain ⟨i, hv⟩ := d
  rcases hd with ⟨q, hq, hi⟩ | ⟨m, hi⟩ | ⟨m, hi⟩ | hi
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact false_of_exc_cross_G2 h hz q hv hq e
    · exact leaf h hz ⟨_, hv⟩ ⟨q, hq, Or.inl rfl⟩ e
    · exact leaf h hz ⟨_, hv⟩ ⟨q, hq, Or.inr (Or.inl rfl)⟩ e
    · exact leaf h hz ⟨_, hv⟩ ⟨q, hq, Or.inr (Or.inr (Or.inl rfl))⟩ e
    · exact leaf h hz ⟨_, hv⟩ ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ e
    · exact leaf h hz ⟨_, hv⟩ ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩ e
    · exact leaf h hz ⟨_, hv⟩ ⟨q, hq, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩ e
  · subst hi
    exact false_of_exc_cross_reeF4 h hz m hv e
  · subst hi
    exact CFSG.HardMathSupport.Malle.E27Lie.false_of_suzuki h hz hv e
  · subst hi
    exact CFSG.HardMathSupport.Malle.E27Lie.false_of_tits h hz e

end

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
