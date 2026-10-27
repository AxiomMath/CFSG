module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.Assembly
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.OrthPlusIndex
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SU

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

open CFSG.AGLEmbedding TauCeti

section Main


@[expose] def LieInputRestTwistedD : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (d : TauCeti.ValidLieTypeIndex) (r : ℕ)
    (q : TauCeti.PrimePower), d.1 = .twistedD r q → q.p = 2 →
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) → SimpleStmt Y

theorem lieInputRest_of_twistedD_and_orth_plus (hT : LieInputRestTwistedD)
    (hL : OrthPlusLeviOb) (hC : OrthPlusCentOb) : LieInputRest := by
  intro Y _ _ hR
  obtain ⟨d, hd, ⟨e⟩⟩ := hR
  obtain ⟨i, hv⟩ := d
  cases i with
  | twistedA r q =>
    exact simpleStmt_of_twistedA_index (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩) rfl hd e
  | D r q =>
    exact simpleStmt_of_D_index hL hC (Or.inl ⟨⟨_, hv⟩, hd, ⟨e⟩⟩) rfl hd e
  | twistedD r q => exact hT Y ⟨_, hv⟩ r q rfl hd ⟨e⟩
  | _ => exact hd.elim

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

end
