module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269U42
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269U5
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def I269Residual : Prop :=
  ∀ (S : Type) [Group S],
    catalogIs S (fun i => S9.isSp6two i ∨ S9.isD4two i ∨ S9.isTD4two i ∨ S9.isU3eight i) → E9Solv S

theorem i269At_of_residual (h : I269Residual) (G : Type) [Group G]
    [Finite G] : I269At G := by
  intro X L D _ hL hcat hD hDN hcard
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with h1 | h1 | h1 | h1 | h1 | h1
  · exact layer_eq_bot_of_E9 hL (h _ ⟨i, Or.inl h1, ⟨e⟩⟩) hDN hD hcard
  · exact layer_eq_bot_of_u42 hL ⟨i, h1, ⟨e⟩⟩ hDN hD hcard
  · exact layer_eq_bot_of_E9 hL (h _ ⟨i, Or.inr (Or.inl h1), ⟨e⟩⟩) hDN hD hcard
  · exact layer_eq_bot_of_E9 hL (h _ ⟨i, Or.inr (Or.inr (Or.inl h1)), ⟨e⟩⟩) hDN hD hcard
  · exact layer_eq_bot_of_E9 hL (h _ ⟨i, Or.inr (Or.inr (Or.inr h1)), ⟨e⟩⟩) hDN hD hcard
  · exact layer_eq_bot_of_u5 hL ⟨i, h1, ⟨e⟩⟩ hDN hD hcard

end CFSG.LocalAnalysis.GLTheoremA

end
