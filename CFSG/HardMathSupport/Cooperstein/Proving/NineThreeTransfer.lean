module

public import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
public import CFSG.HardMathSupport.Cooperstein.Transport

public section

namespace CFSG.HardMathSupport.Cooperstein.Proving

open CFSG.Open CFSG.AGLEmbedding

section Transfer

theorem isClassicalTwoOrG2_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsClassicalTwoOrG2 Y) : IsClassicalTwoOrG2 Y' := by
  rcases h with ⟨d, hd, ⟨φ⟩⟩ | ⟨n, hn, ⟨φ⟩⟩ | ⟨d, hd, ⟨φ⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans φ⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans φ⟩⟩)

theorem card_center_eq_of_mulEquiv {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) :
    Nat.card (Subgroup.center Q) = Nat.card (Subgroup.center P) := by
  rw [← Subgroup.map_center_eq e]
  exact CFSG.HardMathSupport.Cooperstein.Transport.card_map_mulEquiv e _

noncomputable def quotCenterEquiv {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) :
    P ⧸ Subgroup.center P ≃* Q ⧸ Subgroup.center Q :=
  QuotientGroup.congr (Subgroup.center P) (Subgroup.center Q) e (Subgroup.map_center_eq e)

variable {G : Type} [Group G] {X Y L S : Subgroup G}

theorem nineThreeFive_of_le (hYX : Y ≤ X) (hLY : L ≤ Y)
    (h : L ⊓ CFSG.Open.pCoreOf 2 X = L ⊓ CFSG.Open.pCoreOf 2 Y) :
    NineThreeFive Y L → NineThreeFive X L := by
  have hLX : L ≤ X := hLY.trans hYX
  intro hY
  obtain ⟨hs, ⟨φ⟩, hb⟩ := hY
  exact ⟨hs, ⟨(barMEquiv hLX hLY h).trans φ⟩, hb⟩

end Transfer

end CFSG.HardMathSupport.Cooperstein.Proving

end
