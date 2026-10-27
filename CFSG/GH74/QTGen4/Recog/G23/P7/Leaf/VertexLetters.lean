module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.VertexLettersC
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem leafVertexLetters
    : LeafVertexLetters := by
  intro G _ _ σ a b z M W w₁ w₂ h
  obtain ⟨k, hk₁, hk₂⟩ := h.toVHc.main
  exact ⟨k, hk₁, hk₂, h.toVHc.generation⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
