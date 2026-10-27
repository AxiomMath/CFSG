module

public import CFSG.GH74.GLS.Bg.Iii2.Statements
public import CFSG.GH74.GLS.Bg.Iii2.L41Main

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip

theorem l41_of (h44 : II4_44) : L41 := by
  intro G _ _ hG h3 x K hxK hK1
  have hR : ∀ y : G, orderOf y = 2 → 3 ≤ pRank 2 ↥(centralizer ({y} : Set G)) := fun y hy =>
    TwoThin.rankThreeCentralizers G hG.1 hG.2.1 h3 y hy
  have hSL : IsSL2Or2A7 (↥K ⧸ pPrimeCore 2 ↥K) := h44 G hG x hxK.1.1 K hxK.1.2.2 hK1
  have hZ : center (↥K ⧸ pPrimeCore 2 ↥K) ≠ ⊥ := by
    intro h
    have h2 := hSL.2
    rw [h, Subgroup.card_bot] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨z, L, hP, ⟨e⟩⟩ := L41.exists_goodPair hR hxK hZ
  refine ⟨z, L, L41.isPRigid_of_goodPair hP, ?_⟩
  have h1 : pRank 2 (Hat L) = pRank 2 (Hat K) := pRank_eq_of_mulEquiv' e
  rw [← pRank_hat L, h1, pRank_hat K]
  exact hK1

end CFSG.GH74.GLS.Bg.Iii2
