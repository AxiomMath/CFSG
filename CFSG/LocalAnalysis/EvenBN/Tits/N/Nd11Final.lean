module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11P1
public import CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11S

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped Pointwise commutatorElement

section Final

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

theorem node11_of_nodes (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h07 : Node07 d) (h08 : Node08 d z₀) (h09 : Node09 d z₀) (h10 : Node10 d z₀) :
    Node11 d z₀ := by
  have hsq := z0_sq hz h10
  have hcomm := P1_comm h49 hd hz h07 h08 h09 h10
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (Kc_comm h49 hd hz h07 h08 h09 h10 a a.2 b b.2)⟩⟩,
    Kc_le_P1 h49 hd hz h07 h08 h09 h10, Kc_relIndex h49 hd hz h07 h08 h09 h10⟩,
    P_eq_zpowers_P1 h49 hd hz h07 h08 h09 h10, ⟨exists_u h49 hd hz h07 h08 h09 h10,
      fun n hn x hx => Pe10_inv h49 hd hz h07 h10 hn hx,
      Pe10_central h49 hd hz h07 h08 h09 h10⟩,
    ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, fun y hy => ?_⟩,
    fun n hn x hx => ?_, P1_CNt h49 hd hz h07 h08 h09, ?_⟩
  · obtain ⟨v, hvK, hv, hgen⟩ := exists_v h49 hd hz h07 h08 h09 h10 hy
    exact ⟨v, hvK, hv, hgen⟩
  · obtain ⟨y, hy⟩ := h07.1
    exact P1_inv h49 hd hz hsq hy hn hx
  · exact P1_structure h49 hd hz h07 h08 h09 h10 (card_P1 h49 hd hz h07 h08 h09 h10) hcomm
      (Pe10_le_Kc h49 hd hz h07 h08 h09 h10) fun y hy => by
        obtain ⟨v, hvK, -, hgen⟩ := exists_v h49 hd hz h07 h08 h09 h10 hy
        exact ⟨v, hvK, hgen⟩

end Final

end CFSG.LocalAnalysis.EvenBN.Tits.N.Nd11

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

section Step11

variable {G : Type} [Group G] [Finite G]

theorem step11_holds : Step11 := by
  intro G _ _ d z₀ h49 hd hz _h05 h07 h08 h09 h10
  exact Nd11.node11_of_nodes h49 hd hz h07 h08 h09 h10

end Step11

end CFSG.LocalAnalysis.EvenBN.Tits.N
