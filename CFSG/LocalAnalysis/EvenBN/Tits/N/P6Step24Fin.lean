module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Step24
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Tail4
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Endgame

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Fin


theorem tail24_holds {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G} (h49 : d.Thm49Statement)
    (hd : d.Hyp) (_hz : d.S56Z0 z₀) (_h07 : Node07 d) (h10 : Node10 d z₀) (_h11 : Node11 d z₀)
    (_h12 : Node12 d z₀) (_h13 : Node13 d) (_h14 : Node14 d) (_h16 : Node16 d z₀)
    (h19 : Node19 d z₀) (h20 : Node20 d z₀) (h21 : Node21 d z₀) (_h22 : Node22 d z₀)
    (h23a : Node23a d z₀) (h23b : Node23b d z₀) (h23c : Node23c d z₀) : Tail24 d z₀ := by
  intro hV s y hsH hs2 hZs hyH _hys hy3 hyz hZ4 hcard
  have hx5H : d.x₅ ∈ Hg d := hd.s56_M_le_normalizer_V h49 hd.s56_x5_mem_M
  obtain ⟨hN, hq⟩ := h23a.2.2.2.2.1
  haveI := hN
  exact P6.tail_core d z₀ hx5H hd.s56_orderOf_x5 hV h10.2.2.1 h23a.2.1.1 h23a.2.1.2 h23a.2.2.1.1 hN
    (P6.relIndex_eq_two_or_six hq) h19.2.2.2.2.1 h19.2.2.2.2.2.2.1 h20.2.2.2.2.1
    (h21.1.imp (fun h => h.1) id) h21.2.2.1 h23b.1 h23c.1
    (fun s hs h2 hrel => (h23c.2 s hs h2 hrel).1) hsH hs2 hZs hyH hy3 hyz hZ4 hcard

theorem step24_holds : Step24 := step24_of_tail fun h49 hd hz h07 h10 h11 h12 h13 h14 h16 h19 h20 h21 h22
    h23a h23b h23c => tail24_holds h49 hd hz h07 h10 h11 h12 h13 h14 h16 h19 h20 h21 h22 h23a h23b h23c

end Fin

end CFSG.LocalAnalysis.EvenBN.Tits.N
