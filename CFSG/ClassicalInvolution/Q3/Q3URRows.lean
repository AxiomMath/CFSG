module

public import CFSG.ClassicalInvolution.Q3.Q3URClose
public import CFSG.ClassicalInvolution.Q3.Q3WARow
public import CFSG.ClassicalInvolution.Q3.Q3URDict

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSU
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank

theorem oddLieType_of_phanChain3U (h3 : OddThreeFreeInput) (hP : Phan3Rec) {m : ℕ} (hm : 2 ≤ m)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {K : Subgroup G} {z : G} (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 1 (CompData.model .PSU (m + 1)) (conjClass3 K) z)
    (hch : PhanChain3U K m) : CFSG.Blueprint.OddLieType G := by
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have hconn := (CoreAssembly.deltaConnected_iff K).mp hR.conn
  obtain ⟨hex, hP1⟩ := hR.setup
  have hK : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  obtain ⟨d⟩ := LocalShapeC3.nonempty_dictU hm hR.inClass hK hR.cls hshape
  obtain ⟨U, hUΩ, hcomm, hpair, htriple⟩ := hch
  let c : UCore3 m (conjClass3 K) K z :=
    { hm := hm, hΩ := hR.inClass, hex := hex, hK := hK, hz := hR.cls, hP1 := hP1,
      hO3 := h3 G K z hR, d := d }
  obtain ⟨-, -, -, -, hodd⟩ := c.typeU_of_chain hnab hP hsingle hconn U hUΩ hcomm hpair htriple
  exact hodd

theorem shapePiece3_psu_of_chain (h3 : OddThreeFreeInput) (hP : Phan3Rec) {m : ℕ} (hm : 2 ≤ m)
    (h : ChainRow3U m) : ShapePiece3 1 (CompData.model .PSU (m + 1)) := by
  intro G _ _ _ hnab K z hR hshape
  exact Or.inl (oddLieType_of_phanChain3U h3 hP hm hnab hR hshape (h G hnab K z hR hshape))

theorem piece3SU7_of_chain (h3 : OddThreeFreeInput) (hP : Phan3Rec)
    (h : ∀ m, 6 ≤ m → ChainRow3U m) : Piece3SU7 := by
  rintro a t n ⟨rfl, rfl, hn⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact shapePiece3_psu_of_chain h3 hP (by omega) (h m (by omega))

theorem piece3SUs_of_chain (h3 : OddThreeFreeInput) (hP : Phan3Rec) (h2 : ChainRow3U 2)
    (h3' : ChainRow3U 3) (h4 : ChainRow3U 4) : Piece3SUs := by
  rintro a t n ⟨rfl, rfl, hn3, hn5⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain rfl | rfl | rfl : m = 2 ∨ m = 3 ∨ m = 4 := by omega
  · exact shapePiece3_psu_of_chain h3 hP (by norm_num) h2
  · exact shapePiece3_psu_of_chain h3 hP (by norm_num) h3'
  · exact shapePiece3_psu_of_chain h3 hP (by norm_num) h4

end CFSG.ClassicalInvolution.Q3.Q3W
