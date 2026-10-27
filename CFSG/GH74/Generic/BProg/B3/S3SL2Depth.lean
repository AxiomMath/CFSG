module

public import CFSG.GH74.Generic.JStar2Defs
public import CFSG.GH74.Generic.JMaxShapes
public import CFSG.GH74.Generic.BProg.Vocab

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup

namespace S3SL2Depth

theorem index_le_eight {K : Type} [Group K] {i : ℕ} (h : InG2Depth i K) : 1 ≤ i ∧ i ≤ 8 := by
  obtain ⟨-, h⟩ := h
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ <;> omega

theorem d2_eq_seven_of_isL3OddGt3 {Kt : Type} [Group Kt] (hG2 : InG2 Kt) (h : IsL3OddGt3 Kt) :
    d2 Kt = 7 := by
  obtain ⟨p, f, hp, hp2, hq, hmod⟩ := h
  have hlie : OfLieType Kt := ofLieType_of_lieModel_L3 hG2.1.1 hmod
  have hL3 : IsL3Odd Kt := ⟨p, f, hp, hp2, hmod⟩
  have h7 : InG2Depth 7 Kt := ⟨hG2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, p, f, hp, hp2, hq, hmod⟩))))))⟩
  refine le_antisymm (Nat.sInf_le h7) (le_csInf ⟨7, h7⟩ fun i hi => ?_)
  obtain ⟨-, hi⟩ := hi
  rcases hi with ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ | ⟨rfl, hn, -⟩ |
    ⟨rfl, -, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hlie hn
  · exact absurd hL3 hn
  · exact le_rfl
  · omega

end S3SL2Depth

section Depth

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem depth7_simple {x : G} {K : Subgroup G} (hc : IsJ2Circ x K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    {u : G} {W : Subgroup G} (hW : IsILo 2 u W) (hG2 : InG2 (↥W ⧸ pPrimeCore 2 ↥W)) :
    InG2Depth 7 (↥W ⧸ pPrimeCore 2 ↥W) ∨ InG2Depth 8 (↥W ⧸ pPrimeCore 2 ↥W) := by
  obtain ⟨⟨hILoK, hdepth, -⟩, -⟩ := hc
  have h7 : d2 (↥K ⧸ pPrimeCore 2 ↥K) = 7 := S3SL2Depth.d2_eq_seven_of_isL3OddGt3 hILoK.2 h3
  have hG7 : depthOfG G = 7 := by rw [← hdepth, h7]
  have hle : 7 ≤ d2 (↥W ⧸ pPrimeCore 2 ↥W) := by
    rw [← hG7]
    exact Nat.sInf_le ⟨u, W, ⟨hW, hG2⟩, rfl⟩
  have hpos : 0 < d2 (↥W ⧸ pPrimeCore 2 ↥W) := by omega
  have hne : {i : ℕ | InG2Depth i (↥W ⧸ pPrimeCore 2 ↥W)}.Nonempty := Nat.nonempty_of_pos_sInf hpos
  have hmem : InG2Depth (d2 (↥W ⧸ pPrimeCore 2 ↥W)) (↥W ⧸ pPrimeCore 2 ↥W) := Nat.sInf_mem hne
  have h8 := (S3SL2Depth.index_le_eight hmem).2
  have h78 : d2 (↥W ⧸ pPrimeCore 2 ↥W) = 7 ∨ d2 (↥W ⧸ pPrimeCore 2 ↥W) = 8 := by omega
  rcases h78 with h | h
  · exact Or.inl (h ▸ hmem)
  · exact Or.inr (h ▸ hmem)

end Depth

end CFSG.GH74.Generic.BProg.B3
