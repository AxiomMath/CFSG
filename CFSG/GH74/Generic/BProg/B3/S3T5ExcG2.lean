module

public import CFSG.GH74.Generic.S3.LyB2G2
public import CFSG.GH74.Generic.BProg.B3.S3SL2Depth
public import CFSG.GH74.GLS.C3.Layer1.Th2BalK10

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5X

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.Generic.S3 (G2Table blockData_of_l3 blockData_of_kcent d2_le_six_of_shapeS2)

theorem g2Table_of_depth (hF : GenericKnownFacts) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) (hkgh : KGH G)
    (hd : ∀ u : G, orderOf u = 2 → ∀ L : Subgroup (CentralizerBar u), IsComponent L →
      InG2 ↥L → 7 ≤ d2 ↥L) : G2Table G := by
  intro u hu L hL hG2
  have hsh := generic_shapes_of_inG2 hF hs hn hgen hkgh hu hG2
  have hle := hd u hu L hL hG2
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := S45.exists_noncomm_of_isQuasisimple hL.1
  rcases hsh with h1 | h2 | h3 | h4 | h5
  · exfalso
    have := d2_le_six_of_shapeS1 hL hG2 h1
    omega
  · exfalso
    have hZ : center ↥L ≠ ⊥ := by
      intro hbot
      have hmem : (⟨xbar u, h2.2⟩ : ↥L) ∈ center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_center_iff.1 (xbar_mem_center u) g)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact xbar_ne_one hu (congrArg Subtype.val hmem)
    have := d2_le_six_of_shapeS2 hL hG2 hZ h2
    omega
  · obtain ⟨⟨p, f, hp, hp2, -, hmodel⟩, hxL⟩ := h3
    exact ⟨hxL, center_eq_bot_of_quasisimple_lieModel_L3 hL.1 hmodel,
      blockData_of_l3 hp hp2 hmodel⟩
  · obtain ⟨⟨f, hmodel⟩, hxL⟩ := h4
    have hsimple : IsSimpleGroup ↥L := CFSG.Timmesfeld.isSimpleGroup_of_lieModel hmodel
    exact ⟨hxL, CFSG.GH74.Generic.S3.center_eq_bot_of_simple_nonab hsimple hnab,
      blockData_of_kcent (S45.kCent_of_isJ1OrRee (Or.inr ⟨f, hmodel⟩))⟩
  · obtain ⟨hJ1, hxL⟩ := h5
    have hsimple : IsSimpleGroup ↥L := by
      obtain ⟨e⟩ := hJ1
      exact (MulEquiv.isSimpleGroup_congr e).2 CFSG.Sporadic.J1.isSimpleGroup_J1
    exact ⟨hxL, CFSG.GH74.Generic.S3.center_eq_bot_of_simple_nonab hsimple hnab,
      blockData_of_kcent (S45.kCent_of_isJ1OrRee (Or.inl hJ1))⟩

theorem seven_le_d2 {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (h3G : 3 ≤ pRank 2 G) {x : G} {K : Subgroup G}
    (hc : IsJ2Circ x K) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) (u : G) (hu : orderOf u = 2)
    (L : Subgroup (CentralizerBar u)) (hL : IsComponent L) (hG2 : InG2 ↥L) : 7 ≤ d2 ↥L := by
  obtain ⟨⟨hILoK, hdepth, -⟩, -⟩ := hc
  have h7 : d2 (↥K ⧸ pPrimeCore 2 ↥K) = 7 := S3SL2Depth.d2_eq_seven_of_isL3OddGt3 hILoK.2 h3
  have hG7 : depthOfG G = 7 := by rw [← hdepth, h7]
  obtain ⟨W, hW, hWL⟩ := Th2.Bal.exists_pCompIn_over hL
  obtain ⟨e⟩ := Th2.Bal.kBar_equiv_of_over hW hWL
  have hILo : IsILo 2 u W :=
    ⟨hu, by simpa [oBound] using rankThreeCentralizers G hs hn h3G u hu, hW⟩
  have hG2W : InG2 (kBar W) := inG2_of_mulEquiv e.symm hG2
  have hle : depthOfG G ≤ d2 (kBar W) := Nat.sInf_le ⟨u, W, ⟨hILo, hG2W⟩, rfl⟩
  rw [d2_congr e] at hle
  omega

end S3T5X

end CFSG.GH74.Generic.BProg.B3
