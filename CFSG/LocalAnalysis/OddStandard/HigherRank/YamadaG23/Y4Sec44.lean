module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Sec42
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4P2c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Core

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_no_extremal (c : Ctx4 s e) (h42 : IsSylowIn 2 (⊤ : Subgroup G) s.T₂) {x : G}
    (hx : IsExtremalConj s.T₂ s.t x) : x ∉ y4S2 s := by
  intro hxS
  have hxM : x ∈ M2 s := y4_S2_extremal_mem_M2 c hx hxS
  have hcard : 8 ≤ Nat.card ↥(centEl s.fr.B x) := y4_extremal_cent_B c hx
  have hxL : x ∉ L := y4_conj_t_not_mem_L c.toF33 hx.2.1
  have hxB : x ∉ s.fr.B := fun h => hxL (f3_B_le_L s h)
  by_cases hxF : x ∈ normalizer (s.fr.F : Set G)
  · have hxT : x ∈ s.T := y4_normT2_F c h42 x hx.1 hxF
    have hxC : x ∈ s.C₂ := y4_M2_le_C2 c.toF33 hxM
    have hxP : x ∈ f3P s := by
      rw [← f3_T_inf_C₂ c.toF33]
      exact ⟨hxT, hxC⟩
    exact hxB (by rw [← y4_M2_inf_P c]; exact ⟨hxM, hxP⟩)
  · exact y4_core_false c hxM hxB (y4_conj_t_mul_self hx.2.1) hxF hcard

theorem sec44_of (hB : Sec3Inputs) : Sec44 := by
  intro G _ _ L hS hL s e hBr
  have c : Ctx4 s e := ctx4_of hB hS hL s e hBr
  have h42 : IsSylowIn 2 (⊤ : Subgroup G) s.T₂ := sec42_of hB G L hS hL s e hBr
  exact ⟨y4S2 s, y4_S2_le_T2 c, y4_S2_secProp c h42, fun x hx => y4_no_extremal c h42 hx⟩

end CFSG.OddStandard.HigherRank.YamadaG23
