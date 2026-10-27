module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4S2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4P2b

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

theorem y4_S2_extremal_mem_M2 (c : Ctx4 s e) {x : G} (hx : IsExtremalConj s.T₂ s.t x)
    (hxS : x ∈ y4S2 s) : x ∈ M2 s := by
  by_contra hxM
  have hnot : ∃ v ∈ cen s.fr.B, x * v * x⁻¹ ≠ v := y4_S2_moves_V c hxS hxM
  have hB : Nat.card ↥(centEl s.fr.B x) ≤ 8 := y4_card_centB_le c hnot
  have hM2 : Nat.card ↥(centEl (M2 s) x) ≤ 2 * Nat.card ↥(centEl s.fr.B x) :=
    y4_card_centM2_le c hxS hxM
  have hthis : y4S2 s ⊓ M2 s = M2 s := by
    rw [y4S2, inf_eq_right.mpr (le_sup_left : M2 s ≤ M2 s ⊔ s.fr.S)]
  have hinf : centEl (y4S2 s) x ⊓ M2 s = centEl (M2 s) x := by
    rw [centEl, centEl, inf_assoc, inf_comm (centralizer ({x} : Set G)),
      ← inf_assoc, hthis]
  have hle := y4_card_le_relIndex_mul (F := y4S2 s) (C := centEl (y4S2 s) x) (N := M2 s)
    inf_le_left (le_sup_left : M2 s ≤ y4S2 s)
  rw [hinf, y4_relIndex_M2_S2 c] at hle
  have hcp := y4_cp c.toF33 hx (y4_S2_le_T2 c)
  rw [y4_card_S2 c] at hcp
  omega

theorem y4_extremal_cent_B (c : Ctx4 s e) {x : G} (hx : IsExtremalConj s.T₂ s.t x) :
    8 ≤ Nat.card ↥(centEl s.fr.B x) := by
  have hM2T2 : M2 s ≤ s.T₂ := (y4_M2_le_C2 c.toF33).trans (y4_C2_le_T2 s)
  have hcp := y4_cp c.toF33 hx hM2T2
  rw [y4_card_M2 c] at hcp
  have hinf : centEl (M2 s) x ⊓ f3P s = centEl s.fr.B x := by
    rw [centEl, centEl, ← y4_M2_inf_P c]
    simp only [inf_assoc, inf_left_comm, inf_comm]
  have hle := y4_card_le_relIndex_mul (F := s.C₂) (C := centEl (M2 s) x) (N := f3P s)
    (fun y hy => y4_M2_le_C2 c.toF33 (Subgroup.mem_inf.mp hy).1) (f3_P_le_C₂ c.toF33)
  rw [hinf, f3_P_relIndex_C₂ c.toF33] at hle
  omega

end CFSG.OddStandard.HigherRank.YamadaG23
