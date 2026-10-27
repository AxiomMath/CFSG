module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7B1a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54R
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y57D

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7b_M3_elem (c : Ctx7 G L) (hb : B5Std c) : IsElemAbelian 2 (M3 c.s) := by
  have hd : c.d ∈ M3 c.s := by
    have hmem : c.d ∈ V1 c.e := by
      rw [c.hV]
      exact Subgroup.subset_closure (by simp)
    exact hmem.2
  exact y57_caseA c.toCtx5 hb.hH hd

theorem y7b_card_M3 (c : Ctx7 G L) (hb : B5Std c) : Nat.card ↥(M3 c.s) = 2 ^ 6 := by
  have hF : c.s.fr.F ≤ M3 c.s := le_sup_right
  have hcard := Subgroup.relIndex_mul_card (H := c.s.fr.F) (K := M3 c.s)
  rw [inf_of_le_left hF, y54_M3_relIndex c.toCtx5 hb.hH, y7b_card_F hb.hH] at hcard
  norm_num at hcard ⊢
  omega

theorem y7b_V_le_V2 (c : Ctx7 G L) (hb : B5Std c) : cen c.s.fr.B ≤ V2 c.e := by
  rw [← y7b_E_inf_F hb.hH, V2]
  exact le_inf (inf_le_right.trans le_sup_right) (inf_le_left.trans (y7b_E_le_M4 c hb))

theorem y7b_H_inf_V2 (c : Ctx7 G L) (hb : B5Std c) : c.s.H ⊓ V2 c.e = cen c.s.fr.B := by
  rw [V2, inf_inf_distrib_left, y54_H_inf_M3 c.toCtx5 hb.hH, y7b_H_inf_M4 c hb, inf_comm,
    y7b_E_inf_F hb.hH]

theorem y7b_V2_elem (c : Ctx7 G L) (hb : B5Std c) : IsElemAbelian 2 (V2 c.e) := by
  have hle : V2 c.e ≤ M3 c.s := by
    rw [V2]
    exact inf_le_left
  obtain ⟨hcomm, hsq⟩ := y7b_M3_elem c hb
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun x hx => hsq x (hle hx)⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val
    (hcomm.is_comm.comm (⟨(a : G), hle a.2⟩ : ↥(M3 c.s)) ⟨(b : G), hle b.2⟩)

end CFSG.OddStandard.HigherRank.YamadaG23
