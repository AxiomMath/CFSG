module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A2V2

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_E_le_M4 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) : c.s.fr.E ≤ M4 c.e := by
  have h := c.y7acfg hH
  intro x hx
  refine Subgroup.mem_inf.mpr ⟨(y56_C4_cand c.toCtx5 hH).1 (Subgroup.mem_sup_left hx), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact (y6_C0_comm h.cfg x (s3_E_le_A c.s hx) w (y7a_V_le_C0 h hw)).symm

theorem y7a_E_inf_V2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : c.s.fr.E ⊓ V2 c.e = cen c.s.fr.B := by
  apply le_antisymm
  · intro x hx
    rw [← y7a_V2_inf_A c hH hF h71]
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hx).2, s3_E_le_A c.s (Subgroup.mem_inf.mp hx).1⟩
  · exact le_inf (y56_V_le_E hH) (y7a_cenB_le_V2 c hH hF h71)

private lemma y7a_E_elemAbelian {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsElemAbelian 2 s.fr.E :=
  ⟨⟨⟨fun a b => Subtype.ext (y56_E_comm hH a a.2 b b.2)⟩⟩, y56_E_sq hH⟩

private lemma y7a_E_V2_comm (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : ∀ e ∈ c.s.fr.E, ∀ v ∈ V2 c.e, e * v = v * e := fun e he v hv =>
  (((y7a_V2_mem_iff c hH hF h71 v).mp hv).2.1 e he).symm

theorem y7a_U_elemAbelian (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : IsElemAbelian 2 (c.s.fr.E ⊔ V2 c.e) :=
  y7a_isElemAbelian_sup (y7a_E_elemAbelian hH)
    ((y7a_M3_elemAbelian c hH).mono inf_le_left) (y7a_E_V2_comm c hH hF h71)

theorem y7a_card_U (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    (h71 : c.Fact71) : Nat.card ↥(c.s.fr.E ⊔ V2 c.e) = 32 := by
  have h := y7a_card_sup_mul_inf (y7a_E_V2_comm c hH hF h71)
  have hE : Nat.card ↥c.s.fr.E = 8 := by
    have := (y56_E_isE3 hH).2
    norm_num at this
    exact this
  rw [y7a_E_inf_V2 c hH hF h71, y54_V_card hH, (y7a_V2_data c hH hF h71).1, hE] at h
  omega

theorem y7a_U_le_M4 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) :
    c.s.fr.E ⊔ V2 c.e ≤ M4 c.e :=
  sup_le (y7a_E_le_M4 c hH) inf_le_right

end CFSG.OddStandard.HigherRank.YamadaG23
