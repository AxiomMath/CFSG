module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79x
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79c
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBDef

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_B_M3_isE (c : Ctx7 G L) (hb : B7Std c) : IsE 6 ↥(M3 c.s) :=
  y7c_isE_of_isElemAbelian (y7c_M3_elem c hb.hH hb.h5.2.2.2.2.2)
    (y7c_card_M3 c.toCtx5 hb.hH)

theorem y7c_X_ne_top (c : Ctx7 G L) (hb : B7Std c) : y7cX c.s ≠ ⊤ := by
  intro htop
  haveI : IsSimpleGroup G := hb.hH.hS.std.simple
  haveI : (M3 c.s).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases Subgroup.Normal.eq_bot_or_eq_top (M3 c.s) with hbot | htop'
  · have hcard := y7c_card_M3 c.toCtx5 hb.hH
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  · obtain ⟨a, b, hab⟩ := hb.hH.hS.std.nonab
    exact hab (y7c_M3_comm c hb a (by rw [htop']; trivial) b (by rw [htop']; trivial))

theorem y7c_B_kgroup (c : Ctx7 G L) (hb : B7Std c) :
    CFSG.SectionRank.IsKGroupCat (y7cGam c.s) := by
  have hX : CFSG.SectionRank.IsKGroupCat ↥(y7cX c.s) :=
    CFSG.GH74.GLS.isKGroupNative_of_kProper hb.hH.hS.std.kProper (y7c_X_ne_top c hb)
  exact CFSG.SectionRank.IsKGroupCat.quotient hX ((M3 c.s).subgroupOf (y7cX c.s))

theorem y7c_B_t_sq (c : Ctx7 G L) (hb : B7Std c) : y7cTC c hb ^ 2 = 1 := by
  rw [y7cTC, ← map_pow,
    show (⟨c.s.t, y7c_t_mem_X c hb⟩ : ↥(y7cX c.s)) ^ 2 = 1 from
      Subtype.ext (by simpa using y7c_t_sq c.s),
    map_one]

theorem y7c_B_t_ne (c : Ctx7 G L) (hb : B7Std c) : y7cTC c hb ≠ 1 := by
  intro h
  have htM : c.s.t ∈ M3 c.s :=
    (y7cPi_eq_one_iff c.s ⟨c.s.t, y7c_t_mem_X c hb⟩).mp h
  have htH : c.s.t ∈ c.s.H := by
    rw [Setting3.H]
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rfl)
  have htF : c.s.t ∈ c.s.fr.F := by
    rw [← y54_H_inf_M3 c.toCtx5 hb.hH]
    exact Subgroup.mem_inf.mpr ⟨htH, htM⟩
  exact hb.hH.h31.2.2.1 1 (by simpa using y54_F_le_L c.s htF)

theorem y7c_NLF_eq_JF {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn L s.fr.F = JF s := by
  have h := hH.hLF.fact18.2.2.2.2.2.2.1.1
  rw [f3_zL_eq_bot hH, sup_bot_eq] at h
  show normIn L s.fr.F = ⁅normIn L s.fr.F, normIn L s.fr.F⁆
  exact h

theorem y7c_F_le_JF {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.F ≤ JF s := by
  rw [← y7c_NLF_eq_JF hH]
  exact le_inf (y54_F_le_L s) Subgroup.le_normalizer

theorem y7c_S_le_JF {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.fr.S ≤ JF s := by
  rw [← y7c_NLF_eq_JF hH]
  exact y54_S_le_N hH

theorem y7c_JF_le_X (c : Ctx7 G L) (hb : B7Std c) : JF c.s ≤ y7cX c.s := by
  rw [y7cX, Subgroup.le_set_normalizer_iff]
  intro j hj m hm
  rw [← y7c_NLF_eq_JF hb.hH] at hj
  exact y54_N_norm_M3 c.toCtx5 hb.hH j (y54_NL_le_N hb.hH hj) m hm

theorem y7c_B_J_cent (c : Ctx7 G L) (hb : B7Std c) :
    ∀ j ∈ y7cJC c, j * y7cTC c hb = y7cTC c hb * j := by
  intro j hj
  rw [y7cJC, mem_y7cImg] at hj
  obtain ⟨x, hxJ, rfl⟩ := hj
  rw [y7cTC, ← map_mul, ← map_mul]
  exact congrArg (y7cPi c.s) (Subtype.ext (y7c_JF_comm_t c.s x hxJ))

end CFSG.OddStandard.HigherRank.YamadaG23
