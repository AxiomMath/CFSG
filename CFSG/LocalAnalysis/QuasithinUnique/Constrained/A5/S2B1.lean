module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S2A5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.S2 CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.AppC Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

namespace S2

theorem isSylow_sup_of_inf {R K : Subgroup G} (hR : IsPGroup 2 R)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) (h : IsSylowTwoOf (R ⊓ K) K) :
    IsSylowTwoOf R (K ⊔ R) := by
  rw [A4.isSylowTwoOf_iff_maximal]
  refine ⟨le_sup_right, hR, fun P hPH hP hRP => ?_⟩
  intro t ht
  have htH : t ∈ R ⊔ K := by rw [sup_comm]; exact hPH ht
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at htH
  obtain ⟨r, hr, k, hk, rfl⟩ := htH
  have hkP : k ∈ P := by
    have := P.mul_mem (P.inv_mem (hRP hr)) ht
    simpa using this
  have hmax := ((A4.isSylowTwoOf_iff_maximal).mp h).2.2 (P ⊓ K) inf_le_right (hP.to_inf_left)
    (le_inf (inf_le_left.trans hRP) inf_le_right)
  have hkR : k ∈ R := (hmax ⟨hkP, hk⟩).1
  exact R.mul_mem hr hkR

omit [Finite G] in
theorem L_le_normalizer_U : L ≤ Subgroup.normalizer (blockU L : Set G) :=
  fun _ hl => C1.mem_normalizer_blockU (Subgroup.le_normalizer hl)

omit [Finite G] in
theorem SI_le_normalizer_U : s2SI S L ≤ Subgroup.normalizer (blockU L : Set G) :=
  fun _ hs => C1.mem_normalizer_blockU (mem_normalizer_iff_cj.2 (Data.cj_SI_L hs))

namespace Ctx

variable {t : G} (c : Ctx T M H S L t)
include c

theorem isSylow_S_L : IsSylowTwoOf (S ⊓ L) L :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal c.data.cs.sylow c.data.cs.block.1.2.1
    c.data.cs.block.1.2.2

theorem pCoreH_le_SI : pCoreOf 2 H ≤ s2SI S L :=
  (GammaExtra.le_thompsonJ c.maxQ).trans
    ((C1GN.thompsonJ_le_baum S).trans c.R_le_SI)

theorem blockU_ne_bot : blockU L ≠ ⊥ := by
  have h := c.data
  have hZ : blockZ L = ⊥ := AppC.blockZ_eq_bot_of_alt5 h.isShort h.alt5
  have := h.isShort.2.2.2.2.1
  rw [hZ] at this
  exact bot_lt_iff_ne_bot.1 this

theorem isPGroup_U : IsPGroup 2 ↥(blockU L) :=
  c.isPGroup_S.to_le (c.u₁R.trans (C1GN.baum_le S))

theorem pCore_LSI_ne_bot : pCoreOf 2 (L ⊔ s2SI S L) ≠ ⊥ := by
  intro hbot
  apply c.blockU_ne_bot
  have : blockU L ≤ pCoreOf 2 (L ⊔ s2SI S L) :=
    le_pCoreOf_of_normalizes (C1GN.blockU_le_self L |>.trans le_sup_left)
      (sup_le L_le_normalizer_U SI_le_normalizer_U) c.isPGroup_U
  rw [hbot] at this
  exact le_bot_iff.1 this

theorem LSI_le_H : L ⊔ s2SI S L ≤ H :=
  sup_le (C56.le_H c.data.cs) (s2SI_le_S.trans c.data.cs.sylow.1)

theorem LSI_charTwo : CharTwo (L ⊔ s2SI S L) :=
  charTwo_of_pCore_centralizer_le c.data.cs.charTwo c.LSI_le_H
    (inf_le_left.trans (c.pCoreH_le_SI.trans le_sup_right))

theorem LSI_gamma : IsGamma M (L ⊔ s2SI S L) :=
  ⟨c.pCore_LSI_ne_bot, s2SI S L, L ⊔ s2SI S L,
    ⟨c.SI_conf, le_sup_right, c.pCore_LSI_ne_bot, c.LSI_charTwo,
      fun hle => c.data.cs.not_le (le_sup_left.trans hle)⟩, le_rfl⟩

theorem local_SI : quasithinIsLocal (s2SI S L) L := by
  have h := c.data
  have hSIL : s2SI S L ⊓ L = S ⊓ L := by
    ext x
    constructor
    · rintro ⟨⟨hxS, -⟩, hxL⟩
      exact ⟨hxS, hxL⟩
    · rintro ⟨hxS, hxL⟩
      exact ⟨⟨hxS, Subgroup.le_normalizer hxL⟩, hxL⟩
  have hsyl : IsSylowTwoOf (s2SI S L) (L ⊔ s2SI S L) := by
    apply isSylow_sup_of_inf c.isPGroup_SI Data.SI_le_normalizer_L
    rw [hSIL]
    exact c.isSylow_S_L
  have hLn : L ≤ L ⊔ s2SI S L := le_sup_left
  have hN : (L.subgroupOf (L ⊔ s2SI S L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLn).mpr
      (sup_le Subgroup.le_normalizer Data.SI_le_normalizer_L)
  have hsub : IsSubnormal L (L ⊔ s2SI S L) := A3.subnormal_of_normal hLn hN
  have hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    h.isShort.2.2.2.1.resolve_right (L238.card_ne_three_of_isAltType le_rfl h.alt5)
  exact ⟨c.isPGroup_SI, C1GN.mem_cComp_of_short h.isShort hq hsub, hsyl.2.2, c.pCore_LSI_ne_bot⟩

end Ctx

end S2

end CFSG.QuasithinUnique.A5
