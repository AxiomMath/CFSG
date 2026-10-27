module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrTau
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTHat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitTransport
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitGam

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {Gh Zh Ah : Subgroup Γ} {t : Γ}

private theorem lit_subgroupOf_inf (G H K : Subgroup Γ) :
    (H ⊓ K).subgroupOf G = H.subgroupOf G ⊓ K.subgroupOf G := by
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem lit_T_data [(Zh.subgroupOf Gh).Normal] (c : LitCtx (Zh.subgroupOf Gh) (Ah.subgroupOf Gh))
    (h : LitGam Gh Zh Ah t)
    (hT : IsQuotIso (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ⊓ (Gh ⊓ centralizerSection Ah Zh))
      ↥blockStab) :
    Group.IsSolvable ↥(litTSub (litConj Gh t h.t_G) (Zh.subgroupOf Gh)) ∧
      72 ∣ (litP (Zh.subgroupOf Gh)).relIndex
        (litTSub (litConj Gh t h.t_G) (Zh.subgroupOf Gh)) := by
  have eT : litTSub (litConj Gh t h.t_G) (Zh.subgroupOf Gh) =
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh).subgroupOf Gh :=
    lit_litTSub_eq h.Z_central h.Z_le_G h.t_G h.t_Z
  have hq : IsQuotIso ((Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh).subgroupOf Gh)
      (((Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh) ⊓
        (Gh ⊓ centralizerSection Ah Zh)).subgroupOf Gh) ↥blockStab :=
    lit_isQuotIso_subgroupOf (inf_le_left : Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ≤ Gh) hT
  have hC : (Gh ⊓ centralizerSection Ah Zh).subgroupOf Gh =
      litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) :=
    (lit_litC_eq h.Z_central h.A_le_G).symm
  have h2 : ((Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh) ⊓
        (Gh ⊓ centralizerSection Ah Zh)).subgroupOf Gh =
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh).subgroupOf Gh ⊓
        litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) := by
    rw [lit_subgroupOf_inf Gh (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
      (Gh ⊓ centralizerSection Ah Zh), hC]
  rw [h2] at hq
  have hT' : IsQuotIso (litTSub (litConj Gh t h.t_G) (Zh.subgroupOf Gh))
      (litTSub (litConj Gh t h.t_G) (Zh.subgroupOf Gh) ⊓
        litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh)) ↥blockStab := by
    rw [eT]; exact hq
  have hTN : litTSub (litConj Gh t h.t_G) (Zh.subgroupOf Gh) ≤
      normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh) := by
    intro x hx
    rw [lit_normalizer_eq h.A_le_G]
    rw [eT] at hx
    have hxTh : (x : Γ) ∈ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh := hx
    exact ⟨hxTh.1, h.five_b hxTh⟩
  exact ⟨lit_T_solvable c hT', lit_T_card c hTN hT'⟩

end CFSG.OddStandard.HigherRank.YamadaG23
