module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBrBasic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitGam

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {Gh Zh Ah : Subgroup Γ} {t : Γ}

theorem lit_gam_of_hyps (hZG : Zh ≤ Gh) (hZc : ∀ x ∈ Gh, ∀ z ∈ Zh, x * z = z * x)
    (hZ4 : Nonempty (↥Zh ≃* Multiplicative (ZMod 4))) (hZA : Zh ≤ Ah) (hAG : Ah ≤ Gh)
    (hrel : Zh.relIndex Ah = 16) (hcomm : ∀ a ∈ Ah, ∀ b ∈ Ah, ⁅a, b⁆ ∈ Zh)
    (hsyl : IsSylowIn 2 (Gh ⊓ centralizerSection Ah Zh) Ah) (ht : orderOf t = 2)
    (ht1 : t ∈ normalizer (Gh : Set Γ)) (ht2 : t ∈ normalizer (Zh : Set Γ))
    (h5a : Ah ≤ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
    (h5b : Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ≤ normalizer (Ah : Set Γ))
    (h7 : ∀ n ∈ normIn Gh Ah, ∃ m ∈ normIn Gh Ah, ∃ c ∈ Gh ⊓ centralizerSection Ah Zh,
      n = m * c ∧ ⁅m, t⁆ ∈ Ah) :
    LitGam Gh Zh Ah t := by
  have hcardZh : Nat.card Zh = 4 := by
    obtain ⟨e⟩ := hZ4
    calc Nat.card Zh = Nat.card (Multiplicative (ZMod 4)) := Nat.card_congr e.toEquiv
      _ = 4 := Nat.card_zmod 4
  have hcardSub : Nat.card (Zh.subgroupOf Ah) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv, hcardZh]
  have hindex : (Zh.subgroupOf Ah).index = 16 := hrel
  have hcardA : Nat.card Ah = 64 := by
    have hcard := Subgroup.card_mul_index (Zh.subgroupOf Ah)
    rw [hcardSub, hindex] at hcard
    norm_num at hcard
    exact hcard.symm
  exact ⟨hZG, hZc, hZA, hAG, hcardA, hcomm, hsyl, ht, ht1, ht2, h5a, h5b, h7⟩

theorem lit_ctx_of_hyps [(Zh.subgroupOf Gh).Normal] (h : LitGam Gh Zh Ah t)
    (hZ4 : Nonempty (↥Zh ≃* Multiplicative (ZMod 4))) (hsq : ∀ a ∈ Ah, a ^ 2 ∈ Zh)
    (heven : Even ((normIn Gh Ah).relIndex Gh)) :
    LitCtx (Zh.subgroupOf Gh) (Ah.subgroupOf Gh) := by
  have hcardZh : Nat.card Zh = 4 := by
    obtain ⟨e⟩ := hZ4
    calc Nat.card Zh = Nat.card (Multiplicative (ZMod 4)) := Nat.card_congr e.toEquiv
      _ = 4 := Nat.card_zmod 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz x
    exact Subtype.ext (h.Z_central x.1 x.2 z.1 hz).symm
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Z_le_G).toEquiv, hcardZh]
  · exact Subgroup.subgroupOf_mono Gh h.Z_le_A
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.A_le_G).toEquiv, h.card_A]
  · intro a ha b hb
    have h1 : ⁅(a : Γ), (b : Γ)⁆ ∈ Zh := h.comm_mem a.1 ha b.1 hb
    rw [Subgroup.mem_subgroupOf]
    change ⁅(a : Γ), (b : Γ)⁆ ∈ Zh
    exact h1
  · intro a ha
    have h1 : (a : Γ) ^ 2 ∈ Zh := hsq a.1 ha
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact h1
  · have hlit : litC (Zh.subgroupOf Gh) (Ah.subgroupOf Gh)
        = (Gh ⊓ centralizerSection Ah Zh).subgroupOf Gh :=
      lit_litC_eq h.Z_central h.A_le_G
    rw [hlit,
      Subgroup.relIndex_subgroupOf (H := Ah) (K := Gh ⊓ centralizerSection Ah Zh) (L := Gh)
        inf_le_left]
    exact h.sylow.2.2
  · have hnorm : normalizer ((Ah.subgroupOf Gh : Subgroup ↥Gh) : Set ↥Gh)
        = (normIn Gh Ah).subgroupOf Gh := lit_normalizer_eq h.A_le_G
    rw [hnorm]
    exact heven

end CFSG.OddStandard.HigherRank.YamadaG23
