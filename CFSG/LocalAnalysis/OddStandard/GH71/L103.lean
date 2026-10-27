module

public import CFSG.LocalAnalysis.OddStandard.GH71.Bar3
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Coprime
public import CFSG.LocalAnalysis.OddStandard.GH71.CoversTransfer

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem normalizer_ne_top (h : Ctx71 G z S U u) {Q : Subgroup G} (hQ3 : IsPGroup 3 ↥Q)
    (hQ1 : Q ≠ ⊥) : normalizer (Q : Set G) ≠ ⊤ := by
  have := h.simple
  intro htop
  rcases (normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with hb | ht
  · exact hQ1 hb
  · exact ne_top_of_isPGroup_three h.orderOf_z hQ3 ht

theorem lemma_10_3 (h : Ctx71 G z S U u) (hB0 : SpecB0) (hB1 : SpecB1) (hB2 : SpecB2)
    (h812 : IVK_8_12_ly) {Q₁ : Subgroup G}
    (hQ₁ : Open.fusionIsSylowIn 3 Q₁ (pPrimeCoreOf 2 (normalizer (U : Set G))))
    (hSQ₁ : S ≤ normalizer (Q₁ : Set G)) (hQ₁1 : Q₁ ≠ ⊥) :
    ∃ Q, MaxSInv 3 S ⊤ Q ∧ Q₁ ≤ Q ∧
      Covers (normalizer (Q : Set G)) (normalizer (U : Set G))
        (pPrimeCoreOf 2 (normalizer (U : Set G))) := by
  set N := normalizer (U : Set G) with hN
  set ON := pPrimeCoreOf 2 N with hON
  set 𝒬 : Set (Subgroup G) := {Q | IsPGroup 3 ↥Q ∧ S ≤ normalizer (Q : Set G) ∧ Q₁ ≤ Q ∧
    Covers (normalizer (Q : Set G)) N ON} with h𝒬
  have hQ₁𝒬 : Q₁ ∈ 𝒬 := ⟨hQ₁.2.1, hSQ₁, le_rfl,
    covers_frattini Nat.prime_three (pPrimeCoreOf_le' N) (le_normalizer_pPrimeCoreOf' N)
      (odd_card_pPrimeCoreOf' N) hQ₁⟩
  obtain ⟨Q, hQ𝒬, hQmax⟩ :=
    Set.exists_max_image 𝒬 (fun Q => Nat.card Q) (Set.toFinite 𝒬) ⟨Q₁, hQ₁𝒬⟩
  obtain ⟨hQ3, hSQ, hQ₁Q, hQcov⟩ := hQ𝒬
  set H := normalizer (Q : Set G) with hHdef
  have hQ1 : Q ≠ ⊥ := fun hb => hQ₁1 (le_bot_iff.mp (hb ▸ hQ₁Q))
  have hH : H ≠ ⊤ := h.normalizer_ne_top hQ3 hQ1
  have hSH : S ≤ H := hSQ
  obtain ⟨P, hP, hQP⟩ := exists_maxSInv_above (le_normalizer : Q ≤ H) hQ3 hSQ
  have hQO : Q ≤ pPrimeCoreOf 2 H :=
    le_pPrimeCoreOf_of_odd le_normalizer (odd_card_of_isPGroup_three hQ3) le_rfl
  have hONC : ON ≤ centralizer (U : Set G) := by
    rw [hON, h.pPrimeCoreOf_normalizer_U]; exact pPrimeCoreOf_le' _
  have hPO : P ≤ pPrimeCoreOf 2 H := by
    by_contra hPO
    have hcard : Nat.card (barIn H P) = 3 := h.card_barIn_of_ivk h812 hH hSH hP hPO
    apply h.not_inf_centralizer_U_le hB0 hSH hP.1 hP.2.2.1 hcard
    have hCU : P ⊓ centralizer (U : Set G) ≤ ON := by
      rw [hON, h.pPrimeCoreOf_normalizer_U]
      refine h.le_pPrimeCoreOf_centralizer_U hB1 hB2 inf_le_right (hP.2.1.to_le inf_le_left) ?_
      intro s hs
      exact inf_normalizer_le_normalizer_inf
        ⟨hP.2.2.1 hs, normalizer_le_normalizer_centralizer U (h.U_norm hs)⟩
    have hQ₁le : Q₁ ≤ P ⊓ centralizer (U : Set G) :=
      le_inf (hQ₁Q.trans hQP) (hQ₁.1.trans hONC)
    have heq := hQ₁.2.2 _ hCU (hP.2.1.to_le inf_le_left) hQ₁le
    rw [heq]
    exact hQ₁Q.trans hQO
  have hPsyl : Open.fusionIsSylowIn 3 P (pPrimeCoreOf 2 H) :=
    L121.sylowIn_of_maxSInv h.S2 hP (pPrimeCoreOf_le' H) hPO
      (not_two_dvd_of_odd (odd_card_pPrimeCoreOf' H)) (hSH.trans (le_normalizer_pPrimeCoreOf' H))
  have hcov₁ : Covers (normalizer (P : Set G)) H (pPrimeCoreOf 2 H) :=
    covers_frattini Nat.prime_three (pPrimeCoreOf_le' H) (le_normalizer_pPrimeCoreOf' H)
      (odd_card_pPrimeCoreOf' H) hPsyl
  have hU2 : IsPGroup 2 ↥U := h.S2.to_le h.U_le
  have hcovN : Covers (normalizer (P : Set G)) N ON :=
    covers_transfer hU2 (h.U_le.trans hSH) (h.U_le.trans hP.2.2.1) hQcov hcov₁
  have hP𝒬 : P ∈ 𝒬 := ⟨hP.2.1, hP.2.2.1, hQ₁Q.trans hQP, hcovN⟩
  have hPQ : Q = P := eq_of_le_of_card_ge hQP (hQmax P hP𝒬)
  refine ⟨Q, ⟨le_top, hQ3, hSQ, fun W _ hW3 hSW hQW => ?_⟩, hQ₁Q, hQcov⟩
  by_contra hne
  have hlt : Q < W := lt_of_le_of_ne hQW (Ne.symm hne)
  have h1 := lt_inf_normalizer_of_lt Nat.prime_three hW3 hlt
  have h2 := hP.2.2.2 (W ⊓ H) inf_le_right (hW3.to_le inf_le_left)
    (fun s hs => inf_normalizer_le_normalizer_inf ⟨hSW hs, le_normalizer (hSH hs)⟩)
    (by rw [← hPQ]; exact h1.le)
  rw [← hPQ] at h2
  exact h1.ne h2.symm

end Ctx71

end CFSG.OddStandard.GH71
