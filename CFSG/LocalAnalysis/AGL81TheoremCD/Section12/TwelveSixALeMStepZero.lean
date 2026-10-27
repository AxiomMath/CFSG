module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvariantX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPGen
import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSetup

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKCtx.V_inf_relPPrimeCore_eq_bot
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) : D.V ⊓ relPPrimeCore p H = ⊥ := by
  have hVX := hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
    (D.centralizer_le₃ hc) (D.t₁_mem hc.data) (D.t₂_mem hc.data) (D.t₃_mem hc.data)
  exact le_bot_iff.mp ((inf_le_inf le_rfl
    (relPPrimeCore_le_xSub hc.ctx.p_prime M H)).trans hVX.le)

private theorem ne_bot_inf_of_isSylowOf_of_three_dvd {O P S : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S P) (hOP : O ≤ P)
    (hPN : P ≤ Subgroup.normalizer (O : Set G)) (hdvd : 3 ∣ Nat.card O) :
    S ⊓ O ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSylO : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ O) O :=
    hSyl.inf_of_le_normalizer hOP hPN
  have hk : 0 < (Nat.card O).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hdvd
  intro hbot
  have h1 : 3 ^ (Nat.card O).factorization 3 = 1 := by
    rw [← hSylO.card_eq, hbot, Subgroup.card_bot]
  have h2 : 3 ≤ 3 ^ (Nat.card O).factorization 3 :=
    Nat.le_self_pow (Nat.pos_iff_ne_zero.mp hk) 3
  omega

private theorem exists_order_three_centralizing_of_isSylowOf {O P S : Subgroup G}
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 S P) (hOP : O ≤ P)
    (hPN : P ≤ Subgroup.normalizer (O : Set G)) (hdvd : 3 ∣ Nat.card O) :
    ∃ r ∈ S ⊓ O, (∀ s ∈ S, s * r = r * s) ∧ orderOf r = 3 :=
  exists_central_order_three_of_le_normalizer hSyl.isPGroup inf_le_left
    ((le_inf Subgroup.le_normalizer (hSyl.le.trans hPN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
    (ne_bot_inf_of_isSylowOf_of_three_dvd hSyl hOP hPN hdvd)

private theorem not_three_dvd_card_of_isElemAbelian_e27 {V O : Subgroup G}
    (hE : IsElemAbelian 3 V) (hVcard : Nat.card V = 27) (hVO : V ⊓ O = ⊥)
    (hPN : V ⊔ O ≤ Subgroup.normalizer (O : Set G)) (hVM : V ≤ M) (hOM : O ≤ M)
    (h3 : CFSG.Open.pRank 3 M ≤ 3) : ¬ 3 ∣ Nat.card O := by
  intro hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hSyl, hVS⟩ := exists_isSylowOf_ge (p := 3) (Q := V) (K := V ⊔ O) le_sup_left
    (CFSG.Open.IsElemAbelian.isPGroup hE)
  obtain ⟨r, hrS, hrcent, hrord⟩ :=
    exists_order_three_centralizing_of_isSylowOf hSyl le_sup_right hPN hdvd
  have hrO : r ∈ O := (Subgroup.mem_inf.mp hrS).2
  have hrnotV : r ∉ V := by
    intro hrV
    have h1 : r ∈ (⊥ : Subgroup G) := by
      rw [← hVO]
      exact Subgroup.mem_inf.mpr ⟨hrV, hrO⟩
    rw [Subgroup.mem_bot] at h1
    have h2 : orderOf r = 1 := by rw [h1, orderOf_one]
    omega
  have hrpow : r ^ 3 = 1 := by
    have h := pow_orderOf_eq_one r
    rwa [hrord] at h
  have hVcard3 : Nat.card V = 3 ^ 3 := by
    rw [hVcard]
    norm_num
  have hrcomm : ∀ v ∈ V, v * r = r * v := fun v hv => hrcent v (hVS hv)
  obtain ⟨hE', hEcard⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_sup_zpowers_of_card (p := 3) Nat.prime_three
      (E := V) hE (k := 3) hVcard3 hrpow hrnotV hrcomm
  have hEM : V ⊔ Subgroup.zpowers r ≤ M :=
    sup_le hVM (Subgroup.zpowers_le.mpr (hOM hrO))
  have h4 : 4 ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEM hE' (k := 4) (by rw [hEcard])
  omega

theorem TwelveSixKCtx.not_three_dvd_card_relPPrimeCore
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) :
    ¬ 3 ∣ Nat.card (relPPrimeCore p H) := by
  intro hdvd
  have hOH : relPPrimeCore p H ≤ H := relPPrimeCore_le (p := p) H
  have hON : H ≤ Subgroup.normalizer (relPPrimeCore p H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp
      (relPPrimeCore_normal hc.ctx.p_prime H)
  have hVH : D.V ≤ H := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_left
  have hVM : D.V ≤ M := (D.V_le.trans (D.sup_le hc.data)).trans inf_le_right
  exact not_three_dvd_card_of_isElemAbelian_e27 D.cfg.elem D.cfg.card
    (hc.V_inf_relPPrimeCore_eq_bot D) (sup_le (hVH.trans hON) (hOH.trans hON)) hVM
    (relPPrimeCore_le_M_of_twelveCtx hc.ctx) hc.h3 hdvd

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
