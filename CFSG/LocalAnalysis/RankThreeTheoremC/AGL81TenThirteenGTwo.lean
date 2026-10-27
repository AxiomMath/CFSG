module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeListOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenBlock
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalFrob
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcCensus
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeNormalRank
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

@[expose] def KFactG28AutCard : Prop :=
  ∀ (Y : Type) [Group Y], IsCaseIThreeG28 Y → Nat.card (MulAut Y) = 3 ^ 6 * 17816092672

theorem kFactG28AutCard_holds :
    KFactG28AutCard := by
  intro Y _ hY
  obtain ⟨d, hd, ⟨e⟩⟩ := hY
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  subst hd1
  obtain ⟨F, _, _, hFchar, hF⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.exists_field_card q.p q.exponent
      q.prime_p q.exponent_pos
  haveI : CharP F 2 := by rw [← hqp]; exact hFchar
  have hF8 : Nat.card F = 8 := by rw [hF, hqp, hqe]; norm_num
  obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv F
    (by rw [hF, TauCeti.PrimePower.card_def])
  let eA : CFSG.Blueprint.AdjointQuotient .G2 F ≃*
      CFSG.Blueprint.Chevalley.adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot
  let eY : Y ≃* CFSG.Blueprint.Chevalley.adjointGroup .G2 F := e.trans (b.symm.trans eA)
  calc Nat.card (MulAut Y)
      = Nat.card (MulAut (CFSG.Blueprint.Chevalley.adjointGroup .G2 F)) :=
        Nat.card_congr (MulAut.congr eY).toEquiv
    _ = 3 * Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .G2 F) :=
        CFSG.AGLEmbedding.KFactProofs.G28.card_aut hF8
    _ = 3 * (3 ^ 5 * 17816092672) := by
        rw [CFSG.AGLEmbedding.KFactProofs.G28.card_X' hF8]
    _ = 3 ^ 6 * 17816092672 := by norm_num

variable {G : Type} [Group G] [Finite G]

theorem relIndex_d1PlusCore_dvd_card_mulAut {p : ℕ} {H : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hK : K.Normal) :
    (d1PlusCore p H K).relIndex H ∣ Nat.card (MulAut K) := by
  classical
  haveI := hK
  let π : H →* (H ⧸ primeComplementCore (G := H) p) :=
    QuotientGroup.mk' (primeComplementCore (G := H) p)
  let φ : H →* MulAut K := (MulAut.conjNormal (H := K)).comp π
  have hker : φ.ker = (d1PlusCore p H K).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, d1PlusCore, Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨x, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hx' : π x ∈ (MulAut.conjNormal (H := K)).ker := by
        rw [MonoidHom.mem_ker]
        exact hx
      rwa [CFSG.BenderSuzuki.External.conjNormal_ker_eq_centralizer (H := K)] at hx'
    · rintro ⟨y, hy, hxy⟩
      rw [Subgroup.mem_comap] at hy
      have hyx : y = x := H.subtype_injective hxy
      subst hyx
      rw [show φ y = MulAut.conjNormal (H := K) (π y) from rfl, ← MonoidHom.mem_ker]
      rwa [CFSG.BenderSuzuki.External.conjNormal_ker_eq_centralizer (H := K)]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  exact Subgroup.card_subgroup_dvd_card φ.range

theorem false_of_g28 (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h984 : AGL81NineEightFour G) (h94 : AGL81NineFourCfg G) (hSU : KFactBlockNoSU38)
    (hG28 : KFactG28RankNotNineFour) (hAut : KFactG28AutCard) (hS : Setting G)
    {P : Sylow 3 G} {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hd : AGL81CfgData 3 P M H Q K) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {I₀ : Subgroup G} (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hI : IsTwoPrimeComponent I₀ I₀)
    (hN : H ⊓ L ≤ normalizer (I₀ : Set G)) (hK : IsCaseIThreeG28 K)
    {dJ : TauCeti.ValidLieTypeIndex} (hdJ : IsUThreeEightIndex dJ) (f : I₀ →* CatGroup dJ)
    (hf : Function.Surjective f) : False := by
  rcases blockL28Hyps_of_cfg h85 h93 hD2 h984 hS hd hL with
    ⟨hKgrp, hAsc, -, hNine, hNotX, hNotSylow⟩
  have hInner : BlockInnerHyp M (pCoreOf 2 H) L :=
    blockInnerHyp_of_cfg h84 h86 hD2 h984 hS hd hL
  have hI₀M : I₀ ≤ M := hI₀.le.trans (le_trans inf_le_right hL.le)
  have hbar : barM M I₀ ≤ blockParabolic M (pCoreOf 2 H) L :=
    barM_le_blockParabolic_of_cfg h984 hS hd hI₀.le
  have hnorm : blockParabolic M (pCoreOf 2 H) L ≤
      Subgroup.normalizer ((barM M I₀ ⊔ ⊥ : Subgroup _) : Set _) := by
    simpa using blockParabolic_le_normalizer_barM_of_cfg h984 hS hd hL.le hN
  have hPL : 3 ^ 7 ∣ Nat.card (blockParabolic M (pCoreOf 2 H) L) :=
    hSU G M (pCoreOf 2 H) L hKgrp hAsc hL hNine hNotX hNotSylow hInner
      ⊥ I₀ hI₀M bot_le hbar (by rw [Subgroup.normalizer_eq_top]; exact le_top)
      (by rw [Subgroup.card_bot]; norm_num) hnorm hI.perfect dJ f hdJ hf
  have hPLH : Nat.card (blockParabolic M (pCoreOf 2 H) L) ∣ Nat.card H :=
    card_blockParabolic_dvd_of_cfg h984 hS hd hL.le
  have h3H : 3 ^ 7 ∣ Nat.card H := hPL.trans hPLH
  obtain ⟨h2, hn⟩ := hG28 _ K hK
  have h3notX : ¬ 3 ∣ Nat.card (d1PlusCore 3 H K) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree.not_three_dvd_card_plusCore
      h94 hS hd h2 hn
  have hKnormal : K.Normal := by
    obtain ⟨H₁, R₁, he⟩ := hd.escape
    rw [hd.kbar]
    exact d1KBar_normal_of_escape he hd.base hd.le_H
      (fun h => hd.not_le_X0 (by rw [hd.kbar, h]; exact bot_le))
  have hrel : (d1PlusCore 3 H K).relIndex H ∣ Nat.card (MulAut K) :=
    relIndex_d1PlusCore_dvd_card_mulAut hKnormal
  have hrel' : (d1PlusCore 3 H K).relIndex H ∣ 3 ^ 6 * 17816092672 := by
    rwa [hAut K hK] at hrel
  have hXH : d1PlusCore 3 H K ≤ H := Subgroup.map_subtype_le _
  have hcardX : (d1PlusCore 3 H K).relIndex H * Nat.card (d1PlusCore 3 H K) =
      Nat.card H := by
    have h := Subgroup.relIndex_mul_card (d1PlusCore 3 H K) H
    rwa [inf_eq_left.mpr hXH] at h
  have hcop : Nat.Coprime (3 ^ 7) (Nat.card (d1PlusCore 3 H K)) :=
    (Nat.prime_three.coprime_pow_of_not_dvd h3notX).symm
  have h37rel : 3 ^ 7 ∣ (d1PlusCore 3 H K).relIndex H := by
    apply hcop.dvd_of_dvd_mul_right
    rwa [hcardX]
  exact (by norm_num : ¬ 3 ^ 7 ∣ 3 ^ 6 * 17816092672) (h37rel.trans hrel')

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
