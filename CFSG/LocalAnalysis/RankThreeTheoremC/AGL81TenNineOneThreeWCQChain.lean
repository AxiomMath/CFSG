module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaChain
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeG28Center
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeGammaBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeCfgHolds
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineOneThreeProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeG28Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers
open Subgroup
open TenNineOneThree (IsWClosedIn GammaZeroIn)

variable (G : Type) [Group G] [Finite G]

@[expose] noncomputable def agl81QHat (H Q' : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) [K.Normal] :
    Subgroup (MulAut.conjNormal (H := K)).range :=
  (((Q'.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3))).map
    (MulAut.conjNormal (H := K))).subgroupOf (MulAut.conjNormal (H := K)).range

@[expose] def AGL81TenNineOneThreeWCQCfg : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)), AGL81CfgData 3 P M H Q K →
    ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) → H ⊓ M ≤ normalizer (L : Set G) →
    ∀ (_ : K.Normal), ∃ Q' : Subgroup G, IsSylowIn 3 Q' (H ⊓ M) ∧ Q ≤ Q' ∧
      ∃ A : Subgroup (MulAut.conjNormal (H := K)).range, Nat.card A = 3 ∧
      IsWClosedIn (agl81QHat G H Q' K) A (agl81YHat G M H K) ∧
      (¬ 3 ∣ Nat.card (d1PlusCore 3 H K) →
        ∃ A' : Subgroup (MulAut.conjNormal (H := K)).range, Nat.card A' = 3 ∧
          IsWClosedIn (agl81QHat G H Q' K) A' (agl81YHat G M H K) ∧ A' ≠ A)

variable {G}

section Plumbing

variable {H : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} [K.Normal]

@[expose] noncomputable def agl81PiHat (H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) [K.Normal] :
    H →* (MulAut.conjNormal (H := K)).range :=
  (MulAut.conjNormal (H := K)).rangeRestrict.comp
    (QuotientGroup.mk' (primeComplementCore (G := H) 3))

theorem agl81PiHat_surjective : Function.Surjective (agl81PiHat H K) :=
  (MonoidHom.rangeRestrict_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem subgroupOf_map_map_eq (X : Subgroup H) :
    ((X.map (QuotientGroup.mk' (primeComplementCore (G := H) 3))).map
      (MulAut.conjNormal (H := K))).subgroupOf (MulAut.conjNormal (H := K)).range =
      X.map (agl81PiHat H K) := by
  ext y
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, hx, Subtype.ext hy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩

theorem agl81QHat_eq (Q' : Subgroup G) :
    agl81QHat G H Q' K = (Q'.subgroupOf H).map (agl81PiHat H K) :=
  subgroupOf_map_map_eq _

theorem agl81YHat_eq (M : Subgroup G) :
    agl81YHat G M H K = (M.subgroupOf H).map (agl81PiHat H K) :=
  subgroupOf_map_map_eq _

end Plumbing

theorem agl81GammaZeroIn_of_cfg_of_sylow (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hE : Asc81bASevenPLRankNX) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card)
    (hS : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hd : AGL81CfgData 3 P M H Q K)
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin 7)) (hYL : H ⊓ M ≤ normalizer (L : Set G))
    [K.Normal] {Q' : Subgroup G} (hQ'Y : IsSylowIn 3 Q' (H ⊓ M)) (hQQ' : Q ≤ Q')
    (hQ'H : IsSylowIn 3 Q' H) :
    GammaZeroIn (agl81QHat G H Q' K) (agl81YHat G M H K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNX := noXBlockFor_of_setting hNX3 hS
  have hT := hd.toTwoLocalPhaseThree' hS h98
  have hK : Open.IsKGroup ↥M := (hT.toTwoLocalPair.isKGroup_of_isKProper hS.kProper).1
  have hA : Asc81bHyp M (pCoreOf 2 H) := hT.asc81bHyp
  have hNH : normalizer (pCoreOf 2 H : Set G) = H := hT.toTwoLocalPair.normalizer_twoCore_H
  have hLM : L ≤ M := hL.le
  have hLX : ¬ InClassXBlock L := fun h =>
    hNX M L hT.toTwoLocalPair.maxTwoLocal_M hLM hL.subnormal h
  have h5 : NineThreeFive M L :=
    ASevenBlock.nineThreeFive_of_altSeven hord hLX (h93 G M (pCoreOf 2 H) L hK hA hL) e
  have hQ'3 : IsPGroup 3 Q' := hQ'H.isPGroup
  have hQ'L : Q' ≤ normalizer (L : Set G) := hQ'Y.le.trans hYL
  have hQ'S : Q' ≤ normalizer (pCoreOf 2 H : Set G) := by rw [hNH]; exact hQ'H.le
  obtain ⟨E, hEP, hEel, hE9⟩ := hE G M (pCoreOf 2 H) L hK hA hL hLX ⟨e⟩
  rw [hNH] at hEP
  have h9 := TenNineOneThree.nine_dvd_card_inf hQ'H hQ'L
    (TenNineOneThree.nine_dvd_card_of_barM (inf_le_right.trans hLM) hEP hE9)
  obtain ⟨C, hCQ, hAel, hA9, hcomm, hdisj, hgen⟩ :=
    ASevenBlock.directProd_of_nineThreeFive h86 hK hA hL h5 hQ'3 hQ'S hQ'L h9
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hQ'M : Q' ≤ M := hQ'Y.le.trans inf_le_right
  have hQ'c : Nat.card (Q'.subgroupOf H) = 3 ^ (Nat.card H).factorization 3 := by
    have := hQ'H.toSylow.card_eq_multiplicity
    rwa [IsSylowIn.coe_toSylow] at this
  have hC1 : C = ⊥ → normalizer (Q' : Set G) ≤ M := by
    intro hC
    have hQA : Q' ⊓ L = Q' := by
      have h := hgen
      rw [hC, sup_bot_eq] at h
      exact h
    have hQ'9 : Nat.card Q' = 9 := by rw [← hQA]; exact hA9
    obtain ⟨-, -, hrk | ⟨F, hFQ, hFel, hF9, hΓ⟩⟩ := hd.base
    · exfalso
      have hrk' : 3 ≤ Open.pRank 3 Q := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← CFSG.SectionRank.pRank_eq_open_pRank_top]
        exact hrk
      obtain ⟨E27, hE27Q, -, h27⟩ := CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 hrk'
      have hdvd := Subgroup.card_dvd_of_le (hE27Q.trans hQQ')
      rw [h27, hQ'9] at hdvd
      norm_num at hdvd
    · have hFQ' : F = Q' :=
        Subgroup.eq_of_le_of_card_ge (hFQ.trans hQQ') (by rw [hQ'9, hF9]; norm_num)
      rw [← hFQ']
      refine le_trans ?_ hΓ
      exact le_sSup ⟨F, le_rfl,
        (by norm_num : 1 ≤ 2).trans
          (CFSG.AGLEmbedding.KFactProofs.G28.two_le_pRank_of_card_9 le_rfl hFel hF9), rfl⟩
  rw [agl81QHat_eq, agl81YHat_eq]
  exact TenNineOneThree.gammaZeroIn_map_of_directProd he hQ'H.le hQ'c hQ'M inf_le_left hCQ hAel
    hA9 (fun a ha c hc => hcomm a ha c hc) hdisj hgen hC1 (agl81PiHat H K) agl81PiHat_surjective

open TenNineOneThree in
theorem agl81TenNineOneThreeListCfg_of_wcQ_core
    (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hsyl : ∀ (_ : Setting G) {P : Sylow 3 G} {M H Q : Subgroup G}
      {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}, AGL81CfgData 3 P M H Q K →
      ∀ {Q' : Subgroup G}, IsSylowIn 3 Q' (H ⊓ M) → Q ≤ Q' → IsSylowIn 3 Q' H)
    (hE : Asc81bASevenPLRankNX) (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card)
    (h9 : AGL81NineCompetitorQ G) (h94 : AGL81NineFourCfg G)
    (hWC : AGL81TenNineOneThreeWCQCfg G) : AGL81TenNineOneThreeListCfg G := by
  intro hS P M H Q K hd L hL he hYL
  have hKn : K.Normal := agl81NineThreeNormalCfg_holds hS 3 P M H Q K hd
  refine ⟨hKn, ?_⟩
  haveI := hKn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlist : NineThreeListGroup 3 K := nineThreeListGroup_of_cfg h9 hS hd
  obtain ⟨Q', hQ'Y, hQQ', A, hA3, hAwc, hdist⟩ := hWC hS P M H Q K hd L hL he hYL hKn
  obtain ⟨e⟩ := he
  have hQ'H := hsyl hS hd hQ'Y hQQ'
  have hY := agl81GammaZeroIn_of_cfg_of_sylow hNX3 h98 hE h86 h93 hord hS hd hL e hYL hQ'Y hQQ'
    hQ'H
  set S : Sylow 3 (MulAut.conjNormal (H := K)).range :=
    hQ'H.toSylow.mapSurjective agl81PiHat_surjective with hSdef
  have hSeq : (S : Subgroup (MulAut.conjNormal (H := K)).range) = agl81QHat G H Q' K := by
    rw [agl81QHat_eq, hSdef, Sylow.coe_mapSurjective, IsSylowIn.coe_toSylow]
  rw [← hSeq] at hY hAwc
  rcases kFactTenNineWCGammaRk_of kFactG28SylowCenter_holds _ K hlist (pRank_le_three_of_cfg hS hd)
    S A _ hA3 hY hAwc with h | h | ⟨hG, huniq⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, not_three_dvd_card_plusCore h94 hS hd (two_le_pRank_of_isCaseIThreeProd h)
      (not_nineFourListGroup_of_isCaseIThreeProd h)⟩
  · exfalso
    obtain ⟨h2, hn⟩ := kFactG28RankNotNineFour_holds _ K hG
    obtain ⟨A', hA'3, hA'wc, hne⟩ := hdist (not_three_dvd_card_plusCore h94 hS hd h2 hn)
    rw [← hSeq] at hA'wc
    exact hne (huniq A' hA'3 hA'wc)

theorem agl81TenNineOneThreeListCfg_of_wcQ'
    (hNX3 : D1NoXBlock3 G) (h98 : AGL81NineEightFour G)
    (hE : Asc81bASevenPLRankNX) (h93 : Asc81bNineThree)
    (h9 : AGL81NineCompetitorQ G) (h94 : AGL81NineFourCfg G)
    (hWC : AGL81TenNineOneThreeWCQCfg G) : AGL81TenNineOneThreeListCfg G :=
  agl81TenNineOneThreeListCfg_of_wcQ_core hNX3 h98
    (fun _ {_ _ _ _ _} hd {_} hQ'Y hQQ' => isSylowIn_H_of_cfg hd hQ'Y hQQ') hE
    (asc81bEightSix_of_bhs bhsLocalCStar_proved) h93
    (fun q hv _ => CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv) h9 h94 hWC

theorem agl81TenNineOneThreeListCfg_of_wcQ_min
    (hNX3 : D1NoXBlock3 G) (hE : Asc81bASevenPLRankNX) (h93 : Asc81bNineThree)
    (h9 : AGL81NineCompetitorQ G) (h94 : AGL81NineFourCfg G)
    (hWC : AGL81TenNineOneThreeWCQCfg G) : AGL81TenNineOneThreeListCfg G :=
  agl81TenNineOneThreeListCfg_of_wcQ' hNX3 agl81NineEightFour_holds hE h93 h9 h94 hWC

end CFSG.LocalAnalysis.RankThreeTheoremC
