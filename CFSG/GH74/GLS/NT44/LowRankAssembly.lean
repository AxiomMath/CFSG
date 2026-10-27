module

public import CFSG.GH74.GLS.Stage1.Thm4.Defs
public import CFSG.GH74.GLS.NT44.LowRankComponentAction
import CFSG.GH74.GLS.NT44.LowRankActor
import CFSG.GH74.GLS.NT44.RankThreeBalanceObstructions
import CFSG.GH74.GLS.NT44.LowRankObstructionImage
import CFSG.GH74.GLS.NT44.ComponentQuotientSylow
import CFSG.GH74.GLS.NT44.LowRankModelClassification
import CFSG.GH74.GLS.NT44.RigidSylowCardinality
import CFSG.GH74.GLS.NT44.LocalKBalance
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutTwoPart
import CFSG.GH74.Generic.BProg.B3.S3T2A7LocEven

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup
open scoped commutatorElement

theorem low_rank_conjugate_closure_balance_of_noncentral_involution
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {fullQ : Type} [Group fullQ]
    {T W J : Subgroup G} {x u : G}
    (hnonab : ∃ b c : G, b * c ≠ c * b)
    (hx2 : orderOf x = 2)
    (hmax : ∀ z : G, orderOf z = 2 →
      (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ z).ncard ≤
        (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x).ncard)
    (hJ : J ∈ CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    (hcenter : Nat.card (Subgroup.center fullQ) = 16)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hxT : x ∈ T)
    (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hW : CFSG.ABGLocalTools.IsSylowOf 2 W
      (CFSG.GH74.GLS.zStar (CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x)))
    (hWT : W ≤ T)
    (hZW : Subgroup.closure {z : G | z ∈ T ∧ IsConj x z} ≤ W)
    (hWrank : CFSG.pRank 2 ↥W ≤ 2)
    (huT : u ∈ T)
    (huJ : u ∈ J)
    (hu2 : orderOf u = 2)
    (huZ : u ∉ CFSG.GH74.GLS.zStar J) :
    let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
    let A : Subgroup G := Z ⊔ Subgroup.zpowers u
    A ≤ T ⊓ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x ∧
      CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A := by
  classical
  let Z : Subgroup G := Subgroup.closure {z : G | z ∈ T ∧ IsConj x z}
  let A : Subgroup G := Z ⊔ Subgroup.zpowers u
  change
    A ≤ T ⊓ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x ∧
      CFSG.GH74.GLS.IsE 3 ⊤ A ∧
      CFSG.GH74.GLS.IsKBal 2 A ∧ CFSG.GH74.GLS.IsWeakKBal 1 A
  let P : Subgroup G := CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x
  have hJP : J ≤ P := by
    show J ≤ sSup (CFSG.GH74.GLS.Stage1.Thm4.RigidSet fullQ x)
    exact le_sSup hJ
  have hW' : CFSG.ABGLocalTools.IsSylowOf 2 W (CFSG.GH74.GLS.zStar P) := hW
  have hActor := low_rank_conjugate_closure_actor_of_noncentral_involution
    (P := P) hnonab hT hx2 hxT hTC hW' hWT hJP hZW hWrank huT huJ hu2 huZ
  obtain ⟨hZomega, hZ4, hZconj, hZcl, huW, hATP, hE, hA8, hAW, hACW⟩ := hActor
  have hAelem : CFSG.IsElementaryAbelian 2 ↥A := hE.2.1
  have h16W : 16 ∣ Nat.card ↥W := by
    have hdiv := CFSG.GH74.GLS.NT44.two_pow_dvd_card_sylow_zStar_kz_of_mem_rigidSet
      (n := 4) hJ (by rw [hcenter]; norm_num) hW
    simpa using hdiv
  have hterminal : ∀ (a : G) (haA : a ∈ A) (ha2 : orderOf a = 2)
      (hAH : A ≤ Subgroup.centralizer ({a} : Set G))
      (L : Subgroup (CFSG.GH74.CentralizerBar a))
      (hL : CFSG.IsComponent L)
      (hcent : ((A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
          (CFSG.GH74.GLS.Th2.Bal.piBar a)) ⊓
        Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
        Subgroup.zpowers (CFSG.GH74.GLS.Th2.Bal.piBar a ⟨a, hAH haA⟩))
      (k : ℕ) (hk : 1 ≤ k)
      (hnotLocal : ¬ CFSG.GH74.GLS.Th2.Bal.IsLocallyKBalanced k
        (↥L ⧸ Subgroup.center ↥L)), False := by
    intro a haA ha2 hAH L hL hcent k hk hnotLocal
    obtain ⟨haW, hWH, hrest⟩ :=
      original_low_rank_obstruction_faithful_image
        hnonab hx2 hmax hW hZ4 hZW hAelem hACW a haA ha2 hAH L hL hcent
    dsimp only at hrest
    obtain ⟨hj, hrange, hV4, hVElem, hVbot, hfaith⟩ := hrest
    have hAction := original_low_rank_component_action_of_faithful_image
      hT hWT hWH hL hZomega hZcl hj hV4 hVElem hfaith
    obtain ⟨S, hLn, hrest2⟩ := hAction
    dsimp only at hrest2
    obtain ⟨hWS, hVSbar, hstrong, hnormal, hVLeL, hType, hInd, hact, hAlphaInj⟩ := hrest2
    let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
    let π := CFSG.GH74.GLS.Th2.Bal.piBar a
    let j : ↥W →* CFSG.GH74.CentralizerBar a := π.comp (Subgroup.inclusion hWH)
    let Sbar : Sylow 2 (CFSG.GH74.CentralizerBar a) :=
      S.mapSurjective (CFSG.GH74.GLS.TwoThin.barMk_surjective (Y := ↥H))
    let α : ↥W →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
      (@CFSG.GH74.GLS.Prop27.actQuot
        (CFSG.GH74.CentralizerBar a) inferInstance L hLn).comp j
    have hSylow := exists_centerQuotient_sylow_omega1_four
      Sbar hLn hVLeL hVElem hV4 hfaith hInd
    obtain ⟨P_L, hP_L, hrest3⟩ := hSylow
    dsimp only at hrest3
    obtain ⟨hOmega, hOmega4, hOmegaElem, hOmegaComm⟩ := hrest3
    let τ : ↥L →* (↥L ⧸ Subgroup.center ↥L) :=
      QuotientGroup.mk' (Subgroup.center ↥L)
    let Q : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
      P_L.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L))
    let K := ↥L ⧸ Subgroup.center ↥L
    let _ : IsSimpleGroup K := hL.1.2.1
    have hModel := psl2_odd_or_psu34_of_goldschmidtSimpleType_omega1_card_four
      (K := K) hType Q hOmegaComm hOmega4
    rcases hModel with ⟨p, f, hpFact, hOdd, hf, h5, h8, hPSL⟩ | hPSU
    ·
      obtain ⟨ePSL⟩ := hPSL
      have hW2 : IsPGroup 2 ↥W := hT.isPGroup.to_le hWT
      have h8W := @CFSG.AGLEmbedding.card_dvd_eight_of_injective_mulAut_psl2
        ↥W _ _ K _ _ p f hpFact hOdd hf h5 h8 ePSL hW2 α hAlphaInj
      exact (by decide : ¬ ((16 : ℕ) ∣ 8)) (h16W.trans h8W)
    ·
      obtain ⟨ePSU⟩ := hPSU
      have hLie : CFSG.Blueprint.LieModel K .PSU 3 2 2 :=
        Or.inl ⟨by decide,
          (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff K 2 le_rfl).mpr
            ⟨(show K ≃* CFSG.Theory.Comparator.PSU3Model 2 from ePSU)⟩⟩
      have hLB := CFSG.GH74.Generic.BProg.B3.S3T2A7Loc.locBal1Two_U34 hLie
      exact hnotLocal (CFSG.GH74.GLS.NT44.isLocallyKBalanced_of_locBal1Two hLB hk)
  have hKBal : CFSG.GH74.GLS.IsKBal 2 A := by
    by_contra hnotK
    obtain ⟨a, haA, hAH, D, L, hrest⟩ :=
      exists_strong_two_obstruction_with_rank_three_centralizer hAelem hA8 hnotK
    dsimp only at hrest
    obtain ⟨ha1, ha2, hD, hL, hFnorm, hFcent, hRnorm, hRcentF, hNne, hNR,
      hNnc, hcent, hnotLocal⟩ := hrest
    exact hterminal a haA ha2 hAH L hL hcent 2 (by norm_num) hnotLocal
  have hWeakKBal : CFSG.GH74.GLS.IsWeakKBal 1 A := by
    by_contra hnotW
    obtain ⟨a, haA, hAH, D, L, hrest⟩ :=
      exists_weak_one_obstruction_with_rank_three_centralizer hAelem hA8 hnotW
    dsimp only at hrest
    obtain ⟨ha1, ha2, hD, hL, hFnorm, hFcent, hRnorm, hRcentF, hNne, hNR,
      hNnc, hcent, hnotLocal⟩ := hrest
    exact hterminal a haA ha2 hAH L hL hcent 1 (by norm_num) hnotLocal
  have hATP' : A ≤ T ⊓ CFSG.GH74.GLS.Stage1.Thm4.Kz fullQ x := hATP
  exact ⟨hATP', hE, hKBal, hWeakKBal⟩

end CFSG.GH74.GLS.NT44

end
