module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitSol25
import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FWEq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwFusIEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwSwitch
import CFSG.GroupTheory.ThompsonIndexTwo
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43H
import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_caseA
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) (hG3 : L34Lemma43OddOrbitStep)
    {a x : G} {J S : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hZ1 : S ⊓ zStarIn J = ⊥) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hKL : IsL34Type (K ⧸ Open.fusionZStar K))
    (hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)))
    (hKn : ¬ normalizer (W : Set G) ≤ normalizer (K : Set G)) {T : Subgroup G}
    (hTsyl : IsSylowTwoIn T (normalizer (W : Set G))) (hST : S ≤ T)
    (hTN : T ≤ normalizer (K : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hSsyl, haS, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, hLB, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced solomonCommutingCoreInput hLB
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc, hmax,
    GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hs : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd ha2, le_normalizer := hKM,
      isPComponent_K := hKc, sup_eq := hsup }
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hSsyl
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have haT : a ∈ T := hST haS
  have hxT : x ∈ T := hST hxS
  have haK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  have hCn : T ≤ normalizer ((T ⊓ coreActionKernel K : Subgroup G) : Set G) := by
    intro t ht
    refine GrS4.mem_normalizer_of_map_le_self ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hy).1) (inv_mem ht),
      UnbalancedLayer.conj_mem_coreActionKernel (hTN ht) (mem_inf.mp hy).2⟩
  have hCne : T ⊓ coreActionKernel K ≠ ⊥ := by
    intro h
    have haC : a ∈ T ⊓ coreActionKernel K := mem_inf.mpr ⟨haT, haK⟩
    rw [h, mem_bot] at haC
    rw [haC, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨z, hzC, hz2, hzc⟩ := GrS4.exists_center_involution_of_normal hT2 inf_le_left hCn hCne
  obtain ⟨hzT, hzK⟩ := mem_inf.mp hzC
  have haz : a * z = z * a := hzc a haT
  have hzx : z * x = x * z := (hzc x hxT).symm
  have hzN : z ∈ normalizer (J : Set G) := hCaN (mem_centralizer_singleton_iff.mpr haz.symm)
  have hzJ : z ∈ coreActionKernel J := mem_coreActionKernel_of_mem_kernel hs hzK hzN
  have hzZ : z ∉ center G := GSLit.not_mem_center_of_orderOf_eq_two hnab hz2
  obtain ⟨L, hLz, hLc, hCzN, hLL, hmaxL, hTL, hTLs⟩ :=
    exists_target hMax hS hbase ha2 hz2 haz hJa hJc hmax hL34 hzJ
  obtain ⟨-, -, -, hTset, -, -⟩ := GrS5.gsFixedLayer_facts hS hK ha2 hz2 haz hzZ hJa hJc hzJ
  obtain ⟨hTJJ, hTJs⟩ := GrS5.gsFixedLayer_sup_oddIn hTset
  have hTC : T ≤ centralizer ({z} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hzc t ht)
  have hTNL : T ≤ normalizer (L : Set G) := hTC.trans hCzN
  have hLper : ⁅L, L⁆ = L := commutator_eq_of_isPComponent hLz hLc
  have hU3' : GSUnbalancingTriple z x L :=
    unbalancing_orbit_containment_transfer hU3 hz2 haz hzx hzN (mem_coreActionKernel.mp hzJ).2
      hLz hLc (hTL.trans le_sup_left)
  obtain ⟨T', hT'syl, hTT'⟩ := GrS4.exists_isSylowTwoIn_le' hTNL hT2
  have hT'2 : IsPGroup 2 T' := GrS4.isPGroup_of_isSylowTwoIn hT'syl
  have hset' : L34Sec4Setting G z x L T' := ⟨hbase, hU3', hLL, hmaxL, hT'syl, hTT' hzT, hTT' hxT⟩
  have hZ' : T' ⊓ zStarIn L = ⊥ := inf_zStarIn_eq_bot_of_sup hT'2 hTL hTLs hTJJ hTJs
    (odd_card_zStarIn_of_inf_eq_bot hSsyl hZ1)
  have h3' : IsThreeConnected (T' ⊓ withKernel L) := by
    by_contra h
    have hexp := GrS4.exponent_eq_four L34Facts.l34CenterExponentFact
      L34Facts.l34ElementaryCenterFact hset' h
    rw [hZ', Monoid.exp_eq_one_of_subsingleton] at hexp
    exact absurd hexp (by norm_num)
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hSsyl
  obtain ⟨E₁, -, hE₁P, -, hE₁, -, -⟩ := L34Facts.l34TwoEightsFact G J (S ⊓ J) hJper hL34 hP
  have hPT : S ⊓ J ≤ gsFixedLayer J z :=
    le_gsFixedLayer_of_isPGroup hTset (hS2.to_le inf_le_left)
      (fun p hp => mem_inf.mpr ⟨(mem_inf.mp hp).2, hTC (hST (mem_inf.mp hp).1)⟩)
  have hE₁r : IsAbelianTwoOfRank 3 E₁ := hE₁.1.isAbelianTwoOfRank (by rw [hE₁.2])
  have hE₁S : E₁ ≤ S ⊓ withKernel J :=
    le_inf (hE₁P.trans inf_le_left) ((hE₁P.trans inf_le_right).trans le_sup_left)
  have hE₁L : E₁ ≤ withKernel L := ((hE₁P.trans hPT).trans hTL).trans le_sup_left
  have hE₁T' : E₁ ≤ T' ⊓ withKernel L :=
    le_inf ((hE₁P.trans inf_le_left).trans (hST.trans hTT')) hE₁L
  have hWE₁ : wGroup E₁ = W := hWB E₁ hE₁S hE₁r
  have hWB' : ∀ B : Subgroup G, B ≤ T' ⊓ withKernel L → IsAbelianTwoOfRank 3 B →
      wGroup B = W := fun B hB hBr =>
    (wGroup_eq_of_abelianConnected hGW (h3' B E₁ hB hE₁T' hBr hE₁r).abelianConnected).trans hWE₁
  have hP' : IsSylowTwoIn (T' ⊓ L) L := GrS4.isSylowTwoIn_inf hT'syl
  have hZP' : T' ⊓ L ⊓ zStarIn L = ⊥ := eq_bot_iff.mpr fun y hy => by
    have h1 : y ∈ T' ⊓ zStarIn L :=
      mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hy).1).1, (mem_inf.mp hy).2⟩
    rwa [hZ'] at h1
  obtain ⟨E', -, hE'P, hE', hE'c, -⟩ := L34Facts.l34ElementaryCenterFact G L (T' ⊓ L) hLper hLL
    hP' fun y hy => by
      rw [hZP', mem_bot] at hy
      rw [hy, one_mul]
  rw [hZP', card_bot, mul_one] at hE'c
  obtain ⟨F', -, hF'P, -, hF', -, -⟩ := L34Facts.l34TwoEightsFact G L (T' ⊓ L) hLper hLL hP'
  have hNL : normalizer (L : Set G) ≤ M :=
    normalizer_le_of_wData L34Facts.l34ParabolicGenerationFact hLper hLL hP'
      (inf_le_inf_left _ le_sup_left) inf_le_right hWB'
      (hE'P.trans (inf_le_inf_left _ le_sup_left)) hE' (by omega) hF'P hF'
  have hTeq : T' = T := hTsyl.eq_of_le hTT' (hT'syl.1.trans hNL) hT'2
  have hT'M : IsSylowTwoIn T' M := hTeq ▸ hTsyl
  have hcent' : ∀ s ∈ T', s * z = z * s := fun s hs => hzc s (hTeq ▸ hs)
  have hLM : L ≤ M := le_normalizer.trans hNL
  have hOJ : oddIn J ≤ oddIn M := by
    rw [GrS4.oddIn_eq_inf_of_singleComponentSetting hs]
    exact inf_le_right
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hKL' : K ≤ L ⊔ oddIn M :=
    (le_of_eq (GrS4.eq_sup_oddIn_of_singleComponentSetting hs)).trans
      (sup_le ((le_of_eq hTJs.symm).trans
        (sup_le (hTL.trans le_sup_left) (hOJ.trans le_sup_right))) (hOK.trans le_sup_right))
  have hLN : L ≤ normalizer (K : Set G) := fun l hl =>
    mem_normalizer_of_commute hMax hS hbase hs hL34 hz2 haz hzK (hLM hl)
      (mem_centralizer_singleton_iff.mp (hLz hl))
  have hLKO : L ≤ normalizer ((K ⊔ oddIn M : Subgroup G) : Set G) := by
    intro l hl
    refine mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hLN hl),
      mem_normalizer_iff_map_conj_eq.mp (GrS4.self_le_normalizer_oddIn M (hLM hl))]
  have hLK : L ≤ K ⊔ oddIn M :=
    le_of_sup_oddIn_eq_of_normalizer hLper hTL hTLs
      ((hTJJ.trans (GrS4.le_of_singleComponentSetting hs)).trans le_sup_left) hLKO
  have hsup' : L ⊔ oddIn M = K ⊔ oddIn M :=
    le_antisymm (sup_le hLK le_sup_right) (sup_le hKL' le_sup_right)
  have hrun' : L34Sec4Running L E₁ := ⟨hE₁L, hE₁, by rw [hWE₁]; exact hW⟩
  have hSylT : ∃ P : Sylow 2 G, (P : Subgroup G) = T' :=
    GrS5S.l34Lemma43SylowStepS_of_certs G z x L T' E₁ hset' hcent' hrun' h3' W hW hWodd hWB'
      hNL hT'M
  have hgs' : GSMaximalSetting G z L := ⟨hsimple, hnab, hK, hUo, hz2, hLz, hLc, hmaxL,
    GrS5.three_le_pRank_of_l34 hLL, Sol78.not_psp4_of_l34 hLL, Or.inl ⟨hLL, hset.1⟩⟩
  have hs' : SingleComponentSetting G z L W K :=
    { toGSMaximalSetting := hgs', ne_bot := hW, odd_card := hWodd, normalizer_le := hNL,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd hz2, le_normalizer := hKM,
      isPComponent_K := hKc, sup_eq := hsup' }
  have hincl := hG3 G z x L T' E₁ hset' hcent' hrun' h3' hZ' W hW hWodd hWB' hNL K hKM hKc hKL
    hsup' hT'M hSylT (hTeq ▸ hTN) hKn (FW.not_oddIn_le_of_not_le hMax hs' hKn)
  exact false_of_sylowIncl hMax GrS5S.l34Lemma43SylowStepS_of_certs
    (GrS5S.l34Lemma43FusionStepI_of_max hMax) hHS hset' hcent' hrun' h3' hW hWodd hWB' hNL hincl
    hT'M

end CFSG.ComponentClassification.GrSLit.KSw
