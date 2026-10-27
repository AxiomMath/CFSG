module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwStep
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwMemTools
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inner56
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayerNormalizer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5TWGen
import CFSG.GroupTheory.ThompsonIndexTwo
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43H
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Choice56
import CFSG.Sporadic.HeldB.AllFixed

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

theorem false_of_normal_of_mem
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) {a x : G} {J S : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (h3 : IsThreeConnected (S ⊓ withKernel J)) (haZ : a ∈ S ⊓ zStarIn J) {W : Subgroup G}
    (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)))
    (hKN : normalizer (W : Set G) ≤ normalizer (K : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hSsyl, haS, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
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
  have haJ : a ∈ J := (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp haZ).2
  obtain ⟨T, hTsyl, hST⟩ := GrS4.exists_isSylowTwoIn_le' (hSsyl.1.trans hNJ) hS2
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have haT : a ∈ T := hST haS
  have hxT : x ∈ T := hST hxS
  have haK : a ∈ coreActionKernel K := GrS4.mem_coreActionKernel_of_singleComponentSetting hMax hs
  have hCn : T ≤ normalizer ((T ⊓ coreActionKernel K : Subgroup G) : Set G) := by
    intro t ht
    refine GrS4.mem_normalizer_of_map_le_self ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hy).1) (inv_mem ht),
      UnbalancedLayer.conj_mem_coreActionKernel (hKN (hTsyl.1 ht)) (mem_inf.mp hy).2⟩
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
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hSsyl
  have hPT : S ⊓ J ≤ gsFixedLayer J z :=
    le_gsFixedLayer_of_isPGroup hTset (hS2.to_le inf_le_left)
      (fun p hp => mem_inf.mpr ⟨(mem_inf.mp hp).2, hTC (hST (mem_inf.mp hp).1)⟩)
  have haL : a ∈ L := hTL (hPT (mem_inf.mpr ⟨haS, haJ⟩))
  have haCL : a ∈ coreActionKernel L :=
    mem_coreActionKernel_of_conj_mem_oddIn hTL hTLs (hTNL haT) fun y hy => by
      have hya : y * a = a * y := mem_centralizer_singleton_iff.mp (hJa (hTJJ hy))
      rw [show a * y * a⁻¹ * y⁻¹ = 1 by rw [← hya]; group]
      exact Subgroup.one_mem _
  have haZL : a ∈ zStarIn L := GrS5S.mem_zStarIn_of_mem_coreActionKernel haL haCL
  have hCS : T' ⊓ centralizer ({a} : Set G) = S :=
    hSsyl.eq_of_le (le_inf (hST.trans hTT') fun s hs => mem_centralizer_singleton_iff.mpr
      (hcent s hs)) (inf_le_right.trans hCaN) (hT'2.to_le inf_le_left)
  have hSN : ∀ s ∈ S, s ∈ normalizer (L : Set G) ∧ s ∈ normalizer (gsFixedLayer J z : Set G) :=
    fun s hs => ⟨hTNL (hST hs),
      UnbalancedGS.mem_normalizer_gsFixedLayer_of_commute (hSsyl.1 hs) (hzc s (hST hs))⟩
  have hU : T' ⊓ withKernel L = S ⊓ withKernel J := by
    apply le_antisymm
    · intro t ht
      obtain ⟨htT', htK⟩ := mem_inf.mp ht
      have htS : t ∈ S := hCS ▸ mem_inf.mpr ⟨htT', mem_centralizer_singleton_iff.mpr
        (GrS5.commute_of_mem_withKernel hT'2 htT' htK (hTT' haT) haZL)⟩
      exact mem_inf.mpr ⟨htS, mem_withKernel_of_fixedLayer hTL hTJJ hTLs hTJs htK
        (hSsyl.1 htS) (hSN t htS).2⟩
    · intro s hs
      obtain ⟨hsS, hsK⟩ := mem_inf.mp hs
      exact mem_inf.mpr ⟨hTT' (hST hsS), mem_withKernel_of_fixedLayer hTJJ hTL hTJs hTLs hsK
        (hSN s hsS).1 (hSN s hsS).2⟩
  have h3' : IsThreeConnected (T' ⊓ withKernel L) := hU ▸ h3
  have hWB' : ∀ B : Subgroup G, B ≤ T' ⊓ withKernel L → IsAbelianTwoOfRank 3 B →
      wGroup B = W := fun B hB hBr => hWB B (hU ▸ hB) hBr
  obtain ⟨E₁, E₂, hE₁P, hE₂P, hE₁, hE₂, hE₁₂⟩ :=
    L34Facts.l34TwoEightsFact G J (S ⊓ J) hJper hL34 hP
  have hPS₁ : S ⊓ J ≤ S ⊓ withKernel J := inf_le_inf_left _ le_sup_left
  obtain ⟨D, hDS, hD, hD16⟩ := GrS4.exists_sixteen_of_isThreeConnected h3 (hE₁P.trans hPS₁)
    (hE₂P.trans hPS₁) hE₁ hE₂ hE₁₂
  have hE₁r : IsAbelianTwoOfRank 3 E₁ := hE₁.1.isAbelianTwoOfRank (by rw [hE₁.2])
  have hE₁S : E₁ ≤ S ⊓ withKernel J := hE₁P.trans hPS₁
  have hE₁L : E₁ ≤ withKernel L := ((hE₁P.trans hPT).trans hTL).trans le_sup_left
  have hWE₁ : wGroup E₁ = W := hWB E₁ hE₁S hE₁r
  have hP' : IsSylowTwoIn (T' ⊓ L) L := GrS4.isSylowTwoIn_inf hT'syl
  obtain ⟨F', -, hF'P, -, hF', -, -⟩ := L34Facts.l34TwoEightsFact G L (T' ⊓ L) hLper hLL hP'
  have hNL : normalizer (L : Set G) ≤ M :=
    normalizer_le_of_wData L34Facts.l34ParabolicGenerationFact hLper hLL hP'
      (inf_le_inf_left _ le_sup_left) inf_le_right hWB' (hU ▸ hDS) hD hD16 hF'P hF'
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
  have hMN : M ≤ normalizer ((K ⊔ oddIn M : Subgroup G) : Set G) := by
    intro m hm
    refine mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp (hKN hm),
      mem_normalizer_iff_map_conj_eq.mp (GrS4.self_le_normalizer_oddIn M hm)]
  have hLK : L ≤ K ⊔ oddIn M :=
    le_of_sup_oddIn_eq_of_normalizer hLper hTL hTLs
      ((hTJJ.trans (GrS4.le_of_singleComponentSetting hs)).trans le_sup_left) (hLM.trans hMN)
  have hsup' : L ⊔ oddIn M = K ⊔ oddIn M :=
    le_antisymm (sup_le hLK le_sup_right) (sup_le hKL' le_sup_right)
  have hrun' : L34Sec4Running L E₁ := ⟨hE₁L, hE₁, by rw [hWE₁]; exact hW⟩
  exact false_of_kSylow hMax GrS5S.l34Lemma43SylowStepKS_of_certs
    (GrS5S.l34Lemma43FusionStepKS_of_max hMax) hHS hset' hcent' hrun' h3' hW hWodd hWB' hNL
    hKM hKc hsup' hKN hT'M

end CFSG.ComponentClassification.GrSLit.KSw

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma43KSylowMemStep_of_inputs
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) : L34Lemma43KSylowMemStep := by
  intro G _ _ a x J S A hset hcent _ h3 _ haZ W hW hWodd hWB hNJ K hKM hKc _ hsup hKN
  exact (KSw.false_of_normal_of_mem hMax hS hHS hset hcent h3 haZ hW hWodd hWB hNJ hKM hKc hsup
    hKN).elim

end CFSG.ComponentClassification.GrSLit
