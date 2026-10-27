module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSw46Tools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFL
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inner56
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayerNormalizer
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSTarget
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Lemma55
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Sylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Walter.J1
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

theorem false_of_kSylow46 (hMax : MaximalTwoComponentInput)
    (hSol : SolomonCommutingCoreInput) (h45 : L34Lemma45) (hU : L34UnbalancingUnitaryStep)
    (hC : L34UnitaryCentralizerFact) (hCF : L34CentralFourFact) (hZS : L34Lemma46CenterStep)
    (hCl : L34Lemma46ClosedStep) (hGold : GoldschmidtStronglyClosedInput) {a x : G}
    {J S A : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hZ : S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) (hrun : L34Sec4Running J A)
    (h3 : ¬ IsThreeConnected (S ⊓ withKernel J)) (hexp : Monoid.exponent ↥(S ⊓ zStarIn J) = 4)
    (hcyc : ¬ IsCyclic ↥(S ⊓ zStarIn J)) {W : Subgroup G} (hW : W ≠ ⊥)
    (hWodd : Odd (Nat.card W)) (hWE : wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G)))
    (hKN : normalizer (W : Set G) ≤ normalizer (K : Set G))
    (hSM : IsSylowTwoIn S (normalizer (W : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hS, haS, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, hLB, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hsc : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := GrS4.normalizer_ne_top_of_odd hW hWodd ha2, le_normalizer := hKM,
      isPComponent_K := hKc, sup_eq := hsup }
  have hCaM : centralizer ({a} : Set G) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have hJM : J ≤ M := le_normalizer.trans hNJ
  have hJK : J ≤ K := GrS4.le_of_singleComponentSetting hsc
  have hKsup : J ⊔ oddIn K = K := (GrS4.eq_sup_oddIn_of_singleComponentSetting hsc).symm
  have hJ1 : ((oddIn M ⊔ J).subgroupOf M).Normal := normal_oddIn_sup_of_normalizer hJM hsup hKN
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := GrS4.isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer (P : Set G) := GrS4.inf_mem_normalizer (le_normalizer hxS) (hSN hxS)
  obtain ⟨-, h8, -, -, -, hel, -, -⟩ := hC G J P x hJper hL34 hxU hP hxP
  have hR : IsEightGroup (P ⊓ centralizer ({x} : Set G)) := ⟨hel (by rwa [hZP]), h8⟩
  obtain ⟨C, -, hCe, -, hRC, -, hNC⟩ := hCF G J P x hJper hL34 hP hxU hxP (by rwa [hZP])
    (by rw [hZP]; exact GrS4.exists_sq_ne_one_of_exponent_eq_four hexp)
  have hWC : wGroup C = W := (wGroup_eq_of_le_eight hGW hCe hRC hR.2).trans hWE
  have hNP : normalizer (P : Set G) ≤ M := fun n hn => by
    have h1 := GrS4.mem_normalizer_wGroup (hNC hn)
    rwa [hWC] at h1
  have hOJ : oddIn J ≤ oddIn M := by
    rw [GrS4.oddIn_eq_inf_of_singleComponentSetting hsc]
    exact inf_le_right
  have hNS : normalizer (S : Set G) ≤ M := by
    intro y hy
    have hbS : y⁻¹ * a * y ∈ S := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hy) a).mp haS
      rwa [inv_inv] at h1
    have hbZ : ∀ t ∈ S, (y⁻¹ * a * y) * t = t * (y⁻¹ * a * y) := by
      intro t ht
      have ht' : y * t * y⁻¹ ∈ S := (mem_normalizer_iff.mp hy t).mp ht
      have hc := hcent _ ht'
      calc y⁻¹ * a * y * t = y⁻¹ * (a * (y * t * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * t * y⁻¹) * a) * y := by rw [hc]
        _ = t * (y⁻¹ * a * y) := by group
    have hbJ := hZS G a x J S A hset hcent hZ hrun h3 hexp hcyc _ hbS hbZ
    have hcond := GrS4.mem_zStarIn_oddIn_sup hJM hOJ (hSM.1 hbS) hbJ
    obtain ⟨m, hm, hbm⟩ := h45 G a x J S hset M hJM hJ1 hSM (fun s hs => (hcent s hs).symm)
      hNP y (hSM.1 hbS) hcond
    have hc : y * m⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc y * m⁻¹ * a = y * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = y * (y⁻¹ * a * y) * m⁻¹ := by rw [← hbm]
        _ = a * (y * m⁻¹) := by group
    have h1 := mul_mem (hCaM hc) hm
    rwa [inv_mul_cancel_right] at h1
  obtain ⟨T, hTS⟩ := GrS4.exists_sylow_eq_of_normalizer_le_of_isSylowTwoIn hSM hNS
  obtain ⟨B, hBZ, hB, hBsc⟩ := hCl G a x J S A hset hcent hZ hrun h3 hexp hcyc W hW hWodd hWE
    hNJ (l34ZConjClosed_of_le_normalizer hJK hKsup hKN hP (GrS4.isPGroup_of_isSylowTwoIn hS))
    hNS ⟨T, hTS⟩
  refine GrS4.false_of_stronglyClosed_le_zStarIn hGold hnab T hJa hJc (hBZ.trans inf_le_right)
    (by rw [hTS]; exact hBZ.trans inf_le_left) hB ?_
  rw [hTS]
  exact hBsc

theorem false_of_frattini46 (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hFixL : SolomonFixedLayerStep)
    (hSol : SolomonCommutingCoreInput) (h44 : L34Lemma44) (h45 : L34Lemma45)
    (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact) (hCF : L34CentralFourFact)
    (hZS : L34Lemma46CenterStep) (hCl : L34Lemma46ClosedStep)
    (hGold : GoldschmidtStronglyClosedInput) {a x : G} {J S : Subgroup G}
    (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hZ : S ⊓ zStarIn J ≠ ⊥ → a ∈ S ⊓ zStarIn J) (h3 : ¬ IsThreeConnected (S ⊓ withKernel J))
    (hexp : Monoid.exponent ↥(S ⊓ zStarIn J) = 4) (hcyc : ¬ IsCyclic ↥(S ⊓ zStarIn J))
    {W : Subgroup G} (hW : W ≠ ⊥) (hWodd : Odd (Nat.card W))
    (hWE : wGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) {K : Subgroup G}
    (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G))))
    (hsup : J ⊔ oddIn (normalizer (W : Set G)) = K ⊔ oddIn (normalizer (W : Set G))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbase, hU3, hL34, hmax, hSsyl, haS, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, hLB, -, -⟩ := id hbase
  have : IsSimpleGroup G := hsimple
  have hGW : GWTwoBalanced G := gwTwoBalanced_of_locallyTwoBalanced hSol hLB
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
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro h
    obtain ⟨y, hy, hyy⟩ := GrS4.exists_sq_ne_one_of_exponent_eq_four hexp
    rw [h, mem_bot] at hy
    rw [hy, one_mul] at hyy
    exact hyy rfl
  have haZ : a ∈ S ⊓ zStarIn J := hZ hZne
  have haJ : a ∈ J := (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp haZ).2
  have hKN : M ≤ normalizer (K : Set G) :=
    Single.normalizer_le_of_mem hMax hFixL hs hL34 hset.1 haJ
  have hJK : J ≤ K := GrS4.le_of_singleComponentSetting hs
  have hKsup : J ⊔ oddIn K = K := (GrS4.eq_sup_oddIn_of_singleComponentSetting hs).symm
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hSsyl
  obtain ⟨T, hTsyl, hST⟩ := GrS4.exists_isSylowTwoIn_le' (hSsyl.1.trans hNJ) hS2
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hTsyl
  have haT : a ∈ T := hST haS
  have hxT : x ∈ T := hST hxS
  have haZK : a ∈ zStarIn K := mem_zStarIn_of_fixedLayer le_rfl hJK hKsup haJ (mem_inf.mp haZ).2
  have hCn : T ≤ normalizer ((T ⊓ zStarIn K : Subgroup G) : Set G) := by
    intro t ht
    refine GrS4.mem_normalizer_of_map_le_self ?_
    rintro _ ⟨y, hy, rfl⟩
    exact mem_inf.mpr ⟨mul_mem (mul_mem ht (mem_inf.mp hy).1) (inv_mem ht),
      GrS4.conj_mem_zStarIn (hKN (hTsyl.1 ht)) (mem_inf.mp hy).2⟩
  have hCne : T ⊓ zStarIn K ≠ ⊥ := by
    intro h
    have haC : a ∈ T ⊓ zStarIn K := mem_inf.mpr ⟨haT, haZK⟩
    rw [h, mem_bot] at haC
    rw [haC, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨z, hzC, hz2, hzc⟩ := GrS4.exists_center_involution_of_normal hT2 inf_le_left hCn hCne
  obtain ⟨hzT, hzK⟩ := mem_inf.mp hzC
  have haz : a * z = z * a := hzc a haT
  have hzx : z * x = x * z := (hzc x hxT).symm
  have hCS : T ⊓ centralizer ({a} : Set G) = S :=
    hSsyl.eq_of_le (le_inf hST fun s hs => mem_centralizer_singleton_iff.mpr (hcent s hs))
      (inf_le_right.trans hCaN) (hT2.to_le inf_le_left)
  have hzS : z ∈ S := hCS ▸ mem_inf.mpr ⟨hzT, mem_centralizer_singleton_iff.mpr haz.symm⟩
  have hzSJ : z ∈ S ⊓ J := by
    rw [← inf_eq_of_sup_oddIn hP hJK hKsup hS2]
    exact mem_inf.mpr ⟨hzS, (map_subtype_le _ : zStarIn K ≤ K) hzK⟩
  have hzZJ : z ∈ zStarIn J := GrS4.mem_zStarIn_of_le hJK (mem_inf.mp hzSJ).2 hzK
  have hzJ : z ∈ coreActionKernel J := GrS5.zStarIn_le_coreActionKernel J hzZJ
  have hzN : z ∈ normalizer (J : Set G) := hCaN (mem_centralizer_singleton_iff.mpr haz.symm)
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
  have hPT : S ⊓ J ≤ gsFixedLayer J z :=
    le_gsFixedLayer_of_isPGroup hTset (hS2.to_le inf_le_left)
      (fun p hp => mem_inf.mpr ⟨(mem_inf.mp hp).2, hTC (hST (mem_inf.mp hp).1)⟩)
  have hLeq : T' ⊓ L = S ⊓ J := inf_eq_of_fixedLayer hP hTJJ hPT hTL hTLs (hST.trans hTT') hT'2
  have hZeq : T' ⊓ zStarIn L = S ⊓ zStarIn J :=
    inf_zStarIn_eq_of_fixedLayer hTJJ hTL hTJs hTLs hPT hLeq
  have haZL : a ∈ zStarIn L :=
    mem_zStarIn_of_fixedLayer hTJJ hTL hTLs (hPT (mem_inf.mpr ⟨haS, haJ⟩)) (mem_inf.mp haZ).2
  have hCS' : T' ⊓ centralizer ({a} : Set G) = S :=
    hSsyl.eq_of_le (le_inf (hST.trans hTT') fun s hs => mem_centralizer_singleton_iff.mpr
      (hcent s hs)) (inf_le_right.trans hCaN) (hT'2.to_le inf_le_left)
  have hSN : ∀ s ∈ S, s ∈ normalizer (L : Set G) ∧ s ∈ normalizer (gsFixedLayer J z : Set G) :=
    fun s hs => ⟨hTNL (hST hs),
      UnbalancedGS.mem_normalizer_gsFixedLayer_of_commute (hSsyl.1 hs) (hzc s (hST hs))⟩
  have hUeq : T' ⊓ withKernel L = S ⊓ withKernel J := by
    apply le_antisymm
    · intro t ht
      obtain ⟨htT', htK⟩ := mem_inf.mp ht
      have htS : t ∈ S := hCS' ▸ mem_inf.mpr ⟨htT', mem_centralizer_singleton_iff.mpr
        (GrS5.commute_of_mem_withKernel hT'2 htT' htK (hTT' haT) haZL)⟩
      exact mem_inf.mpr ⟨htS, mem_withKernel_of_fixedLayer hTL hTJJ hTLs hTJs htK
        (hSsyl.1 htS) (hSN t htS).2⟩
    · intro s hs
      obtain ⟨hsS, hsK⟩ := mem_inf.mp hs
      exact mem_inf.mpr ⟨hTT' (hST hsS), mem_withKernel_of_fixedLayer hTJJ hTL hTJs hTLs hsK
        (hSN s hsS).1 (hSN s hsS).2⟩
  have h3' : ¬ IsThreeConnected (T' ⊓ withKernel L) := by rw [hUeq]; exact h3
  have hexp' : Monoid.exponent ↥(T' ⊓ zStarIn L) = 4 := by rw [hZeq]; exact hexp
  have hcyc' : ¬ IsCyclic ↥(T' ⊓ zStarIn L) := by rw [hZeq]; exact hcyc
  have hZ' : T' ⊓ zStarIn L ≠ ⊥ → z ∈ T' ⊓ zStarIn L := fun _ => by
    rw [hZeq]
    exact mem_inf.mpr ⟨hzS, hzZJ⟩
  have hWE' : wGroup (T' ⊓ L ⊓ centralizer ({x} : Set G)) = W := by rw [hLeq]; exact hWE
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by rw [inf_assoc, inf_eq_right.mpr hZJ]
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    GrS4.inf_mem_normalizer (le_normalizer hxS) (hSsyl.1 hxS)
  obtain ⟨-, h8, -, -, -, hel, -, -⟩ := hC G J (S ⊓ J) x hJper hL34 hxU hP hxP
  have hR : IsEightGroup (S ⊓ J ⊓ centralizer ({x} : Set G)) := ⟨hel (by rwa [hZP]), h8⟩
  have hrun' : L34Sec4Running L (S ⊓ J ⊓ centralizer ({x} : Set G)) :=
    ⟨(inf_le_left.trans (hPT.trans hTL)).trans le_sup_left, hR, by rw [hWE]; exact hW⟩
  have hNL : normalizer (L : Set G) ≤ M :=
    normalizer_le_of_wGroup46 hGW h44 hU hC hCF hset' hrun' hexp' hcyc' hWE'
  have hTeq : T' = T := hTsyl.eq_of_le hTT' (hT'syl.1.trans hNL) hT'2
  have hT'M : IsSylowTwoIn T' M := hTeq ▸ hTsyl
  have hcent' : ∀ s ∈ T', s * z = z * s := fun s hs => hzc s (hTeq ▸ hs)
  have hLM : L ≤ M := le_normalizer.trans hNL
  have hOJ : oddIn J ≤ oddIn M := by
    rw [GrS4.oddIn_eq_inf_of_singleComponentSetting hs]
    exact inf_le_right
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hKL' : K ≤ L ⊔ oddIn M :=
    (le_of_eq hKsup.symm).trans (sup_le ((le_of_eq hTJs.symm).trans
      (sup_le (hTL.trans le_sup_left) (hOJ.trans le_sup_right))) (hOK.trans le_sup_right))
  have hLK : L ≤ K ⊔ oddIn M :=
    le_of_sup_oddIn_eq_of_normalizer hLper hTL hTLs (hTJJ.trans (hJK.trans le_sup_left))
      (hLM.trans (le_normalizer_sup_oddIn hKN))
  have hsup' : L ⊔ oddIn M = K ⊔ oddIn M :=
    le_antisymm (sup_le hLK le_sup_right) (sup_le hKL' le_sup_right)
  exact false_of_kSylow46 hMax hSol h45 hU hC hCF hZS hCl hGold hset' hcent' hZ' hrun' h3' hexp'
    hcyc' hW hWodd hWE' hNL hKM hKc hsup' hKN hT'M

end CFSG.ComponentClassification.GrSLit.KSw

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem l34Lemma46FrattiniStep_of_inputs
    (hMax : MaximalTwoComponentInput) (hS : SchreierFor Blueprint.Catalog)
    (hFixL : SolomonFixedLayerStep) (hSol : SolomonCommutingCoreInput) (h44 : L34Lemma44)
    (h45 : L34Lemma45) (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact)
    (hCF : L34CentralFourFact) (hZS : L34Lemma46CenterStep) (hCl : L34Lemma46ClosedStep)
    (hGold : GoldschmidtStronglyClosedInput) : L34Lemma46FrattiniStep := by
  intro G _ _ a x J S A hset hcent hZ _ h3 hexp hcyc W hW hWodd hWE hNJ K hKM hKc _ hsup
  exact (KSw.false_of_frattini46 hMax hS hFixL hSol h44 h45 hU hC hCF hZS hCl hGold hset hcent
    hZ h3 hexp hcyc hW hWodd hWE hNJ hKM hKc hsup).elim

end CFSG.ComponentClassification.GrSLit
