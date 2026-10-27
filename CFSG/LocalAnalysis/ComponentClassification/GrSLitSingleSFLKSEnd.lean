module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleSFLZOne
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd43
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46
public import CFSG.LocalAnalysis.ComponentClassification.Sol78PSp4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4DiagMem
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SHoltX
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSInputs
import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypG
import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn
import CFSG.LocalAnalysis.ComponentClassification.GrSLitWGroup
import CFSG.LocalAnalysis.ComponentClassification.CatLeafAlt
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End46F
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.GrSLit.GrS4

theorem l34Lemma43EndStep_of_kSylow_holtSimple
    (hMax : MaximalTwoComponentInput) (hKS : L34Lemma43KSylowStep) (hHe : L34Lemma43HeldStep)
    (hSyl : L34Lemma43SylowStepKS) (hFus : L34Lemma43FusionStepKS)
    (hHS : RankThree.PartTwo.Sec21.HoltUniqueFixedPointSimple) : L34Lemma43EndStep := by
  intro G _ _ a x J S A hset hcent hZ hrun h3 W hW hWodd hWB hNJ K hKM hKc hcase
  obtain ⟨hbase, hU3, hL34, hmax, hS, haS, hxS⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  have : IsSimpleGroup G := hsimple
  have ha2 : orderOf a = 2 := hU3.1
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJc := hU3.2.2.2.2.1
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  have hMtop : M ≠ ⊤ := normalizer_ne_top_of_odd hW hWodd ha2
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    centralizer_le_normalizer_of_gsMaximalSetting hMax hgs
  have hCaM : centralizer ({a} : Set G) ≤ M := hCaN.trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨hKL, hsup⟩ : IsL34Type (K ⧸ Open.fusionZStar K) ∧ J ⊔ oddIn M = K ⊔ oddIn M := by
    rcases hcase with ⟨hKL, hsup⟩ | ⟨he, hJKO⟩ | ⟨hKL, hKa, hJKK⟩
    · exact ⟨hKL, hsup⟩
    · exact (hHe G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc he hJKO).elim
    · exfalso
      have hN := (hKS G a x J S A hset hcent hZ hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL
        (Or.inr ⟨hKa, hJKK⟩)).1
      exact hKa (Single.conjugate_eq_of_mem_normalizer (hN haM))
  obtain ⟨hKN, hSM⟩ := hKS G a x J S A hset hcent hZ hrun h3 W hW hWodd hWB hNJ K hKM hKc hKL
    (Or.inl hsup)
  obtain ⟨T, hTS⟩ := hSyl G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc hsup hKN
    hSM
  have hfus := hFus G a x J S A hset hcent hrun h3 W hW hWodd hWB hNJ K hKM hKc hsup hKN hSM
    ⟨T, hTS⟩
  have hfix : ∃! ω : G ⧸ M, a • ω = ω := by
    refine ⟨QuotientGroup.mk 1, ?_, fun ω' hω' => ?_⟩
    · show a • (QuotientGroup.mk 1 : G ⧸ M) = QuotientGroup.mk 1
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
      simpa using inv_mem haM
    induction ω' using QuotientGroup.induction_on with
    | H g =>
    have h : a • (QuotientGroup.mk g : G ⧸ M) = QuotientGroup.mk g := hω'
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
    rw [QuotientGroup.eq, mul_one]
    have h1 : g⁻¹ * a * g ∈ M := by
      have h2 := inv_mem h
      rwa [show ((a * g)⁻¹ * g)⁻¹ = g⁻¹ * a * g by group] at h2
    obtain ⟨m, hm, hgm⟩ := hfus g h1
    have hc : g * m⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * m⁻¹ * a = g * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * m⁻¹ := by rw [← hgm]
        _ = a * (g * m⁻¹) := by group
    have h3 := mul_mem (hCaM hc) hm
    rw [inv_mul_cancel_right] at h3
    exact inv_mem h3
  have hTa : ∃ T' : Sylow 2 G, a ∈ (T' : Subgroup G) ∧
      (T' : Subgroup G) ≤ centralizer ({a} : Set G) :=
    ⟨T, by rw [hTS]; exact haS, by
      rw [hTS]
      exact fun s hs => mem_centralizer_singleton_iff.mpr (hcent s hs)⟩
  rcases hHS G hnab M hMtop a ha2 hTa hfix with ⟨M', hM'⟩ | ⟨n, -, ⟨e⟩⟩
  · obtain ⟨-, ⟨hAe, hA8⟩, -⟩ := hrun
    obtain ⟨V, hVA, hV4⟩ := exists_le_card_four hAe.isPGroup (by omega)
    have hJ1 : J ≠ ⊥ := by
      intro hJb
      have hd : Nat.card (↥J ⧸ Open.fusionZStar ↥J) ∣ Nat.card ↥J :=
        Subgroup.card_quotient_dvd_card _
      rw [CatLeaf.card_of_isL34Type hL34, hJb, Subgroup.card_bot] at hd
      norm_num at hd
    exact false_of_isStronglyEmbedded_perfect hM' hV4
      (fun v hv => by rw [pow_two]; exact hAe.2 v (hVA hv)) ha2 hJa
      (GSThmB.commutator_eq_self_of_isPComponent hJa hJc) hJ1
  · exact false_of_mulEquiv_alternatingGroup_l34 e ha2 hJa hCaN hJc hL34

end CFSG.ComponentClassification.GrSLit.GrS5S

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS GrS4

theorem l34Lemma46EndStep_of_frattini46
    (hMax : MaximalTwoComponentInput) (hSol : SolomonCommutingCoreInput)
    (hF46 : L34Lemma46FrattiniStep) (hHe : L34HeldCenterFact)
    (h45 : L34Lemma45) (hU : L34UnbalancingUnitaryStep) (hC : L34UnitaryCentralizerFact)
    (hCF : L34CentralFourFact) (hZS : L34Lemma46CenterStep) (hCl : L34Lemma46ClosedStep)
    (hGold : GoldschmidtStronglyClosedInput) : L34Lemma46EndStep := by
  intro G _ _ a x J S A hset hcent hZ hrun h3 hexp hcyc W hW hWodd hWE hNJ K hKM hKc hcase
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
  have hMtop : M ≠ ⊤ := normalizer_ne_top_of_odd hW hWodd ha2
  have hCaM : centralizer ({a} : Set G) ≤ M :=
    (centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  have hJM : J ≤ M := le_normalizer.trans hNJ
  obtain ⟨hKL, hsup⟩ : IsL34Type (K ⧸ Open.fusionZStar K) ∧ J ⊔ oddIn M = K ⊔ oddIn M := by
    rcases hcase with ⟨hKL, hsup⟩ | ⟨he, hJKO⟩ | ⟨-, hKa, hJKK⟩
    · exact ⟨hKL, hsup⟩
    · exfalso
      have hinf : M ⊓ centralizer ({a} : Set G) = centralizer ({a} : Set G) :=
        inf_eq_right.mpr hCaM
      have hJc' : IsPComponent 2 (J.subgroupOf (M ⊓ centralizer ({a} : Set G))) := by
        rw [hinf]
        exact hJc
      have hsq := hHe G M K J a hKM hKc he haM ha2 (le_inf hJM hJa) hJc' hL34 hJKO
      obtain ⟨z, hzZ, hz⟩ := exists_sq_ne_one_of_exponent_eq_four hexp
      apply hz
      have hbot := eq_bot_of_le_two_group_of_le_odd (isPGroup_of_isSylowTwoIn hS)
        (odd_card_map_pPrimeCore J)
        (zpowers_le.mpr (mul_mem (mem_inf.mp hzZ).1 (mem_inf.mp hzZ).1))
        (zpowers_le.mpr (hsq z (mem_inf.mp hzZ).2))
      have h1 : z * z ∈ zpowers (z * z) := mem_zpowers _
      rwa [hbot, mem_bot] at h1
    · exfalso
      obtain ⟨z, hzZ, hz⟩ := exists_sq_ne_one_of_exponent_eq_four hexp
      have hZne : S ⊓ zStarIn J ≠ ⊥ := fun h => hz (by
        rw [h, mem_bot] at hzZ
        rw [hzZ, one_mul])
      exact diagonal_false_of_mem hKM hKc haM hKa hJKK
        ((map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp (hZ hZne)).2)
  have hsc : SingleComponentSetting G a J W K :=
    { toGSMaximalSetting := hgs, ne_bot := hW, odd_card := hWodd, normalizer_le := hNJ,
      normalizer_ne_top := hMtop, le_normalizer := hKM, isPComponent_K := hKc, sup_eq := hsup }
  have haJ : a ∈ J := by
    obtain ⟨z, hzZ, hz⟩ := exists_sq_ne_one_of_exponent_eq_four hexp
    have hZne : S ⊓ zStarIn J ≠ ⊥ := fun h => hz (by
      rw [h, mem_bot] at hzZ
      rw [hzZ, one_mul])
    exact (map_subtype_le _ : zStarIn J ≤ J) (mem_inf.mp (hZ hZne)).2
  have hMO : M ≤ oddIn M ⊔ normalizer (J : Set G) :=
    hF46 G a x J S A hset hcent hZ hrun h3 hexp hcyc W hW hWodd hWE hNJ K hKM hKc hKL hsup
  have hSM : IsSylowTwoIn S M := isSylowTwoIn_of_le_oddIn_sup hS hNJ hMO
  have hJ1 : ((oddIn M ⊔ J).subgroupOf M).Normal := normal_oddIn_sup_of_le hJM hNJ hMO
  have hJper : ⁅J, J⁆ = J := commutator_eq_of_isPComponent hJa hJc
  have hSN : S ≤ normalizer (J : Set G) := hS.1
  set P : Subgroup G := S ⊓ J with hPdef
  have hP : IsSylowTwoIn P J := isSylowTwoIn_inf hS
  have hZJ : zStarIn J ≤ J := map_subtype_le _
  have hZP : P ⊓ zStarIn J = S ⊓ zStarIn J := by
    rw [hPdef, inf_assoc, inf_eq_right.mpr hZJ]
  have hxU : IsL34Unitary J x := hU G a x J hU3 hL34
  have hxP : x ∈ normalizer (P : Set G) := inf_mem_normalizer (le_normalizer hxS) (hSN hxS)
  obtain ⟨-, h8, -, -, -, hel, -, -⟩ := hC G J P x hJper hL34 hxU hP hxP
  have hR : IsEightGroup (P ⊓ centralizer ({x} : Set G)) := ⟨hel (by rwa [hZP]), h8⟩
  obtain ⟨C, -, hCe, -, hRC, -, hNC⟩ := hCF G J P x hJper hL34 hP hxU hxP (by rwa [hZP])
    (by rw [hZP]; exact exists_sq_ne_one_of_exponent_eq_four hexp)
  have hWC : wGroup C = W := (wGroup_eq_of_le_eight hGW hCe hRC hR.2).trans hWE
  have hNP : normalizer (P : Set G) ≤ M := fun n hn => by
    have h1 := mem_normalizer_wGroup (hNC hn)
    rwa [hWC] at h1
  have hOJ : oddIn J ≤ oddIn M := by
    rw [oddIn_eq_inf_of_singleComponentSetting hsc]
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
    have hcond := mem_zStarIn_oddIn_sup hJM hOJ (hSM.1 hbS) hbJ
    obtain ⟨m, hm, hbm⟩ := h45 G a x J S hset M hJM hJ1 hSM (fun s hs => (hcent s hs).symm)
      hNP y (hSM.1 hbS) hcond
    have hc : y * m⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc y * m⁻¹ * a = y * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = y * (y⁻¹ * a * y) * m⁻¹ := by rw [← hbm]
        _ = a * (y * m⁻¹) := by group
    have h1 := mul_mem (hCaM hc) hm
    rwa [inv_mul_cancel_right] at h1
  obtain ⟨T, hTS⟩ := exists_sylow_eq_of_normalizer_le_of_isSylowTwoIn hSM hNS
  obtain ⟨B, hBZ, hB, hBsc⟩ := hCl G a x J S A hset hcent hZ hrun h3 hexp hcyc W hW hWodd hWE
    hNJ (GrS4.l34ZConjClosed_of_le_sup hNJ hMO hSN) hNS ⟨T, hTS⟩
  refine false_of_stronglyClosed_le_zStarIn hGold hnab T hJa hJc (hBZ.trans inf_le_right)
    (by rw [hTS]; exact hBZ.trans inf_le_left) hB ?_
  rw [hTS]
  exact hBsc

end CFSG.ComponentClassification.GrSLit
