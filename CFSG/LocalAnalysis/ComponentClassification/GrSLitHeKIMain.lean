module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMInvol
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInvCent
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34
public import Certificates.Certificate2020
public import Certificates.Certificate2022
public import Certificates.Certificate2110
public import Certificates.Certificate2111
public import Certificates.Certificate2112
public import Certificates.Certificate2114
public import Certificates.Certificate2115
public import Certificates.Certificate2116
public import Certificates.Certificate2117
public import Certificates.Certificate2118
public import Certificates.Certificate2223
public import Certificates.Certificate2224
public import Certificates.Certificate2225
public import Certificates.Certificate2275
public import Certificates.Certificate2276
public import Certificates.Certificate3007
public import Certificates.Certificate3168
public import Certificates.Certificate10005
public import Certificates.Certificate22200
public import Certificates.Certificate22201
public import Certificates.Certificate22203
public import Certificates.Certificate22205
public import Certificates.Certificate22701
public import Certificates.Certificate22703
public import Certificates.Certificate22704
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeGS36
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKDMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKPCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeUSetup
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeW
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.Open.QuasithinDefs
public import CFSG.Walter.J1
public import Certificates.Certificate22705

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

theorem heldKInvariantComponentStep
    : HeldKInvariantComponentStep := by
  intro X _ _ L hset a u J ha hLa hLc hu hKc hJC hJc hJK ⟨ψ⟩ hJa haJ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨e⟩, hrank⟩ := id hset
  set K := gsFixedLayer L u with hKdef
  set Cu := centralizer ({u} : Set X) with hCu
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    norm_num at ha
  have hKL : K ≤ L := (gsFixedLayer_le_inf L u).trans inf_le_left
  have hKC : K ≤ Cu := (gsFixedLayer_le_inf L u).trans inf_le_right
  have haL : a ∈ centralizer (L : Set X) :=
    mem_centralizer_iff.mpr fun l hl => mem_centralizer_singleton_iff.mp (hLa hl)
  have hJq : IsQuasisimple ↥J :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJC) hJc.1
  have hKq : IsQuasisimple ↥K :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKC) hKc.1
  have hJp : ⁅J, J⁆ = J := isPerfect_iff.mp hJq.1
  have hOK : pPrimeCore 2 ↥K ≤ center ↥K := by
    rcases LocalCores.quasisimple_normal_subgroups hKq
        (inferInstance : (pPrimeCore 2 ↥K).Normal) with h | h
    · exfalso
      have hodd : Odd (Nat.card (pPrimeCore 2 ↥K)) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      rw [h, card_top, HeZ.card_gsFixedLayer heldTwoALayerFact heldTwoAKFact ⟨e⟩ hu] at hodd
      exact absurd hodd (by decide)
    · exact h
  have hZK : Open.fusionZStar ↥K = center ↥K :=
    GrS5.fusionZStar_eq_center_of_le hKq.1.commutator_eq_top hOK
  have hKt : IsL34Type (↥K ⧸ Open.fusionZStar ↥K) :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZK).symm
      (heldTwoALayerFact X L ⟨e⟩ u hu).2
  obtain ⟨φ⟩ := nonempty_fusionZStar_equiv_of_mulEquiv' ψ.symm
  have hJt : IsL34Type (↥J ⧸ Open.fusionZStar ↥J) := LieType.CurtisTits.lieModel_of_mulEquiv φ hKt
  have haN : a ∈ normalizer (J : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    show x ∈ J ↔ a * x * a⁻¹ ∈ J
    rw [← HeKP.mem_conjugate, hJa]
  obtain ⟨w, hwJ, hww, hwa, hwZ, hwK⟩ :=
    L34Facts.l34InvolutionCentralizerFact X J a hJp hJt haa haN
  have hJK' := HeKP.commute_of_components hJC hKC hJc hKc hJK
  have hwKc : ∀ k ∈ K, w * k = k * w := fun k hk => hJK' w hwJ k hk
  obtain ⟨y, hyU, hyc⟩ := HeKM.exists_center_mul_of_involution hset ha hLa hu hww
    (mem_centralizer_singleton_iff.mpr hwa) hwKc
  have hyK : y ∈ K := map_subtype_le _ hyU
  have hyy : y * y = 1 := by
    obtain ⟨-, -, hAK⟩ := heldTwoAKFact X L ⟨e⟩ u hu
    rcases hAK y (hKL hyK) (fun k hk => by
      obtain ⟨y', hy', rfl⟩ := hyU
      exact congrArg Subtype.val (mem_center_iff.mp hy' ⟨k, hk⟩).symm) with h | ⟨h, -⟩
    · rw [h, one_mul]
    · have h3 := pow_orderOf_eq_one y
      rw [h.2.1, pow_two] at h3
      exact h3
  have hyw : y * w = w * y := (hwKc y hyK).symm
  set c := y⁻¹ * w with hc
  have hcc : c * c = 1 := by
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
    rw [hc, hyinv]
    calc y * w * (y * w) = y * (w * y) * w := by group
      _ = y * (y * w) * w := by rw [hyw]
      _ = (y * y) * (w * w) := by group
      _ = 1 := by rw [hyy, hww, one_mul]
  have hc1 : c ≠ 1 := by
    intro h
    apply hwZ
    rw [hc, inv_mul_eq_one] at h
    apply GrS4.mem_zStarIn_of_le_centralizer hwJ
    intro j hj
    rw [mem_centralizer_singleton_iff, ← h]
    exact hJK' j hj y hyK
  have hca : c ≠ a := by
    intro h
    apply hwK
    have h1 : w⁻¹ * a = y⁻¹ := by
      rw [← h, hc]
      calc w⁻¹ * (y⁻¹ * w) = w⁻¹ * (w * y⁻¹) := by
            rw [(Commute.inv_left (show Commute y w from hyw)).eq]
        _ = y⁻¹ := by group
    rw [h1]
    apply GrS4.mem_coreActionKernel_of_le_centralizer
    intro j hj
    rw [mem_centralizer_singleton_iff]
    exact hJK' j hj _ (inv_mem hyK)
  have hac : a * c = c * a := by
    have h1 : Commute a y := (mem_centralizer_singleton_iff.mp (hLa (hKL hyK))).symm
    have h2 : Commute a w := hwa.symm
    exact (h1.inv_right.mul_right h2).eq
  exact HeZ.false_of_pair hrank haL hyc haa hcc ha1 hc1 (Ne.symm hca) hac

end CFSG.ComponentClassification.GrSLit
