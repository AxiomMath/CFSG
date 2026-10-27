module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OrderCount
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Final
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCores
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUAction

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open Equiv Equiv.Perm CFSG.Sporadic.Th.Max3 CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
include d htype

theorem isConj_iff_isConj_of_labels {w : J ⧸ Subgroup.center J}
    (φ : Subgroup.centralizer {w} →* alternatingGroup (Fin 9)) (hinj : Function.Injective φ)
    (h4 : ∀ s : Subgroup.centralizer {w}, s ≠ 1 →
      CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2, 2, 2})
    (h2 : ∀ s : Subgroup.centralizer {w}, s * s = 1 →
      ¬ CaseC3.Genuine (Subgroup.center J) (s : J ⧸ Subgroup.center J) →
      ((φ s : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = {2, 2})
    (c : Subgroup.centralizer {w}) :
    (IsConj (u : J ⧸ Subgroup.center J) (c : J ⧸ Subgroup.center J) ↔ IsConj altRep2A (φ c)) ∧
      (IsConj (caseC3Word (Subgroup.center J) u m y x 40) (c : J ⧸ Subgroup.center J) ↔
        IsConj altRep4A (φ c)) := by
  have hφsq : φ c * φ c = 1 → c * c = 1 := fun h => hinj (by rw [map_mul, h, map_one])
  have hφne : ∀ μ : Multiset ℕ, μ ≠ 0 →
      ((φ c : alternatingGroup (Fin 9)) : Perm (Fin 9)).cycleType = μ → c ≠ 1 :=
    fun μ hμ h hc => hμ (by rw [← h, hc, map_one, OneMemClass.coe_one, cycleType_one])
  have hsq : ∀ {a : J ⧸ Subgroup.center J}, a * a = 1 → IsConj a (c : J ⧸ Subgroup.center J) →
      c * c = 1 := fun ha h => Subtype.ext (mul_self_eq_one_of_isConj ha h)
  have hne : ∀ {a : J ⧸ Subgroup.center J}, a ≠ 1 → IsConj a (c : J ⧸ Subgroup.center J) →
      (c : J ⧸ Subgroup.center J) ≠ 1 := fun ha h hc => ha (isConj_one_left.mp (hc ▸ h))
  have hφsq' : c * c = 1 → φ c * φ c = 1 := fun h => by rw [← map_mul, h, map_one]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · have hcc := hsq d.self_mul_self h
    have hng := (d.isConj_self_iff htype (congrArg Subtype.val hcc) (hne d.self_ne_one h)).mp h
    exact (isConj_altRep2A_iff _).mpr ⟨hφsq' hcc, h2 c hcc hng⟩
  · obtain ⟨hs, hct⟩ := (isConj_altRep2A_iff _).mp h
    have hcc := hφsq hs
    have hc1 := hφne _ (by decide) hct
    refine (d.isConj_self_iff htype (congrArg Subtype.val hcc)
      (fun h' => hc1 (Subtype.ext h'))).mpr fun hg => ?_
    rw [h4 c hc1 hg] at hct
    exact absurd hct (by decide)
  · have hcc := hsq d.caseC3BCD.forty_mul_self h
    have hc1 := hne d.forty_ne_one h
    have hg := (d.isConj_forty_iff htype (congrArg Subtype.val hcc) hc1).mp h
    exact (isConj_altRep4A_iff _).mpr ⟨hφsq' hcc, h4 c (fun h' => hc1 (congrArg Subtype.val h')) hg⟩
  · obtain ⟨hs, hct⟩ := (isConj_altRep4A_iff _).mp h
    have hcc := hφsq hs
    have hc1 := hφne _ (by decide) hct
    refine (d.isConj_forty_iff htype (congrArg Subtype.val hcc)
      (fun h' => hc1 (Subtype.ext h'))).mpr (by_contra fun hg => ?_)
    rw [h2 c hcc hg] at hct
    exact absurd hct (by decide)

theorem orderOf_self_forty_facts :
    orderOf (u : J ⧸ Subgroup.center J) = 2 ∧
      orderOf (caseC3Word (Subgroup.center J) u m y x 40) = 2 ∧
      ¬ IsConj (u : J ⧸ Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x 40) ∧
      ∀ t : J ⧸ Subgroup.center J, orderOf t = 2 → IsConj (u : J ⧸ Subgroup.center J) t ∨
        IsConj (caseC3Word (Subgroup.center J) u m y x 40) t := by
  refine ⟨orderOf_eq_prime (by rw [pow_two]; exact d.self_mul_self) d.self_ne_one,
    orderOf_eq_prime (by rw [pow_two]; exact d.caseC3BCD.forty_mul_self) d.forty_ne_one,
    fun h => d.not_isConj_forty_self (isConj_comm.mp h), fun t ht => ?_⟩
  have htt := mul_self_eq_one_of_orderOf_eq_two ht
  have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; exact absurd ht (by decide)
  by_cases hg : CaseC3.Genuine (Subgroup.center J) t
  · exact Or.inr ((d.isConj_forty_iff htype htt ht1).mpr hg)
  · exact Or.inl ((d.isConj_self_iff htype htt ht1).mpr hg)

variable (hOu : CFSG.pPrimeCore 2 (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = ⊥)
include hOu

theorem thompsonPairCount_self_eq :
    thompsonPairCount (u : J ⧸ Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x 40)
      (u : J ⧸ Subgroup.center J) = thompsonPairCount altRep2A altRep4A altRep2A := by
  have hinj := (d.phiU_bijective_of_oddCore_eq_bot hOu).1
  obtain ⟨-, -, -, h4, h2, -⟩ := d.phiU_spec
  exact thompsonPairCount_eq_of_injective d.self_mul_self d.caseC3BCD.forty_mul_self
    d.self_mul_self altRep2A_mul_self altRep4A_mul_self altRep2A_mul_self d.phiU hinj
    d.range_phiU d.phiU_self (fun c => (d.isConj_iff_isConj_of_labels htype _ hinj h4 h2 c).1)
    (fun c => (d.isConj_iff_isConj_of_labels htype _ hinj h4 h2 c).2)

omit htype in
theorem card_centralizer_self_of_pPrimeCore :
    Nat.card (Subgroup.centralizer {(u : J ⧸ Subgroup.center J)}) = 480 :=
  (Nat.card_congr (d.nonempty_mulEquiv_of_oddCore_eq_bot hOu).some.toEquiv).trans
    card_centralizer_altRep2

variable (hOz : CFSG.pPrimeCore 2
  (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) = ⊥)
include hOz

theorem thompsonPairCount_forty_eq :
    thompsonPairCount (u : J ⧸ Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x 40)
      (caseC3Word (Subgroup.center J) u m y x 40) =
        thompsonPairCount altRep2A altRep4A altRep4A := by
  obtain ⟨hinj, hrange, hz, h4, h2⟩ := d.phiZ_spec htype hOu hOz
  exact thompsonPairCount_eq_of_injective d.self_mul_self d.caseC3BCD.forty_mul_self
    d.caseC3BCD.forty_mul_self altRep2A_mul_self altRep4A_mul_self altRep4A_mul_self _ hinj hrange
    hz (fun c => (d.isConj_iff_isConj_of_labels htype _ hinj h4 h2 c).1)
    (fun c => (d.isConj_iff_isConj_of_labels htype _ hinj h4 h2 c).2)

theorem card_quotient_center_of_pPrimeCore :
    Nat.card (J ⧸ Subgroup.center J) = 181440 := by
  obtain ⟨hu, hz, huz, hcl⟩ := d.orderOf_self_forty_facts htype
  have hJ := card_eq_of_thompsonPairCount_support hu hz huz fun t ht h1 h2 =>
    absurd (hcl t ht) (not_or.mpr ⟨h1, h2⟩)
  rw [d.card_centralizer_forty_of_pPrimeCore htype hOz,
    d.card_centralizer_self_of_pPrimeCore hOu, d.thompsonPairCount_self_eq htype hOu,
    d.thompsonPairCount_forty_eq htype hOu hOz] at hJ
  have hA := card_alternatingGroup_nine_eq
  rw [card_centralizer_altRep4, card_centralizer_altRep2] at hA
  rw [hJ, ← hA, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem nonempty_mulEquiv_alternating_of_oddCores :
    Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) :=
  d.nonempty_mulEquiv_alternating_of_card htype (d.card_centralizer_forty_of_pPrimeCore htype hOz)
    (d.card_quotient_center_of_pPrimeCore htype hOu hOz)

omit hOu hOz in
theorem nonempty_mulEquiv_alternating_of_typeD :
    Nonempty ((J ⧸ Subgroup.center J) ≃* alternatingGroup (Fin 9)) :=
  d.nonempty_mulEquiv_alternating_of_oddCores htype
    (d.pPrimeCore_centralizer_eq_bot htype d.self_mul_self d.self_ne_one)
    (d.pPrimeCore_centralizer_eq_bot htype d.caseC3BCD.forty_mul_self d.forty_ne_one)

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
