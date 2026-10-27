module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionTripleSylowGeometry

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow

open CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u

variable {G : Type u} [Group G]

theorem odd_central_kernel_restriction
    (P J₀ E K : Subgroup G) (z : G)
    (hJ₀P : J₀ ≤ P) (hKP : K ≤ P) (hEK : E ≤ K) (hzK : z ∈ K)
    (hgenerated : E ⊔ Subgroup.zpowers z = K)
    (hJnormal : (J₀.subgroupOf P).Normal)
    (hEnormal : (E.subgroupOf K).Normal)
    (hJodd : Odd (Nat.card J₀))
    (hcentral : letI := hJnormal;
      (QuotientGroup.mk (⟨z, hKP hzK⟩ : P) : P ⧸ J₀.subgroupOf P) ∈
        Subgroup.center (P ⧸ J₀.subgroupOf P)) :
    let J := E ⊓ J₀
    let JK := J.subgroupOf K
    ∃ hJK : JK.Normal,
      Odd (Nat.card J) ∧ Odd (Nat.card JK) ∧
      J ≤ E ∧ J ≤ K ∧
      (letI := hJK;
        (QuotientGroup.mk (⟨z, hzK⟩ : K) : K ⧸ JK) ∈ Subgroup.center (K ⧸ JK)) := by
  let J := E ⊓ J₀
  let JK := J.subgroupOf K
  have hKNE : K ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mp hEnormal
  have hKNJ : K ≤ Subgroup.normalizer (J₀ : Set G) :=
    hKP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJ₀P).mp hJnormal)
  have hJKnormal : JK.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (show J ≤ K from inf_le_left.trans hEK)).mpr
      ((le_inf hKNE hKNJ).trans Subgroup.inf_normalizer_le_normalizer_inf)
  have hodd : Odd (Nat.card J) :=
    hJodd.of_dvd_nat (Subgroup.card_dvd_of_le (show J ≤ J₀ from inf_le_right))
  have hJKodd : Odd (Nat.card JK) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show J ≤ K from inf_le_left.trans hEK)).toEquiv]
    exact hodd
  refine ⟨hJKnormal, hodd, hJKodd, inf_le_left, inf_le_left.trans hEK, ?_⟩
  let _ := hJnormal
  let _ := hEnormal
  let _ := hJKnormal
  apply Subgroup.mem_center_iff.mpr
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  let zK : K := ⟨z, hzK⟩
  let kP : P := ⟨k, hKP k.property⟩
  let zP : P := ⟨z, hKP hzK⟩
  have hdJ : (kP * zP)⁻¹ * (zP * kP) ∈ J₀.subgroupOf P := by
    apply QuotientGroup.eq.mp
    simpa only [QuotientGroup.mk_mul] using
      Subgroup.mem_center_iff.mp hcentral (QuotientGroup.mk kP : P ⧸ J₀.subgroupOf P)
  have hdE : (k * zK)⁻¹ * (zK * k) ∈ E.subgroupOf K := by
    have htop : E.subgroupOf K ⊔ Subgroup.zpowers zK = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEK,
        MonoidHom.map_zpowers, Subgroup.map_top, K.range_subtype]
      exact hgenerated
    have hk : k ∈ E.subgroupOf K ⊔ Subgroup.zpowers zK := by
      rw [htop]
      exact Subgroup.mem_top k
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    let qE := QuotientGroup.mk' (E.subgroupOf K)
    have haone : qE a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
    have hkpow : qE k = qE zK ^ n := by
      rw [← hab, map_mul, haone, one_mul, map_zpow]
    apply (QuotientGroup.eq_one_iff _).mp
    change qE ((k * zK)⁻¹ * (zK * k)) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hkpow]
    rw [((show Commute (qE zK) (qE zK) from rfl).zpow_right n).eq]
    exact inv_mul_cancel _
  have hdJK : (k * zK)⁻¹ * (zK * k) ∈ JK := ⟨hdE, hdJ⟩
  have hquot : (QuotientGroup.mk (k * zK) : K ⧸ JK) = QuotientGroup.mk (zK * k) :=
    QuotientGroup.eq.mpr hdJK
  simpa only [QuotientGroup.mk_mul] using hquot

theorem opposite_pair_odd_central_quotient [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (x : G) (hx : rightCosetMk H x ≠ rightCosetMk H 1) :
    let Hx := rightConjugate H x
    let beta₀ := rightCosetMk Hx z
    let P := pairFlipGroup Hx beta₀ z
    let J₀ := pairOddCore Hx beta₀
    ∃ hnormal : (J₀.subgroupOf P).Normal,
      Odd (Nat.card J₀) ∧ J₀ ≤ P ∧
      (letI := hnormal;
        (QuotientGroup.mk (⟨z, flip_mem_pairFlipGroup Hx beta₀ z⟩ : P) :
            P ⧸ J₀.subgroupOf P) ∈ Subgroup.center (P ⧸ J₀.subgroupOf P)) := by
  let Hx := rightConjugate H x
  let beta₀ := rightCosetMk Hx z
  let P := pairFlipGroup Hx beta₀ z
  let J₀ := pairOddCore Hx beta₀
  have hxdatum := local_embedding_right_conjugate h x
  have hbeta₀ := opposite_point_ne_base h hx
  have hflip := distinguished_mem_opposite_pair_fiber H z x
  obtain ⟨T, _, hzT, hTcenter⟩ := central_sylow_right_conjugate S hzS hzcenter x
  have hnormal := pairOddCore_normal_in_pair_group hxdatum.distinguished_order hbeta₀ hflip
  refine ⟨hnormal, pairOddCore_odd Hx beta₀, (pairOddCore_le Hx beta₀ z).2.1, ?_⟩
  exact (pair_flip_zStar_factorization hxdatum T hzT hTcenter hbeta₀ hflip).1

theorem triple_opposite_kernel_odd_central_quotient [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (x : G) (hx : rightCosetMk H x ≠ rightCosetMk H 1) :
    let E := triplePointStabilizer H z (rightCosetMk H x)
    let K := E ⊔ Subgroup.zpowers z
    let J₀ := pairOddCore (rightConjugate H x) (rightCosetMk (rightConjugate H x) z)
    let J := E ⊓ J₀
    ∃ hnormal : (J.subgroupOf K).Normal,
      Odd (Nat.card J) ∧ Odd (Nat.card (J.subgroupOf K)) ∧ J ≤ E ∧
      (letI := hnormal;
        (QuotientGroup.mk (⟨z,
          (show Subgroup.zpowers z ≤ K from le_sup_right) (Subgroup.mem_zpowers z)⟩ : K) :
            K ⧸ J.subgroupOf K) ∈ Subgroup.center (K ⧸ J.subgroupOf K)) := by
  let E := triplePointStabilizer H z (rightCosetMk H x)
  let K := E ⊔ Subgroup.zpowers z
  let Hx := rightConjugate H x
  let beta₀ := rightCosetMk Hx z
  let P := pairFlipGroup Hx beta₀ z
  let J₀ := pairOddCore Hx beta₀
  have hEPair : E ≤ pairPointStabilizer Hx beta₀ := by
    rw [opposite_pair_stabilizer_eq]
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hKP : K ≤ P := sup_le (hEPair.trans le_sup_left) le_sup_right
  obtain ⟨hnormal, hodd, hJ₀P, hcentral⟩ := opposite_pair_odd_central_quotient h S hzS hzcenter x hx
  obtain ⟨hJK, hJodd, hJKodd, hJE, _, hKcentral⟩ := odd_central_kernel_restriction
    P J₀ E K z hJ₀P hKP le_sup_left
    ((show Subgroup.zpowers z ≤ K from le_sup_right) (Subgroup.mem_zpowers z)) rfl
    hnormal (triple_stabilizer_normal_in_generated h (rightCosetMk H x)) hodd hcentral
  exact ⟨hJK, hJodd, hJKodd, hJE, hKcentral⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionTripleSylow
