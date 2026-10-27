module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTwoOne
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineNumericRank

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffine
  (twoRank_le_one_of_not_twoRankAtLeastTwo)

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem centralizer_le_of_class_mem (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    {s : G} (hs : s ∈ involutionPointClass z) (hsH : s ∈ H) :
    Subgroup.centralizer ({s} : Set G) ≤ H := by
  obtain ⟨g, rfl⟩ := hs
  change g⁻¹ * z * g ∈ H at hsH
  have hgH : g ∈ H := (conj_mem_iff huniq g).mp hsH
  intro c hc
  have hcomm : Commute c (g⁻¹ * z * g) := Subgroup.mem_centralizer_singleton_iff.mp hc
  have h := hcomm.map (MulAut.conj g).toMonoidHom
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  have hz' : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
  rw [hz'] at h
  have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr h.eq
  have hmem := H.mul_mem (H.mul_mem (H.inv_mem hgH) (centralizer_le_of_unique huniq hc')) hgH
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hmem

@[expose] def commutingPairSubgroup (s t : G) (hs : s * s = 1) (ht : t * t = 1)
    (hst : Commute s t) : Subgroup G where
  carrier := {1, s, t, s * t}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have hts : t * s = s * t := hst.eq.symm
    have h1 : s * (s * t) = t := by rw [← mul_assoc, hs, one_mul]
    have h2 : t * (s * t) = s := by rw [← mul_assoc, hts, mul_assoc, ht, mul_one]
    have h3 : s * t * s = t := by rw [mul_assoc, hts, ← mul_assoc, hs, one_mul]
    have h4 : s * t * t = s := by rw [mul_assoc, ht, mul_one]
    have h5 : s * t * (s * t) = 1 := by rw [← mul_assoc, h3, ht]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp_all
  inv_mem' := by
    intro a ha
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · simp [hsinv]
    · simp [htinv]
    · right; right; right
      rw [mul_inv_rev, hsinv, htinv, hst.eq]

theorem mem_commutingPairSubgroup {s t : G} {hs : s * s = 1} {ht : t * t = 1}
    {hst : Commute s t} {a : G} :
    a ∈ commutingPairSubgroup s t hs ht hst ↔ a = 1 ∨ a = s ∨ a = t ∨ a = s * t := Iff.rfl

theorem commutingPairSubgroup_sq {s t : G} {hs : s * s = 1} {ht : t * t = 1}
    {hst : Commute s t} {a : G} (ha : a ∈ commutingPairSubgroup s t hs ht hst) : a ^ 2 = 1 := by
  rcases mem_commutingPairSubgroup.mp ha with rfl | rfl | rfl | rfl
  · simp
  · rw [pow_two, hs]
  · rw [pow_two, ht]
  · rw [hst.mul_pow, pow_two, pow_two, hs, ht, one_mul]

theorem commutingPairSubgroup_card {s t : G} {hs : s * s = 1} {ht : t * t = 1}
    {hst : Commute s t} (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hne : s ≠ t) :
    Nat.card (commutingPairSubgroup s t hs ht hst) = 2 ^ 2 := by
  have hst1 : s * t ≠ 1 := by
    intro h
    apply hne
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left ht]
  have hsst : s ≠ s * t := fun h => ht1 (by simpa using h)
  have htst : t ≠ s * t := fun h => hs1 (by simpa using h)
  have h1 : (1 : G) ∉ ({s, t, s * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hs1.symm, ht1.symm, hst1.symm⟩
  have h2 : s ∉ ({t, s * t} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hne, hsst⟩
  change Nat.card ↥({1, s, t, s * t} : Set G) = 2 ^ 2
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_pair htst]
  norm_num

theorem oddCore_le_of_commuting_class [Finite G] (hz : orderOf z = 2)
    (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (h2 : CentralProductCentralizer H z)
    {t : G} (ht : t ∈ involutionPointClass z) (hzt : Commute z t) (hne : t ≠ z) :
    CFSG.oddCore G ≤ H := by
  have htorder := class_orderOf hz ht
  have hzsq : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have htsq : t ^ 2 = 1 := htorder ▸ pow_orderOf_eq_one t
  have hzz : z * z = 1 := by rw [← pow_two]; exact hzsq
  have htt : t * t = 1 := by rw [← pow_two]; exact htsq
  let V := commutingPairSubgroup z t hzz htt hzt
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz; exact absurd hz (by decide)
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at htorder; exact absurd htorder (by decide)
  have hVcard : Nat.card V = 2 ^ 2 := commutingPairSubgroup_card hz1 ht1 hne.symm
  have hpower : ∀ member : V, member ^ 2 = 1 := fun member =>
    Subtype.ext (commutingPairSubgroup_sq member.property)
  have hodd : ¬ 2 ∣ Nat.card (CFSG.oddCore G) :=
    (CFSG.ComponentClassification.OddCore.odd_card G).not_two_dvd_nat
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two V (CFSG.oddCore G) hpower hVcard hodd
    (le_top.trans (Subgroup.normalizer_eq_top (H := CFSG.oddCore G)).ge)
  have hzH := mem_of_unique huniq
  have hC := h2.2 t ht hzt hne
  have htH : t ∈ H := hC (Subgroup.mem_centralizer_singleton_iff.mpr
    (hzt.symm.mul_right (Commute.refl t)).eq)
  rw [hgen]
  refine iSup_le fun v => iSup_le fun hv1 => ?_
  rcases mem_commutingPairSubgroup.mp v.property with hv | hv | hv | hv
  · exact absurd (Subtype.ext hv) hv1
  · rw [hv]; exact inf_le_right.trans (centralizer_le_of_unique huniq)
  · rw [hv]; exact inf_le_right.trans (centralizer_le_of_class_mem huniq ht htH)
  · rw [hv]; exact inf_le_right.trans hC

theorem eq_one_of_sq_eq_one_of_odd {N : Subgroup G} [Finite N] (hN : Odd (Nat.card N))
    {x : G} (hx : x ∈ N) (hsq : x ^ 2 = 1) : x = 1 := by
  have hdvd2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hdvdN : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hdvdN
    exact absurd (hN.of_dvd_nat hdvdN) (by decide)

theorem twoRank_hull_le_one_of_isolated {G : Type} [Group G] [Finite G] {z : G}
    (hz : orderOf z = 2) (hcentral : InvolutionPointCentralSylow z)
    (hiso : ∀ t ∈ involutionPointClass z, Commute z t → t = z) :
    twoRank (involutionPointHull z) ≤ 1 := by
  obtain ⟨S, hzS, hzc⟩ := hcentral
  have hzcomm := commute_of_mem_center hzS hzc
  have hzorder : orderOf (⟨z, hzS⟩ : (S : Subgroup G)) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz
  have hwc : ∀ g : G, g⁻¹ * ((⟨z, hzS⟩ : (S : Subgroup G)) : G) * g ∈ (S : Subgroup G) →
      g⁻¹ * ((⟨z, hzS⟩ : (S : Subgroup G)) : G) * g = (⟨z, hzS⟩ : (S : Subgroup G)) := by
    intro g hg
    exact hiso _ (class_conj_mem (distinguished_mem_pointClass z) g) (hzcomm _ hg)
  obtain ⟨-, hzcenter⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution S ⟨z, hzS⟩ hzc hzorder hwc
  let q := QuotientGroup.mk' (CFSG.oddCore G)
  have hclass : ∀ t ∈ involutionPointClass z, q t = q z := by
    rintro t ⟨g, rfl⟩
    change q (g⁻¹ * z * g) = q z
    rw [map_mul, map_mul, map_inv]
    have hc := Subgroup.mem_center_iff.mp hzcenter (q g)
    change q g * q z = q z * q g at hc
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hL : involutionPointHull z ≤ (Subgroup.zpowers (q z)).comap q := by
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    change q t ∈ Subgroup.zpowers (q z)
    rw [hclass t ht]
    exact Subgroup.mem_zpowers _
  apply twoRank_le_one_of_not_twoRankAtLeastTwo
  rintro ⟨E, hEcard, hEsq⟩
  let f : E → Subgroup.zpowers (q z) := fun e => ⟨q ((e : involutionPointHull z) : G),
    hL (e : involutionPointHull z).property⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Subtype.val hab
    change q _ = q _ at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
    have hsq : (((a : involutionPointHull z) : G))⁻¹ * ((b : involutionPointHull z) : G) =
        ((a⁻¹ * b : E) : G) := rfl
    have hsq2 : ((a⁻¹ * b : E) : G) ^ 2 = 1 := by
      have := congrArg (fun x : E => ((x : involutionPointHull z) : G)) (hEsq (a⁻¹ * b))
      simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
    have h1 := eq_one_of_sq_eq_one_of_odd (CFSG.ComponentClassification.OddCore.odd_card G)
      (hsq ▸ h) hsq2
    have h2 : a⁻¹ * b = 1 := Subtype.ext (Subtype.ext h1)
    exact (inv_mul_eq_one.mp h2)
  have hle := Nat.card_le_card_of_injective f hf
  rw [hEcard, Nat.card_zpowers] at hle
  have hqsq : q z ^ 2 = 1 := by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]
  have hord := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hqsq)
  omega

end CFSG.ComponentClassification.AschbacherStrongEmbedding
