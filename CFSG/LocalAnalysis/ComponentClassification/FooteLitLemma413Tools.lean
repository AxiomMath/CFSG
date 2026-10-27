module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingTheorem
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitEndPair
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma411

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G]

theorem FooteInCC.conj {M : Subgroup G} {t n : G} (ht : FooteInCC M t)
    (hn : n ∈ normalizer (M : Set G)) : FooteInCC M (n * t * n⁻¹) := by
  obtain ⟨ht2, htC, hCt⟩ := ht
  refine ⟨?_, ?_, fun hle => hCt fun x hx => ?_⟩
  · have h1 := (MulAut.conj n).orderOf_eq t
    rwa [MulAut.conj_apply, ht2] at h1
  · exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M hn) t).mp htC
  · have h1 : n * x * n⁻¹ ∈ centralizer ({n * t * n⁻¹} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      calc n * x * n⁻¹ * (n * t * n⁻¹) = n * (x * t) * n⁻¹ := by group
        _ = n * (t * x) * n⁻¹ := by rw [hx]
        _ = n * t * n⁻¹ * (n * x * n⁻¹) := by group
    have h2 := hle h1
    rw [show x = n⁻¹ * (n * x * n⁻¹) * n by group]
    exact mul_mem (mul_mem (inv_mem hn) h2) hn

theorem mem_or_mul_mem_of_mem_sup_zpowers {K : Subgroup G} {s x : G}
    (hKs : K ≤ centralizer ({s} : Set G)) (hs : s * s = 1) (hx : x ∈ K ⊔ zpowers s) :
    x ∈ K ∨ x * s ∈ K := by
  have hsN : s ∈ normalizer (K : Set G) :=
    mem_normalizer_of_forall_commute fun u hu => mem_centralizer_singleton_iff.mp (hKs hu)
  have hle : zpowers s ≤ normalizer (K : Set G) := zpowers_le.mpr hsN
  have hx' : x ∈ (K : Set G) * (zpowers s : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left K (zpowers s) hle]
    exact hx
  obtain ⟨k, hk, y, hy, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
  have hs2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two, hs]
  rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← two_mul, zpow_mul, hs2, one_zpow, mul_one]
    exact hk
  · right
    rw [zpow_add, zpow_mul, hs2, one_zpow, one_mul, zpow_one, mul_assoc, hs, mul_one]
    exact hk

theorem exists_pow_mul_conj_eq {d e : G} (hd : d * d = 1) (he : e * e = 1)
    (hodd : Odd (orderOf (d * e))) : ∃ k : ℕ, (d * e) ^ k * d * ((d * e) ^ k)⁻¹ = e := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hpow : (d * e) ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one _
  have hc : d * (d * e) * d⁻¹ = (d * e)⁻¹ := by
    rw [mul_inv_rev, hdi, hei, ← mul_assoc, hd, one_mul]
  have hck : d * ((d * e) ^ k)⁻¹ * d⁻¹ = (d * e) ^ k := by
    have h1 : (d * (d * e) * d⁻¹) ^ k = ((d * e)⁻¹) ^ k := by rw [hc]
    rw [conj_pow, inv_pow] at h1
    rw [show d * ((d * e) ^ k)⁻¹ * d⁻¹ = (d * (d * e) ^ k * d⁻¹)⁻¹ by group, h1, inv_inv]
  calc (d * e) ^ k * d * ((d * e) ^ k)⁻¹
      = (d * e) ^ k * (d * ((d * e) ^ k)⁻¹ * d⁻¹) * d := by group
    _ = (d * e) ^ k * (d * e) ^ k * d := by rw [hck]
    _ = (d * e) ^ (2 * k + 1) * (d * e)⁻¹ * d := by
        rw [pow_succ, mul_inv_cancel_right, two_mul, pow_add]
    _ = e := by rw [hpow, one_mul, mul_inv_rev, hdi, hei, mul_assoc, hd, mul_one]

theorem mem_zpowers_of_eq_mul_of_odd {s o k : G} (hs : s * s = 1) (hsok : s = o * k)
    (hok : o * k = k * o) (hodd : Odd (orderOf o)) : s ∈ zpowers k := by
  obtain ⟨m, hm⟩ := hodd
  have hc : Commute o k := hok
  have h1 : s ^ (2 * m + 1) = s := by
    rw [pow_succ, pow_mul, sq, hs, one_pow, one_mul]
  have h2 : s ^ (2 * m + 1) = k ^ (2 * m + 1) := by
    rw [hsok, hc.mul_pow, ← hm, pow_orderOf_eq_one, one_mul]
  rw [← h1, h2]
  exact pow_mem (mem_zpowers k) _

variable [Finite G]

theorem not_forall_commute_of_card_eight (hs : IsSimpleGroup G) {E : Subgroup G}
    (hE8 : Nat.card E = 8) {t : G} (ht : orderOf t = 2) : ¬ ∀ g : G, g * t = t * g := by
  intro hcen
  have := hs
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; omega
  have hn : (zpowers t).Normal :=
    normal_of_le_center (zpowers_le.mpr (mem_center_iff.mpr hcen))
  rcases hn.eq_bot_or_eq_top with h | h
  · have h1 := mem_zpowers t
    rw [h, mem_bot] at h1
    exact ht1 h1
  · have h1 : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
    rw [h, card_top] at h1
    have h2 := E.card_le_card_group
    omega

theorem exists_conj_commute_ne_of_card_eight (hs : IsSimpleGroup G) {E : Subgroup G}
    (hE8 : Nat.card E = 8) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g * t * g⁻¹ * t = t * (g * t * g⁻¹) ∧ g * t * g⁻¹ ≠ t := by
  have := hs
  have : Fintype G := Fintype.ofFinite G
  by_contra hall
  push Not at hall
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht; omega
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨O, hOn, hOodd, hO⟩ := ZStar.glauberman_zStar G t ht1 htt hall
  rcases hOn.eq_bot_or_eq_top with hbot | htop
  · apply not_forall_commute_of_card_eight hs hE8 ht
    intro g
    have h1 := hO g
    rw [hbot, mem_bot, mul_inv_eq_one] at h1
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [h1]
  · have h1 : orderOf t ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O (htop ▸ mem_top t)
    rw [ht] at h1
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h1)

omit [Finite G] in
theorem centralizer_le_of_stronglyEmbedded {H : Subgroup G} (hH : Open.fusionStronglyEmbedded H)
    {t : G} (htH : t ∈ H) (ht : orderOf t = 2) : centralizer ({t} : Set G) ≤ H := by
  intro x hx
  by_contra hxH
  have hodd := hH.2.2 x hxH
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp hx
  have hmem : t ∈ H ⊓ H.map (MulAut.conj x⁻¹).toMonoidHom := by
    refine mem_inf.mpr ⟨htH, t, htH, ?_⟩
    change x⁻¹ * t * x⁻¹⁻¹ = t
    rw [inv_inv, mul_assoc, ← hxt, inv_mul_cancel_left]
  have h1 := Subgroup.orderOf_dvd_natCard _ hmem
  rw [ht] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

open CFSG.ComponentClassification.AschbacherStrongEmbedding CFSG.ShultStronglyClosedTI in
theorem fusionStronglyEmbedded_of_productUniqueContainment
    (hs : IsSimpleGroup G) {E : Subgroup G} (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8)
    {H : Subgroup G} {z : G} (hz : orderOf z = 2) (hH : H ≠ ⊤)
    (huniq : ∀ g : G, z ∈ AschbacherTightEmbedding.rightConjugate H g ↔ g ∈ H)
    (hP : ProductUniqueContainment H z) : Open.fusionStronglyEmbedded H := by
  have := hs
  obtain ⟨h12, h23, -⟩ := theorem_3_3 not_minimalInvolutionPointLocalFailure
    benderDoubleCoverRigidity H z hz hH huniq
  have h3 := h23 (h12 hP)
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz; omega
  have hhull : involutionPointHull z = ⊤ := by
    rcases (minimalLocalFailure_hull_normal z).eq_bot_or_eq_top with h | h
    · exfalso
      apply hz1
      have h1 : z ∈ involutionPointHull z :=
        subset_closure ⟨1, by simp [BenderSuzuki.PFAppendixIII.rightConjugateElem]⟩
      rw [h, mem_bot] at h1
      exact h1
    · exact h
  have hcomm : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply not_forall_commute_of_card_eight hs hE8 hz
      intro g
      have h1 : g * z * g⁻¹ * z⁻¹ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        commutator_mem_commutator (mem_top g) (mem_top z)
      rw [h, mem_bot, mul_inv_eq_one] at h1
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h1]
    · exact h
  rcases h3 with hr | ⟨u, -, -, -, -, hse, -⟩
  · exfalso
    set K := involutionPointHull z with hK
    have hEK : E ≤ K := hhull ▸ le_top
    have hel : Open.IsElemAbelian 2 (E.subgroupOf K) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
      · exact commute_of_sq_eq_one hE2 a.2 b.2
      · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE2 _ ha
    have hcard : Nat.card (E.subgroupOf K) = 2 ^ 3 := by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hEK).symm.toEquiv, hE8]
      norm_num
    have h4 := SectionRank.le_pRank one_lt_two (le_top : E.subgroupOf K ≤ ⊤) hel hcard
    have h5 : Open.twoRank ↥K ≤ 1 := hr
    unfold Open.twoRank at h5
    omega
  · rw [hhull, hcomm] at hse
    have hmap := hse.map_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    have himage : (H.subgroupOf (⊤ : Subgroup G)).map
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom = H := by
      change (H.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = H
      rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
    rwa [himage] at hmap

end CFSG.ComponentClassification.FooteLit
