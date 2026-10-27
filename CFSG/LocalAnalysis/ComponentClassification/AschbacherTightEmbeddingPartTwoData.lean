module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwoPGroup

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

@[expose] def OddNormalizerOverlaps {G : Type*} [Group G] (Q : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (Q : Set G) →
    Odd (Nat.card ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))

theorem oddNormalizerOverlaps_iff_trivial_sylows {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) :
    OddNormalizerOverlaps Q ↔ ∀ g : G, g ∉ Subgroup.normalizer (Q : Set G) →
      ∀ T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)),
        sylowImage _ T = ⊥ := by
  constructor
  · intro h g hg T
    exact two_subgroup_of_odd_eq_bot _ _ (sylowImage_isPGroup _ T) (h g hg) (sylowImage_le _ T)
  · intro h g hg
    by_contra hodd
    have heven : Even (Nat.card ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) :=
      Nat.not_odd_iff_even.mp hodd
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G))) 2
        (even_iff_two_dvd.mp heven)
    have htwo : IsPGroup 2 (Subgroup.zpowers v) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
    obtain ⟨T, hT⟩ := htwo.exists_le_sylow
    have hvImage : (v : G) ∈ sylowImage _ T :=
      Subgroup.mem_map.mpr ⟨v, hT (Subgroup.mem_zpowers v), rfl⟩
    rw [h g hg T] at hvImage
    have hvone : (v : G) = 1 := Subgroup.mem_bot.mp hvImage
    have hvone' : v = 1 := Subtype.ext hvone
    rw [hvone', orderOf_one] at hv
    norm_num at hv

theorem involution_conjugate_mem_normalizer_iff {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q)
    (hz : orderOf z = 2) (g : G) :
    g⁻¹ * z * g ∈ Subgroup.normalizer (Q : Set G) ↔
      g ∈ Subgroup.normalizer (Q : Set G) := by
  constructor
  · intro hzH
    by_contra hg
    let I : Subgroup G := rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)
    have hzI : g⁻¹ * z * g ∈ I :=
      ⟨Subgroup.mem_map.mpr ⟨z, hzQ, by simp only [MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]⟩, hzH⟩
    have hzOrder : orderOf (g⁻¹ * z * g) = 2 := by
      simpa only [MulAut.conj_apply, inv_inv] using ((MulAut.conj g⁻¹).orderOf_eq z).trans hz
    exact (hodd g hg).not_two_dvd_nat
      (hzOrder ▸ Subgroup.orderOf_dvd_natCard I hzI)
  · intro hg
    exact (Subgroup.normalizer (Q : Set G)).mul_mem
      ((Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).inv_mem hg)
        (Subgroup.le_normalizer hzQ)) hg

theorem involution_conjugate_mem_Q_iff {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q)
    (hz : orderOf z = 2) (g : G) :
    g⁻¹ * z * g ∈ Q ↔ g ∈ Subgroup.normalizer (Q : Set G) := by
  constructor
  · intro hmem
    exact (involution_conjugate_mem_normalizer_iff Q hodd z hzQ hz g).mp
      (Subgroup.le_normalizer hmem)
  · intro hg
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) z).mp hzQ

theorem involution_unique_containing_normalizer {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q)
    (hz : orderOf z = 2) (g : G) :
    z ∈ rightConjugate (Subgroup.normalizer (Q : Set G)) g ↔
      g ∈ Subgroup.normalizer (Q : Set G) := by
  rw [mem_rightConjugate_iff]
  simpa only [inv_inv, (Subgroup.normalizer (Q : Set G)).inv_mem_iff] using
    involution_conjugate_mem_normalizer_iff Q hodd z hzQ hz g⁻¹

theorem involution_centralizer_le_normalizer {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q)
    (hz : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  apply (involution_conjugate_mem_normalizer_iff Q hodd z hzQ hz g).mp
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hfixed : g⁻¹ * z * g = z := by
    rw [mul_assoc, ← hcomm, inv_mul_cancel_left]
  rw [hfixed]
  exact Subgroup.le_normalizer hzQ

theorem class_mem_normalizer_iff_mem_Q {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (z : G) (hzQ : z ∈ Q)
    (hz : orderOf z = 2) (t : G) (ht : t ∈ CFSG.ShultStronglyClosedTI.involutionPointClass z) :
    t ∈ Subgroup.normalizer (Q : Set G) ↔ t ∈ Q := by
  obtain ⟨g, rfl⟩ := ht
  exact (involution_conjugate_mem_normalizer_iff Q hodd z hzQ hz g).trans
    (involution_conjugate_mem_Q_iff Q hodd z hzQ hz g).symm

theorem class_product_unique_containment {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hodd : OddNormalizerOverlaps Q) (z t : G) (hzQ : z ∈ Q)
    (hz : orderOf z = 2) (ht : t ∈ CFSG.ShultStronglyClosedTI.involutionPointClass z)
    (hcommutes : Commute t z) (hne : t ≠ z) :
    t * z ∈ Q ∧ orderOf (t * z) = 2 ∧
      ∀ g : G, g⁻¹ * (t * z) * g ∈ Subgroup.normalizer (Q : Set G) ↔
        g ∈ Subgroup.normalizer (Q : Set G) := by
  have htorder := CFSG.ShultStronglyClosedTI.order_two_of_mem_pointClass hz ht
  have htH := involution_centralizer_le_normalizer Q hodd z hzQ hz
    (Subgroup.mem_centralizer_singleton_iff.mpr hcommutes)
  have htQ := (class_mem_normalizer_iff_mem_Q Q hodd z hzQ hz t ht).mp htH
  have hprod : t * z ∈ Q := Q.mul_mem htQ hzQ
  have htzne : t * z ≠ 1 := by
    intro htz
    exact hne ((mul_eq_one_iff_eq_inv.mp htz).trans (inv_eq_self_of_orderOf_eq_two hz))
  have hsquare : (t * z) ^ 2 = 1 := by
    rw [hcommutes.mul_pow]
    have ht2 : t ^ 2 = 1 := by simpa only [htorder] using pow_orderOf_eq_one t
    have hz2 : z ^ 2 = 1 := by simpa only [hz] using pow_orderOf_eq_one z
    rw [ht2, hz2, one_mul]
  have horder : orderOf (t * z) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr hsquare) with h | h
    · exact (htzne (orderOf_eq_one_iff.mp h)).elim
    · exact h
  exact ⟨hprod, horder, involution_conjugate_mem_normalizer_iff Q hodd (t * z) hprod horder⟩

theorem subgroup_sylow_ambient_of_normalizer_le {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (D : Sylow 2 H)
    (hnormalizer : Subgroup.normalizer (sylowImage H D : Set G) ≤ H) :
    ∃ P : Sylow 2 G, (P : Subgroup G) = sylowImage H D := by
  let X : Subgroup G := sylowImage H D
  obtain ⟨P, hXP⟩ := (sylowImage_isPGroup H D).exists_le_sylow
  let Y : Subgroup P := X.subgroupOf (P : Subgroup G)
  let N : Subgroup P := Subgroup.normalizer (Y : Set P)
  have himageX : Y.map (P : Subgroup G).subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hXP
  have himageN : N.map (P : Subgroup G).subtype ≤ H := by
    change (Subgroup.normalizer (Y : Set P)).map (P : Subgroup G).subtype ≤ H
    rw [← Subgroup.subgroupOf_normalizer_eq hXP, Subgroup.subgroupOf_map_subtype]
    exact inf_le_left.trans hnormalizer
  have htwoN : IsPGroup 2 (N.map (P : Subgroup G).subtype) :=
    (P.isPGroup'.to_subgroup N).map _
  have hXN : X ≤ N.map (P : Subgroup G).subtype := by
    rw [← himageX]
    exact Subgroup.map_mono Subgroup.le_normalizer
  have hDN : (D : Subgroup H) ≤ (N.map (P : Subgroup G).subtype).subgroupOf H := by
    intro d hd
    exact hXN (Subgroup.mem_map.mpr ⟨d, hd, rfl⟩)
  have hNlocal : (N.map (P : Subgroup G).subtype).subgroupOf H = (D : Subgroup H) :=
    D.is_maximal' htwoN.comap_subtype hDN
  have hNX : N.map (P : Subgroup G).subtype = X := by
    rw [← Subgroup.map_subgroupOf_eq_of_le himageN, hNlocal]
    rfl
  have hNY : N = Y := Subgroup.map_injective (P : Subgroup G).subtype_injective
    (hNX.trans himageX.symm)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hYtop : Y = ⊤ := by
    by_contra hproper
    have hlt := Group.normalizerCondition_of_isNilpotent Y (lt_top_iff_ne_top.mpr hproper)
    change Y < N at hlt
    rw [hNY] at hlt
    exact lt_irrefl _ hlt
  refine ⟨P, ?_⟩
  change (P : Subgroup G) = X
  rw [← himageX, hYtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_central_sylow_involution_in_Q {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q) :
    ∃ (P : Sylow 2 G) (z : G), z ∈ Q ∧ orderOf z = 2 ∧
      (P : Subgroup G) ≤ Subgroup.normalizer (Q : Set G) ∧
      z ∈ (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ∧
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  let H := Subgroup.normalizer (Q : Set G)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
    (even_iff_two_dvd.mp htight.1)
  have hwG : orderOf (w : G) = 2 := (Subgroup.orderOf_coe w).trans hw
  let cyclic : Subgroup G := Subgroup.zpowers (w : G)
  have htwo : IsPGroup 2 cyclic := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hwG, pow_one])
  have hcyclicQ : cyclic ≤ Q := Subgroup.zpowers_le.mpr w.property
  obtain ⟨D, hD⟩ := exists_sylowImage_containing H cyclic htwo (hcyclicQ.trans Subgroup.le_normalizer)
  let X : Subgroup G := sylowImage H D
  let A : Subgroup X := Q.subgroupOf X
  have hXH : X ≤ H := sylowImage_le H D
  let : A.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXH
  have hAne : A ≠ ⊥ := by
    intro hbot
    have hwX : (w : G) ∈ X := hD (Subgroup.mem_zpowers (w : G))
    have hwA : (⟨w.val, hwX⟩ : X) ∈ A := w.property
    rw [hbot] at hwA
    have hwOne : (w : G) = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hwA)
    rw [hwOne, orderOf_one] at hwG
    norm_num at hwG
  obtain ⟨z, hzA, hzcenter, hzorder⟩ :=
    CFSG.ProperTwoGeneratedCore.normal_two_subgroup_contains_central_involution
      (sylowImage_isPGroup H D) A hAne
  have hzQ : (z : G) ∈ Q := hzA
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hzorder
  have hNXH : Subgroup.normalizer (X : Set G) ≤ H := by
    intro g hg
    have hzconjX : g⁻¹ * z.val * g ∈ X := by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) z.val).mp z.property
    exact (involution_conjugate_mem_normalizer_iff Q hodd z.val hzQ hzG g).mp (hXH hzconjX)
  obtain ⟨P, hP⟩ := subgroup_sylow_ambient_of_normalizer_le H D hNXH
  refine ⟨P, z.val, hzQ, hzG, ?_, ?_, ?_⟩
  · rw [hP]
    exact hXH
  · rw [hP]
    exact Subgroup.mem_map.mpr ⟨z, hzcenter, rfl⟩
  · change Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ H
    rw [hP]
    exact hNXH

end CFSG.ComponentClassification.AschbacherTightEmbedding
