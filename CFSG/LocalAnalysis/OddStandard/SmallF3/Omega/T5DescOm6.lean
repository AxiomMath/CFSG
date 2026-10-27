module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5DescGrp
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.ClassicalInvolution.Balance.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem mem_centralizer_of_mem_centerIn {t : G} (ht : t ∈ centerIn L) :
    t ∈ centralizer (L : Set G) := by
  obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp ht
  have haeq' : (a : G) = t := haeq
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hcomm : (⟨l, hl⟩ : ↥L) * a = a * (⟨l, hl⟩ : ↥L) :=
    Subgroup.mem_center_iff.mp ha _
  have hval : l * (a : G) = (a : G) * l := by
    simpa using congrArg Subtype.val hcomm
  rw [haeq'] at hval
  exact hval

private theorem eq_one_or_eq_of_mem_center_card_two {A : Type*} [Group A]
    (hcard : Nat.card (Subgroup.center A) = 2) {x y : A}
    (hx : x ∈ Subgroup.center A) (hy : y ∈ Subgroup.center A) (hy1 : y ≠ 1) :
    x = 1 ∨ x = y := by
  obtain ⟨u, _, hu_uniq⟩ :=
    (Nat.card_eq_two_iff' (α := Subgroup.center A) 1).mp hcard
  by_cases hx1 : x = 1
  · exact Or.inl hx1
  · right
    have hxu : (⟨x, hx⟩ : Subgroup.center A) = u :=
      hu_uniq ⟨x, hx⟩ (fun h => hx1 (Subtype.ext_iff.mp h))
    have hyu : (⟨y, hy⟩ : Subgroup.center A) = u :=
      hu_uniq ⟨y, hy⟩ (fun h => hy1 (Subtype.ext_iff.mp h))
    exact Subtype.ext_iff.mp (hxu.trans hyu.symm)

private theorem mem_sup_centralizer_iff {K : Type*} [Group K] (H : Subgroup K) {s : K} :
    s ∈ H ⊔ Subgroup.centralizer (H : Set K) ↔
      ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set K), h * c = s := by
  have hcoe : (↑(Subgroup.centralizer (H : Set K) ⊔ H) : Set K) =
      (Subgroup.centralizer (H : Set K) : Set K) * (H : Set K) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.centralizer (H : Set K)) H
      (Subgroup.centralizer_le_normalizer (H : Set K))
  have hcoe' : (↑(H ⊔ Subgroup.centralizer (H : Set K)) : Set K) =
      (Subgroup.centralizer (H : Set K) : Set K) * (H : Set K) := by
    rw [sup_comm]; exact hcoe
  have hmem : s ∈ (↑(H ⊔ Subgroup.centralizer (H : Set K)) : Set K) ↔
      ∃ h ∈ H, ∃ c ∈ Subgroup.centralizer (H : Set K), h * c = s := by
    rw [hcoe', Set.mem_mul]
    constructor
    · rintro ⟨c, hc, h, hh, hch⟩
      exact ⟨h, hh, c, hc, (Subgroup.mem_centralizer_iff.mp hc h hh).trans hch⟩
    · rintro ⟨h, hh, c, hc, hhc⟩
      exact ⟨c, hc, h, hh, (Subgroup.mem_centralizer_iff.mp hc h hh).symm.trans hhc⟩
  exact hmem

theorem t5_isOm6M_descL (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2) :
    IsOm6M (DescL L t) := by
  let A := ↥L
  let A' := ↥(DescL L t)
  let f : A →* A' := descRes L t
  let O : Subgroup A := CFSG.oddCore A
  let O' : Subgroup A' := CFSG.oddCore A'
  have hf : Function.Surjective f := descRes_surjective L t
  have hker : f.ker ≤ Subgroup.center A := descRes_ker_le_center hL ht ht2
  have hA'q : CFSG.IsQuasisimple A' :=
    CFSG.LocalCores.isQuasisimple_of_surjective hL.1 f hf hker
  refine ⟨hA'q, ?_⟩
  have hO'le : O' ≤ Subgroup.center A' :=
    CFSG.ClassicalInvolution.Balance.oddCore_le_center_of_isQuasisimple
      (⟨hA'q.1.commutator_eq_top, hA'q.2.1⟩ : CFSG.Open.IsQuasisimple A')
  obtain ⟨tL, htL_center, htL_coe⟩ := Subgroup.mem_map.mp ht
  have htL_ord : orderOf tL = 2 := by
    have h := orderOf_injective L.subtype L.subtype_injective tL
    rw [htL_coe, ht2] at h
    exact h.symm
  have hOddO : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card A
  have htL_not_mem : tL ∉ O := by
    intro hmem
    have h2 : 2 ∣ Nat.card O := by
      have hord : orderOf (⟨tL, hmem⟩ : O) = 2 := by
        rw [← orderOf_injective O.subtype O.subtype_injective ⟨tL, hmem⟩]
        exact htL_ord
      rw [← hord]
      exact orderOf_dvd_natCard _
    obtain ⟨k, hk⟩ := hOddO
    obtain ⟨m, hm⟩ := h2
    omega
  have hftL : f tL = 1 :=
    (descRes_eq_one_iff hL ht ht2 tL).mpr (Or.inr htL_coe)
  have hmkO_tL_ne : QuotientGroup.mk' O tL ≠ 1 := fun h =>
    htL_not_mem ((QuotientGroup.eq_one_iff tL).mp h)
  have hmkO_tL_center : QuotientGroup.mk' O tL ∈ Subgroup.center (A ⧸ O) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective O)
      (Subgroup.mem_map_of_mem (QuotientGroup.mk' O) htL_center)
  have hmaple : O.map f ≤ O' := by
    haveI : O.Normal := CFSG.oddCore_normal A
    have hnormal : (O.map f).Normal := (inferInstance : O.Normal).map f hf
    have hodd : Odd (Nat.card (O.map f)) :=
      hOddO.of_dvd_nat (Subgroup.card_map_dvd (H := O) f)
    exact CFSG.ComponentClassification.OddCore.maximal A' (O.map f) hnormal hodd
  let ρ₁ : A →* (A ⧸ O) ⧸ Subgroup.center (A ⧸ O) :=
    (QuotientGroup.mk' (Subgroup.center (A ⧸ O))).comp (QuotientGroup.mk' O)
  let ρ₂ : A →* A' ⧸ O' := (QuotientGroup.mk' O').comp f
  have hρ₁ : Function.Surjective ρ₁ :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hρ₂ : Function.Surjective ρ₂ := (QuotientGroup.mk'_surjective _).comp hf
  have hker_eq : ρ₁.ker = ρ₂.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro ha
      have hca : QuotientGroup.mk' O a ∈ Subgroup.center (A ⧸ O) := by
        have ha' : (QuotientGroup.mk' O a : (A ⧸ O) ⧸ Subgroup.center (A ⧸ O)) = 1 := ha
        exact (QuotientGroup.eq_one_iff (QuotientGroup.mk' O a)).mp ha'
      have hcases : QuotientGroup.mk' O a = 1 ∨
          QuotientGroup.mk' O a = QuotientGroup.mk' O tL :=
        eq_one_or_eq_of_mem_center_card_two hL.2.1 hca hmkO_tL_center hmkO_tL_ne
      have hfa : f a ∈ O' := by
        rcases hcases with h1 | h2
        · have haO : a ∈ O := (QuotientGroup.eq_one_iff a).mp h1
          exact hmaple (Subgroup.mem_map_of_mem f haO)
        · have htLaO : tL⁻¹ * a ∈ O := by
            apply (QuotientGroup.eq_one_iff (tL⁻¹ * a)).mp
            change QuotientGroup.mk' O (tL⁻¹ * a) = 1
            rw [map_mul, map_inv, h2, inv_mul_cancel]
          have hfa' : f (tL⁻¹ * a) ∈ O' := hmaple (Subgroup.mem_map_of_mem f htLaO)
          rwa [map_mul, map_inv, hftL, inv_one, one_mul] at hfa'
      exact (QuotientGroup.eq_one_iff (f a)).mpr hfa
    · intro ha
      have hfa : f a ∈ O' := (QuotientGroup.eq_one_iff (f a)).mp ha
      have hca : a ∈ Subgroup.center A := descRes_center hL ht ht2 a (hO'le hfa)
      exact (QuotientGroup.eq_one_iff (QuotientGroup.mk' O a)).mpr
        (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective O)
          (Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hca))
  have e : (A ⧸ O) ⧸ Subgroup.center (A ⧸ O) ≃* A' ⧸ O' :=
    (QuotientGroup.quotientKerEquivOfSurjective ρ₁ hρ₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker_eq).trans
        (QuotientGroup.quotientKerEquivOfSurjective ρ₂ hρ₂))
  exact LieModel.of_mulEquiv e hL.2.2

theorem t5_desc_orderOf (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L) (ht2 : orderOf t = 2)
    {s : G} (hs : s ∈ normalizer (L : Set G)) (hs2 : orderOf s = 2)
    (hnc : s ∉ centralizer (L : Set G)) : orderOf (descElt L t s hs) = 2 := by
  have hsN_ord : orderOf (⟨s, hs⟩ : ↥(normalizer (L : Set G))) = 2 := by
    have h := orderOf_injective (Subgroup.subtype (normalizer (L : Set G)))
      (Subgroup.subtype_injective _) ⟨s, hs⟩
    have h2 : orderOf ((⟨s, hs⟩ : ↥(normalizer (L : Set G))) : G) = 2 := by
      simpa using hs2
    exact h.symm.trans h2
  have hdvd : orderOf (descElt L t s hs) ∣ 2 := by
    have h2 : descElt L t s hs ^ 2 = 1 := by
      rw [descElt, ← map_pow, show (⟨s, hs⟩ : ↥(normalizer (L : Set G))) ^ 2 = 1 from by
        rw [← hsN_ord]
        exact pow_orderOf_eq_one _]
      exact map_one _
    exact orderOf_dvd_of_pow_eq_one h2
  have hne : descElt L t s hs ≠ 1 := by
    intro h
    have h' := (descMk_eq_one_iff hL ht ht2 ⟨s, hs⟩).mp (by simpa only [descElt] using h)
    have h'' : s = 1 ∨ s = t := by simpa using h'
    rcases h'' with h1 | ht'
    · exact hnc (by rw [h1]; exact Subgroup.one_mem _)
    · exact hnc (by rw [ht']; exact mem_centralizer_of_mem_centerIn ht)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · rw [orderOf_eq_one_iff] at h1
    exact absurd h1 hne
  · exact h2

theorem t5_desc_mem_normalizer (L : Subgroup G) (t : G) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    descElt L t s hs ∈ normalizer (DescL L t : Set (DescG L t)) := by
  apply Subgroup.le_normalizer_map (descMk L t)
  refine Subgroup.mem_map_of_mem (descMk L t) ?_
  rw [Subgroup.mem_normalizer_iff]
  intro n
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  show (n : G) ∈ L ↔ s * (n : G) * s⁻¹ ∈ L
  exact Subgroup.mem_normalizer_iff.mp hs (n : G)

theorem t5_desc_mem_centralizer_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    descElt L t s hs ∈ centralizer (DescL L t : Set (DescG L t)) ↔
      s ∈ centralizer (L : Set G) := by
  constructor
  · intro hcent
    apply t5_centralizes_of_central_comm hL.1 (Z := zpowers t)
      (Subgroup.zpowers_le.mpr ht) hs
    intro l hl
    let lN : ↥(normalizer (L : Set G)) := ⟨l, Subgroup.le_normalizer (H := L) hl⟩
    have hcent' : descMk L t (⟨s, hs⟩ : ↥(normalizer (L : Set G))) ∈
        centralizer (DescL L t : Set (DescG L t)) := by
      simpa only [descElt] using hcent
    have hg : descMk L t (⟨s, hs⟩ * lN * ⟨s, hs⟩⁻¹ * lN⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      have hlN : descMk L t lN ∈ DescL L t :=
        Subgroup.mem_map_of_mem (descMk L t) (Subgroup.mem_subgroupOf.mpr hl)
      have hc := Subgroup.mem_centralizer_iff.mp hcent' (descMk L t lN) hlN
      rw [← hc]
      group
    have hmem :=
      (descMk_eq_one_iff hL ht ht2 (⟨s, hs⟩ * lN * ⟨s, hs⟩⁻¹ * lN⁻¹)).mp hg
    have hcoe : ((⟨s, hs⟩ * lN * ⟨s, hs⟩⁻¹ * lN⁻¹ :
        ↥(normalizer (L : Set G))) : G) = s * l * s⁻¹ * l⁻¹ := rfl
    rw [hcoe] at hmem
    rcases hmem with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers t
  · intro hcent
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨lN, hlN, hd_eq⟩ :=
      Subgroup.mem_map.mp (show d ∈ (L.subgroupOf (normalizer (L : Set G))).map
        (descMk L t) from hd)
    have hl : (lN : G) ∈ L := Subgroup.mem_subgroupOf.mp hlN
    have hcomm : (lN : G) * s = s * (lN : G) :=
      Subgroup.mem_centralizer_iff.mp hcent (lN : G) hl
    have hN : lN * (⟨s, hs⟩ : ↥(normalizer (L : Set G))) =
        (⟨s, hs⟩ : ↥(normalizer (L : Set G))) * lN := by
      apply Subtype.ext
      simpa using hcomm
    rw [← hd_eq]
    show descMk L t lN * descMk L t (⟨s, hs⟩ : ↥(normalizer (L : Set G))) =
      descMk L t (⟨s, hs⟩ : ↥(normalizer (L : Set G))) * descMk L t lN
    rw [← map_mul, ← map_mul, hN]

theorem t5_desc_innerOn_iff (hL : IsOm6Z2 L) {t : G} (ht : t ∈ centerIn L)
    (ht2 : orderOf t = 2) {s : G} (hs : s ∈ normalizer (L : Set G)) :
    InnerOn (DescL L t) (descElt L t s hs) ↔ InnerOn L s := by
  have htcent : t ∈ centralizer (L : Set G) := mem_centralizer_of_mem_centerIn ht
  constructor
  · intro hinner
    obtain ⟨d, hd, e', he', hde⟩ := (mem_sup_centralizer_iff (DescL L t)).mp hinner
    obtain ⟨lN, hlN, hd_eq⟩ :=
      Subgroup.mem_map.mp (show d ∈ (L.subgroupOf (normalizer (L : Set G))).map
        (descMk L t) from hd)
    have hl : (lN : G) ∈ L := Subgroup.mem_subgroupOf.mp hlN
    obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (DescZ L t) e'
    have hn' : descMk L t n = e' := hn
    have he'cent : descElt L t (n : G) n.2 ∈ centralizer (DescL L t : Set (DescG L t)) := by
      have heq : descElt L t (n : G) n.2 = e' := by
        rw [descElt, show (⟨(n : G), n.2⟩ : ↥(normalizer (L : Set G))) = n from rfl, hn']
      rw [heq]
      exact he'
    have hncent : (n : G) ∈ centralizer (L : Set G) :=
      (t5_desc_mem_centralizer_iff hL ht ht2 n.2).mp he'cent
    have hde' : descMk L t lN * descMk L t n =
        descMk L t (⟨s, hs⟩ : ↥(normalizer (L : Set G))) := by
      rw [← hd_eq, ← hn'] at hde
      simpa only [descElt] using hde
    have h1 : descMk L t ((lN * n)⁻¹ * ⟨s, hs⟩) = 1 := by
      rw [map_mul, map_inv, map_mul, ← hde', inv_mul_cancel]
    have hmem := (descMk_eq_one_iff hL ht ht2 ((lN * n)⁻¹ * ⟨s, hs⟩)).mp h1
    have hcoe : (((lN * n)⁻¹ * ⟨s, hs⟩ : ↥(normalizer (L : Set G))) : G) =
        ((lN : G) * (n : G))⁻¹ * s := rfl
    rw [hcoe] at hmem
    rcases hmem with h | h
    · refine (mem_sup_centralizer_iff L).mpr ⟨(lN : G), hl, (n : G), hncent, ?_⟩
      have h' := congrArg (fun x => ((lN : G) * (n : G)) * x) h
      simpa [mul_assoc] using h'.symm
    · refine (mem_sup_centralizer_iff L).mpr
        ⟨(lN : G), hl, (n : G) * t, mul_mem hncent htcent, ?_⟩
      have h' := congrArg (fun x => ((lN : G) * (n : G)) * x) h
      simpa [mul_assoc] using h'.symm
  · intro hinner
    obtain ⟨l, hl, c, hc, hlc⟩ := (mem_sup_centralizer_iff L).mp hinner
    have hcN : c ∈ normalizer (L : Set G) :=
      Subgroup.centralizer_le_normalizer (L : Set G) hc
    have hcE : descElt L t c hcN ∈ centralizer (DescL L t : Set (DescG L t)) :=
      (t5_desc_mem_centralizer_iff hL ht ht2 hcN).mpr hc
    have hlN : (⟨l, Subgroup.le_normalizer (H := L) hl⟩ :
        ↥(normalizer (L : Set G))) ∈ L.subgroupOf (normalizer (L : Set G)) :=
      Subgroup.mem_subgroupOf.mpr hl
    have hd : descMk L t ⟨l, Subgroup.le_normalizer (H := L) hl⟩ ∈ DescL L t :=
      Subgroup.mem_map_of_mem (descMk L t) hlN
    have hs_eq : descElt L t s hs =
        descMk L t ⟨l, Subgroup.le_normalizer (H := L) hl⟩ * descElt L t c hcN := by
      have hN : (⟨s, hs⟩ : ↥(normalizer (L : Set G))) =
          ⟨l, Subgroup.le_normalizer (H := L) hl⟩ * ⟨c, hcN⟩ := by
        apply Subtype.ext
        simpa using hlc.symm
      rw [descElt, descElt, hN, map_mul]
    exact (mem_sup_centralizer_iff (DescL L t)).mpr ⟨_, hd, _, hcE, hs_eq.symm⟩

end CFSG.OddStandard.SmallF3.Omega
