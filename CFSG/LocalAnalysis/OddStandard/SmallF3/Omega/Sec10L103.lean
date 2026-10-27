module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private lemma mem_centerIn_iff {K : Subgroup G} (a : G) :
    a ∈ centerIn K ↔ a ∈ K ∧ ∀ k ∈ K, a * k = k * a := by
  rw [centerIn, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, fun k hk => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨k, hk⟩)).symm⟩
  · rintro ⟨haK, hcent⟩
    exact ⟨⟨a, haK⟩, Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (hcent (y : G) y.2).symm, rfl⟩

private lemma zpowers_le_normalizer_centralizer {L : Subgroup G} {z : G} (hzL : z ∈ L) :
    zpowers z ≤ normalizer (centralizer (L : Set G)) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro c
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc l hl
    have hzl : z⁻¹ * l * z ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hzL) hl) hzL
    calc l * (z * c * z⁻¹)
        = z * ((z⁻¹ * l * z) * c) * z⁻¹ := by group
      _ = z * (c * (z⁻¹ * l * z)) * z⁻¹ := by rw [hc (z⁻¹ * l * z) hzl]
      _ = (z * c * z⁻¹) * l := by group
  · intro hc l hl
    have hzl : z * l * z⁻¹ ∈ L := L.mul_mem (L.mul_mem hzL hl) (L.inv_mem hzL)
    calc l * c
        = z⁻¹ * (z * l * z⁻¹) * (z * c * z⁻¹) * z := by group
      _ = z⁻¹ * ((z * l * z⁻¹) * (z * c * z⁻¹)) * z := by group
      _ = z⁻¹ * ((z * c * z⁻¹) * (z * l * z⁻¹)) * z := by rw [hc (z * l * z⁻¹) hzl]
      _ = c * l := by group

theorem asc82Lemma103_of (h102 : Asc82Lemma102) (hb : Asc82Basic10)
    (hS5 : Asc82FactSylow5) : Asc82Lemma103 := by
  intro G _ _ t L S z h
  obtain ⟨hpsp, htC, _htL, htS, hSN, hsyl⟩ := hb G t L S z h
  obtain ⟨hZ2, hcent⟩ := hS5 G L hpsp (S ⊓ L) hsyl
  have hzL : z ∈ L := by
    obtain ⟨K, hK⟩ := h.pocket.2
    exact (le_trans hK.2.1 inf_le_left) hK.1
  have hz2 : z ^ 2 = 1 := by
    have hzpow := pow_orderOf_eq_one z
    rw [h.pocket.1] at hzpow
    exact hzpow
  have ht2 : t ^ 2 = 1 := by
    have htpow := pow_orderOf_eq_one t
    rw [h.involution] at htpow
    exact htpow
  have hz_centerS : z ∈ centerIn S := (mem_centerIn_iff z).mpr
    ⟨h.mem_S, fun s hs => (h.central s hs).symm⟩
  have ht_centerS : t ∈ centerIn S := (mem_centerIn_iff t).mpr
    ⟨htS, fun s hs => (Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hs)).symm⟩
  have hsup_le : zpowers z ⊔ zpowers t ≤ omega1 (centerIn S) :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨hz_centerS, hz2⟩))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure ⟨ht_centerS, ht2⟩))
  have hzP : z ∈ centerIn (S ⊓ L) := (mem_centerIn_iff z).mpr
    ⟨⟨h.mem_S, hzL⟩, fun s hs => (h.central s hs.1).symm⟩
  have hzcard : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, h.pocket.1]
  have hZeq : zpowers z = centerIn (S ⊓ L) :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzP) (by rw [hZ2, hzcard])
  rw [omega1]
  refine le_antisymm ?_ hsup_le
  refine (Subgroup.closure_le (zpowers z ⊔ zpowers t)).mpr ?_
  rintro x ⟨hxcenterS, hx2⟩
  obtain ⟨hxS, hxcommS⟩ := (mem_centerIn_iff x).mp hxcenterS
  have hxN : x ∈ normalizer (L : Set G) := hSN hxS
  have hxsup : x ∈ centralizer (L : Set G) ⊔ centerIn (S ⊓ L) :=
    hcent x hxN (fun p hp => hxcommS p hp.1)
  rw [← hZeq] at hxsup
  rw [sup_comm (centralizer (L : Set G)) (zpowers z)] at hxsup
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right (zpowers z)
    (centralizer (L : Set G)) (zpowers_le_normalizer_centralizer hzL)] at hxsup
  obtain ⟨w, hwZ, c, hcC, hcw⟩ := Set.mem_mul.mp hxsup
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hwZ
  have hcomm_xz : Commute x z := hxcommS z h.mem_S
  have hcomm_xw : Commute x w := by rw [← hi]; exact hcomm_xz.zpow_right i
  have hc_centerS : c ∈ centerIn S := by
    have hc_eq : c = w⁻¹ * x := by rw [← hcw]; group
    rw [hc_eq]
    exact (centerIn S).mul_mem
      ((centerIn S).inv_mem (Subgroup.zpowers_le.mpr hz_centerS hwZ)) hxcenterS
  have hc2 : c * c = 1 := by
    have hc_eq : c = w⁻¹ * x := by rw [← hcw]; group
    have hw2 : w ^ 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp
        (dvd_trans (orderOf_dvd_of_mem_zpowers hwZ) (by rw [h.pocket.1]))
    have hwinv2 : (w⁻¹) ^ 2 = 1 := by rw [inv_pow, hw2, inv_one]
    rw [hc_eq, ← pow_two, (hcomm_xw.symm.inv_left).mul_pow 2, hwinv2, hx2, one_mul]
  have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P := by
    intro P hP
    obtain ⟨Q, hQ⟩ := hP.exists_sylow
    haveI : IsCyclic ↥(Q : Subgroup ↥(centralizer (L : Set G))) :=
      h102 G t L h.toSec10Setting Q
    rw [← hQ]
    exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥(centralizer (L : Set G)))
        (centralizer (L : Set G)).subtype
        (centralizer (L : Set G)).subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥(centralizer (L : Set G)))
        (centralizer (L : Set G)).subtype
        (centralizer (L : Set G)).subtype_injective).surjective
  have hct : c * t = t * c := ((mem_centerIn_iff c).mp hc_centerS).2 t htS
  rcases eq_one_or_eq_of_commute hcyc hcC htC hc2 h.involution hct with hc1 | hct'
  · rw [← hcw, hc1, mul_one]
    exact Subgroup.mem_sup_left hwZ
  · rw [← hcw, hct']
    exact Subgroup.mul_mem_sup hwZ (Subgroup.mem_zpowers t)

end CFSG.OddStandard.SmallF3.Omega
