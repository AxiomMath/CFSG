module

public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingConsequences
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem normal_subgroup_normalizer_element_commutes
    (R D : Subgroup G) [R.Normal] (hdisjoint : Disjoint R D)
    (x : G) (hxR : x ∈ R) (hxN : x ∈ Subgroup.normalizer (D : Set G))
    (d : G) (hd : d ∈ D) : Commute x d := by
  have hcR : x * d * x⁻¹ * d⁻¹ ∈ R := by
    have hc := (inferInstance : R.Normal).conj_mem x⁻¹ (R.inv_mem hxR) d
    simpa only [mul_assoc] using R.mul_mem hxR hc
  have hcD : x * d * x⁻¹ * d⁻¹ ∈ D :=
    D.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN d).mp hd) (D.inv_mem hd)
  have hc : x * d * x⁻¹ = d :=
    mul_inv_eq_one.mp (Subgroup.disjoint_def.mp hdisjoint hcR hcD)
  change x * d = d * x
  calc
    x * d = (x * d * x⁻¹) * x := by group
    _ = d * x := congrArg (fun y => y * x) hc

theorem root_center_complement_normalizer_centralizes_point
    (H R : Subgroup G) (hRH : R ≤ H) (hRN : (R.subgroupOf H).Normal)
    (D : Subgroup H) (hcompl : (R.subgroupOf H).IsComplement' D)
    (x : G) (hxZ : x ∈ (Subgroup.center R).map R.subtype)
    (hxN : x ∈ Subgroup.normalizer (D.map H.subtype : Set G))
    (h : G) (hh : h ∈ H) : Commute x h := by
  obtain ⟨xR, hxRZ, hxRval⟩ := Subgroup.mem_map.mp hxZ
  change (xR : G) = x at hxRval
  have hxR : x ∈ R := hxRval ▸ xR.property
  let xH : H := ⟨x, hRH hxR⟩
  let hH : H := ⟨h, hh⟩
  let RH := R.subgroupOf H
  let : RH.Normal := hRN
  have hxHN : xH ∈ Subgroup.normalizer (D : Set H) := by
    have hn := Subgroup.le_normalizer_comap H.subtype
      (show xH ∈ (Subgroup.normalizer (D.map H.subtype : Set G)).comap H.subtype
        from hxN)
    rwa [Subgroup.comap_map_eq_self_of_injective H.subtype_injective] at hn
  obtain ⟨⟨r, d⟩, hrd⟩ := hcompl.2 hH
  have hxHr : Commute xH (r : H) := by
    apply Subtype.ext
    change x * (r : G) = (r : G) * x
    have hrR : (r : G) ∈ R := r.property
    have hc := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxRZ) ⟨r, hrR⟩).symm
    change (xR : G) * (r : G) = (r : G) * (xR : G) at hc
    rwa [hxRval] at hc
  have hxHd : Commute xH (d : H) :=
    normal_subgroup_normalizer_element_commutes RH D hcompl.disjoint
      xH hxR hxHN d d.property
  have hxHh : Commute xH hH := hrd ▸ hxHr.mul_right hxHd
  exact congrArg Subtype.val hxHh.eq

variable [Finite G]

theorem strongly_embedded_central_involution_unique
    (H : Subgroup G) (hH : IsStronglyEmbedded H)
    (x : G) (hxH : x ∈ H) (hx : orderOf x = 2)
    (hcentral : ∀ h ∈ H, Commute x h)
    (a : G) (haH : a ∈ H) (ha : orderOf a = 2) : a = x := by
  have hxI : IsInvolution x :=
    ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩
  have haI : IsInvolution a :=
    ⟨(orderOf_eq_prime_iff.mp ha).2, (orderOf_eq_prime_iff.mp ha).1⟩
  have hnative : CFSG.BenderSuzuki.IsStronglyEmbedded H :=
    CFSG.ShultStronglyClosedTI.native_strong_embedding_of_order_conditions
      (show CFSG.Open.fusionStronglyEmbedded H from hH)
  obtain ⟨g, hgH, hga⟩ := hnative.involutions_conjugate_in hxH hxI haH haI
  have hfix : rightConjugateElem x g = x := by
    change g⁻¹ * x * g = x
    rw [mul_assoc, (hcentral g hgH).eq]
    group
  exact hga.symm.trans hfix

theorem strongly_embedded_root_center_disjoint_complement_normalizer
    (H : Subgroup G) (hH : IsStronglyEmbedded H)
    (R : Subgroup G) (hR : IsPGroup 2 R) (hRH : R ≤ H)
    (hRN : (R.subgroupOf H).Normal)
    (D : Subgroup H) (hcompl : (R.subgroupOf H).IsComplement' D)
    (a b : G) (haH : a ∈ H) (hbH : b ∈ H)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) :
    Disjoint ((Subgroup.center R).map R.subtype)
      (Subgroup.normalizer (D.map H.subtype : Set G)) := by
  let Z := (Subgroup.center R).map R.subtype
  let I := Z ⊓ Subgroup.normalizer (D.map H.subtype : Set G)
  have hZ : IsPGroup 2 Z := (hR.to_subgroup (Subgroup.center R)).map R.subtype
  have hI : IsPGroup 2 I :=
    hZ.of_injective (I.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  apply Subgroup.disjoint_def.mpr
  intro y hyZ hyN
  by_contra hyone
  have hIne : I ≠ ⊥ := by
    intro hbot
    exact hyone (Subgroup.mem_bot.mp (hbot ▸ (show y ∈ I from ⟨hyZ, hyN⟩)))
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).mpr hIne
  obtain ⟨n, hn, hcard⟩ := hI.nontrivial_iff_card.mp inferInstance
  have hdiv : 2 ∣ Nat.card I := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 hdiv
  have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxH : (x : G) ∈ H := hRH ((Subgroup.map_subtype_le _) x.property.1)
  have hcentral : ∀ h ∈ H, Commute (x : G) h :=
    root_center_complement_normalizer_centralizes_point H R hRH hRN D hcompl
      x x.property.1 x.property.2
  have hax := strongly_embedded_central_involution_unique H hH x hxH hxG hcentral a haH ha
  have hbx := strongly_embedded_central_involution_unique H hH x hxH hxG hcentral b hbH hb
  exact hab (hax.trans hbx.symm)

end CFSG.ComponentClassification.AschbacherTightEmbedding
