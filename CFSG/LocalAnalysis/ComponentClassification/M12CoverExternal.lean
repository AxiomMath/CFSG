module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalFixed
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverData

public section

namespace CFSG.ComponentClassification.M12Cover

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

theorem ctss_m12_central_double_cover_external_data_from_fusion_and_section :
    StandardRecognition.ExternalInvolutionData .M12 := by
  intro H _ _ L t hset
  obtain ⟨hLn, hLq, ht, hZ, ⟨e⟩, hCL, hidx⟩ := hset
  have htL : t ∈ L := by
    have h : t ∈ (center L).map L.subtype := by
      rw [hZ]
      exact mem_zpowers t
    obtain ⟨z, -, rfl⟩ := h
    exact z.2
  let t' : L := ⟨t, htL⟩
  have hZ' : center L = zpowers t' := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hZ, MonoidHom.map_zpowers]
    rfl
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht
  have hCL' : centralizer (L : Set H) = zpowers (t' : H) := hCL
  let e' : L ⧸ center L ≃* NativeSporadic.M12 := e
  obtain ⟨hv, -, hconjH⟩ :=
    ctss_m12_central_double_cover_external_involution_conjugacy_frontier hLq ht' hZ' ⟨e'⟩ hCL'
  refine ⟨fun x y hxL hx hyL hy => ?_, fun p hpL hp => ?_⟩
  · obtain ⟨h, hh⟩ := hconjH x y hxL hx hyL hy
    exact ⟨h⁻¹, by rw [inv_inv]; exact hh⟩
  have hidx2 : L.index = 2 := by
    have h1 : L.index ≠ 1 := fun h => hpL ((Subgroup.index_eq_one.1 h).symm ▸ mem_top p)
    have h0 : L.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨v, -, hvp, -⟩ := hv p hpL hp
  have hconj : IsConj p ((t' : H) * p) := isConj_iff.2 ⟨v, hvp⟩
  let π : L →* NativeSporadic.M12 := e'.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hπ : Function.Surjective π := e'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerZ : π.ker = center L := by
    ext l
    simp only [π, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hker : π.ker = zpowers t' := hkerZ.trans hZ'
  have hα := CentralCover.fullAction_apply π hπ hkerZ p
  obtain ⟨-, -, -, -, -, -, hperf, hcard60, hout, -⟩ :=
    ctss_m12_central_double_cover_conjugate_lifts_have_exact_fixed_quotient hLq ht' hZ' π hπ hker
      hCL' hidx2 hpL hp hconj _ hα
  obtain ⟨-, -, hsup, hinf, htZ, ⟨eA, -, -⟩, -, -, -⟩ :=
    ctss_m12_central_double_cover_external_fixed_section_frontier hLq ht' hZ' π hπ hker hCL'
      hidx2 hpL hp hconj _ hα
  have htH : (t' : H) ∈ center H := CentralCover.coe_mem_center_of_center_eq_zpowers hZ'
    (by rw [← ht', pow_orderOf_eq_one])
  have hmapt : (zpowers t').map L.subtype = zpowers t := by
    rw [MonoidHom.map_zpowers]
    rfl
  let A : Subgroup H :=
    (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L).map L.subtype
  let fA : (⁅fixSub (CentralCover.fullAction π hπ hkerZ p),
      fixSub (CentralCover.fullAction π hπ hkerZ p)⁆ : Subgroup NativeSporadic.M12) ≃* A :=
    eA.symm.trans (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)
  have hcardA : Nat.card A = 60 := by rw [← Nat.card_congr fA.toEquiv, hcard60]
  refine ⟨A, map_subtype_le _, ?_, ?_, fun a _ => mem_center_iff.mp htH a, ?_, ?_, ?_⟩
  · rw [← hmapt, ← Subgroup.map_sup, hsup, Subgroup.subgroupOf_map_subtype, inf_comm]
  · rw [← hmapt, ← Subgroup.map_inf_eq _ _ L.subtype L.subtype_injective, hinf, Subgroup.map_bot]
  · have : Group.IsPerfect (⁅fixSub (CentralCover.fullAction π hπ hkerZ p),
        fixSub (CentralCover.fullAction π hπ hkerZ p)⁆ : Subgroup NativeSporadic.M12) :=
      Subgroup.isPerfect_iff.2 hperf
    exact Group.isPerfect_def.1 (Group.IsPerfect.ofSurjective (f := fA.toMonoidHom) fA.surjective)
  · rw [hcardA]
    exact ⟨30, rfl⟩
  · rw [← Nat.card_congr (equivalence fA).toEquiv]
    exact fun h3 => absurd (dvd_trans h3 hout) (by norm_num)

end CFSG.ComponentClassification.M12Cover
