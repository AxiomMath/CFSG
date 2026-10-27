module

public import CFSG.LargeExtraspecial.S9PA

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9.RB

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem exists_spRho_one_mem_LmodN_pgl25 (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hP : PGL25Case H C ht ht1 hVQ) :
    ∃ e : Vt S g t, ∃ he : beta H C ht ht1 hVQ (aV ht) e = 0,
      spRho (beta_isAlt H C ht ht1 hVQ) he 1 ∈ LmodN S g t := by
  classical
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  obtain ⟨d, hd, hdA, hdE⟩ := hP.exists_typeA
  obtain ⟨h, hh, hb⟩ := exists_pair H C ht ht1 hVQ
  have hab := beta_aV_bV H C ht ht1 hVQ hh hb
  obtain ⟨x, hax, hdx⟩ : ∃ x, beta H C ht ht1 hVQ (aV ht) x = 0 ∧
      beta H C ht ht1 hVQ d x = 1 := by
    set b := bV (mem_Lbar_of_pair H ht hh)
    set β := beta H C ht ht1 hVQ
    have hd' : d + β d b • aV ht ≠ 0 := by
      intro h0
      apply hdA
      rw [eq_neg_of_add_eq_zero_left h0]
      exact neg_mem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
    obtain ⟨w, hw⟩ : ∃ w, β (d + β d b • aV ht) w ≠ 0 := by
      by_contra! hcon
      exact hd' (hnd.1 _ hcon)
    have hw1 : β (d + β d b • aV ht) w = 1 := zmod2_eq_one_of_ne_zero hw
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hw1
    refine ⟨w + β (aV ht) w • b, ?_, ?_⟩
    · simp only [map_add, map_smul, smul_eq_mul, hab, mul_one, zmod2_add_self]
    · simp only [map_add, map_smul, smul_eq_mul]
      rw [mul_comm]
      exact hw1
  have hle := LmodN_le_spPointRadical H C ht ht1 hVQ
  have hU := card_spPointRadical hβ hnd (aV_ne_zero H ht)
  rw [hP.finrank_eq] at hU
  have hE := card_LmodN_pgl25 H C ht ht1 hVQ hP
  have hidx : ((LmodN S g t).subgroupOf
      (spPointRadical (beta H C ht ht1 hVQ) (aV ht))).index = 2 := by
    have h1 := ((LmodN S g t).subgroupOf
      (spPointRadical (beta H C ht ht1 hVQ) (aV ht))).card_mul_index
    have h2 : Nat.card ((LmodN S g t).subgroupOf
        (spPointRadical (beta H C ht ht1 hVQ) (aV ht))) = Nat.card (LmodN S g t) := by
      rw [← card_map_of_injective
        (spPointRadical (beta H C ht ht1 hVQ) (aV ht)).subtype_injective,
        subgroupOf_map_subtype, inf_eq_left.mpr hle]
    have h8 : Nat.card (spPointRadical (beta H C ht ht1 hVQ) (aV ht)) = 8 :=
      hU.trans (by norm_num)
    rw [h2, hE, h8] at h1
    omega
  by_cases hxE : spRho hβ hax 0 ∈ LmodN S g t
  · have hdx' : beta H C ht ht1 hVQ (aV ht) (d + x) = 0 := by
      rw [map_add, hd, hax, add_zero]
    refine ⟨d + x, hdx', ?_⟩
    have hmul := mul_mem hdE hxE
    rw [spRho_mul hβ hd hax 0 0 hdx', hdx, zero_add, zero_add] at hmul
    exact hmul
  · refine ⟨x, hax, ?_⟩
    have hmul := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := ⟨spRho hβ hax 0, spRho_mem_spPointRadical hβ hax 0⟩)
      (b := ⟨_, spTransvection_mem_U hβ (aV ht)⟩)).mpr
      (iff_of_false (fun h' => hxE h') (fun h' => hP.tau_not_mem h'))
    rw [spRho_one_eq]
    exact hmul

end CFSG.LargeExtraspecial.S9.RB

