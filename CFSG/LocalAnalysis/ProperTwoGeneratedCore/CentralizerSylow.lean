module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionFusion
public import CFSG.CharacterTheory.TwoRankLowerBound.RankOne
public import CFSG.LocalAnalysis.ComponentClassification.TwoRankSylow

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.Open CFSG.TwoRankLowerBound.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

universe u

variable {G : Type u} [Group G] [Finite G]

theorem sylow_two_rank_eq (S : Sylow 2 G) :
    pRank 2 (S : Subgroup G) = twoRank G := by
  rw [pRank_subgroup_eq_internal_top 2 (by decide)]
  exact CFSG.ComponentClassification.TwoRankSylow.invariant S

theorem sylow_image_two_rank_eq (D : Subgroup G) (T : Sylow 2 D) :
    pRank 2 ((T : Subgroup D).map D.subtype) = pRank 2 D := by
  have hequiv := (T : Subgroup D).equivMapOfInjective D.subtype D.subtype_injective
  calc
    _ = twoRank ((T : Subgroup D).map D.subtype) :=
      pRank_subgroup_eq_internal_top 2 (by decide) _
    _ = twoRank (T : Subgroup D) :=
      (pRank_top_eq_of_equiv 2 (by decide) hequiv).symm
    _ = twoRank D := CFSG.ComponentClassification.TwoRankSylow.invariant T
    _ = pRank 2 D := (pRank_subgroup_eq_internal_top 2 (by decide) D).symm

theorem sylow_involution_centralizer_rank
    (S : Sylow 2 G) (hrank : 2 ≤ pRank 2 (S : Subgroup G))
    (t : G) (htS : t ∈ (S : Subgroup G)) (ht : orderOf t = 2) :
    2 ≤ pRank 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial (S : Subgroup G) :=
    ⟨⟨⟨t, htS⟩, 1, fun h => (orderOf_eq_prime_iff.mp ht).2 (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz, hzcenter⟩ :=
    exists_central_involution_of_two_group (S : Subgroup G) S.isPGroup'
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have htz : Commute t (z : G) := by
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨t, htS⟩)
  by_cases heq : t = (z : G)
  · have hcent : (S : Subgroup G) ≤ Subgroup.centralizer ({t} : Set G) := by
      intro x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      rw [heq]
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨x, hx⟩)
    simpa only [inf_eq_left.mpr hcent] using hrank
  · let C := (S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G)
    have htC : t ∈ C := ⟨htS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have hzC : (z : G) ∈ C :=
      ⟨z.property, Subgroup.mem_centralizer_singleton_iff.mpr htz.eq.symm⟩
    have hC := two_le_twoRank_of_commuting_involutions C ⟨t, htC⟩ ⟨z, hzC⟩
      ((Subgroup.orderOf_coe _).symm.trans ht)
      ((Subgroup.orderOf_coe _).symm.trans hzG)
      (fun h => heq (congrArg Subtype.val h)) (Subtype.ext htz.eq)
    rwa [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)] at hC

theorem overgroup_involution_centralizer_rank
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hrank : 2 ≤ twoRank G) (t : G) (htH : t ∈ H) (ht : orderOf t = 2) :
    2 ≤ pRank 2 (H ⊓ Subgroup.centralizer ({t} : Set G)) := by
  obtain ⟨a, haH, hatS⟩ := involution_conjugate_into_sylow S H hSH t htH ht
  have hat : orderOf (a⁻¹ * t * a) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv, ht] using (MulAut.conj a⁻¹).orderOf_eq t
  have hsource := sylow_involution_centralizer_rank S
    (by rwa [sylow_two_rank_eq]) _ hatS hat
  have hmap :
      (((S : Subgroup G) ⊓ Subgroup.centralizer ({a⁻¹ * t * a} : Set G)).map
        (MulAut.conj a).toMonoidHom) ≤ H ⊓ Subgroup.centralizer ({t} : Set G) := by
    rintro x ⟨y, ⟨hyS, hyC⟩, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem haH (hSH hyS)) (H.inv_mem haH), ?_⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg (fun x : G => a * x * a⁻¹)
      (Subgroup.mem_centralizer_singleton_iff.mp hyC)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel_right,
      mul_inv_cancel, one_mul, mul_one] using h
  have hbound := pRank_mono 2 (by decide) hmap
  rw [pRank_map_automorphism 2 (by decide)] at hbound
  exact hsource.trans hbound

theorem full_core_involution_centralizer_sylow
    (S : Sylow 2 G) (H : Subgroup G) (hSH : (S : Subgroup G) ≤ H)
    (hrank : 2 ≤ twoRank G)
    (hcore : properTwoGenCoreGamma (S : Subgroup G) 2 ≤ H)
    (t : G) (htH : t ∈ H) (ht : orderOf t = 2) :
    let C := Subgroup.centralizer ({t} : Set G)
    let D := H ⊓ C
    2 ≤ pRank 2 D ∧ ∀ T : Sylow 2 D, ∃ U : Sylow 2 C,
      (U : Subgroup C).map C.subtype = (T : Subgroup D).map D.subtype := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C := Subgroup.centralizer ({t} : Set G)
  let D := H ⊓ C
  have hDrank : 2 ≤ pRank 2 D :=
    overgroup_involution_centralizer_rank S H hSH hrank t htH ht
  refine ⟨hDrank, ?_⟩
  intro T
  let R := (T : Subgroup D).map D.subtype
  have hRtwo : IsPGroup 2 R := T.isPGroup'.map D.subtype
  have hRD : R ≤ D := Subgroup.map_subtype_le _
  have hRC : R ≤ C := hRD.trans inf_le_right
  have hRrank : 2 ≤ pRank 2 R := by
    change 2 ≤ pRank 2 ((T : Subgroup D).map D.subtype)
    rwa [sylow_image_two_rank_eq]
  obtain ⟨U, hRU⟩ := (hRtwo.comap_subtype (K := C)).exists_le_sylow
  let P := (U : Subgroup C).map C.subtype
  have hRP : R ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRC]
    exact Subgroup.map_mono hRU
  have hPH : P ≤ H := pGroup_le_of_large_intersection S H 2 hSH hcore P
    (U.isPGroup'.map C.subtype)
    (hRrank.trans (pRank_mono 2 (by decide) (le_inf hRP (hRD.trans inf_le_left))))
  have hPD : P ≤ D := le_inf hPH (Subgroup.map_subtype_le _)
  have hTP : (T : Subgroup D) ≤ P.subgroupOf D := by
    intro x hx
    exact hRP (Subgroup.mem_map_of_mem D.subtype hx)
  have heq := T.is_maximal' ((U.isPGroup'.map C.subtype).comap_subtype) hTP
  have himage := congrArg (Subgroup.map D.subtype) heq
  change (P.subgroupOf D).map D.subtype = R at himage
  rw [Subgroup.map_subgroupOf_eq_of_le hPD] at himage
  exact ⟨U, himage⟩

end CFSG.ProperTwoGeneratedCore
