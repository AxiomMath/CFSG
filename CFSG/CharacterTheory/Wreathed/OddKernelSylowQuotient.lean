module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.NormalSylowIntersection
public import Mathlib.Order.CompletePartialOrder

public noncomputable section
open scoped Classical Pointwise
namespace CFSG.Wreathed.OddKernelSylowQuotient
universe u
variable {B : Type u} [Group B]

def quotientRestriction (U T : Subgroup B) [U.Normal] : T →* B ⧸ U :=
  (QuotientGroup.mk' U).comp T.subtype

theorem quotientRestriction_ker (U T : Subgroup B) [U.Normal] :
    (quotientRestriction U T).ker = U.subgroupOf T := by
  ext t
  change QuotientGroup.mk' U (t : B) = 1 ↔ (t : B) ∈ U
  exact QuotientGroup.eq_one_iff _

theorem quotientRestriction_range (U T : Subgroup B) [U.Normal] :
    (quotientRestriction U T).range = T.map (QuotientGroup.mk' U) := by
  rw [quotientRestriction, MonoidHom.range_comp, Subgroup.range_subtype]

def quotientImageEquiv (U T : Subgroup B) [U.Normal] :
    T ⧸ U.subgroupOf T ≃* T.map (QuotientGroup.mk' U) :=
  (QuotientGroup.quotientMulEquivOfEq (quotientRestriction_ker U T).symm).trans
    ((QuotientGroup.quotientKerEquivRange (quotientRestriction U T)).trans
      (MulEquiv.subgroupCongr (quotientRestriction_range U T)))

theorem quotientImageEquiv_mk (U T : Subgroup B) [U.Normal] (t : T) :
    (quotientImageEquiv U T (QuotientGroup.mk t) : B ⧸ U) =
      QuotientGroup.mk' U (t : B) := by
  rfl

theorem quotientRestriction_injective_iff {U T : Subgroup B} [U.Normal] :
    Function.Injective (quotientRestriction U T) ↔ U ⊓ T = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, quotientRestriction_ker]
  constructor
  · intro h
    have hmap := congrArg (Subgroup.map T.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.map_bot] at hmap
  · intro h
    apply le_bot_iff.mp
    intro t ht
    have ht1 : (t : B) = 1 := Subgroup.mem_bot.mp (h ▸ ⟨ht, t.property⟩)
    exact Subtype.ext ht1

variable [Finite B]

def quotientSylow (U : Subgroup B) [U.Normal] (S : Sylow 2 B) :
    Sylow 2 (B ⧸ U) :=
  S.mapSurjective (QuotientGroup.mk'_surjective U)

theorem quotientSylow_coe (U : Subgroup B) [U.Normal] (S : Sylow 2 B) :
    (quotientSylow U S : Subgroup (B ⧸ U)) =
      (S : Subgroup B).map (QuotientGroup.mk' U) := by
  rfl

theorem normal_subgroup_Sylow_intersection (U : Subgroup B) [U.Normal] (S : Sylow 2 B) :
    ∃ P : Sylow 2 U, (P : Subgroup U).map U.subtype = U ⊓ (S : Subgroup B) := by
  obtain ⟨P, hP⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection
    2 U S
  refine ⟨P, ?_⟩
  rw [hP, Subgroup.subgroupOf_map_subtype, inf_comm]

omit [Finite B] in
theorem oddKernelIntersection_normal (O U : Subgroup B) [O.Normal] [U.Normal] :
    (U ⊓ O).Normal := inferInstance

omit [Finite B] in
theorem oddKernelIntersection_subgroupOf_normal (O U : Subgroup B)
    [O.Normal] : ((U ⊓ O).subgroupOf U).Normal := by
  have h : (U ⊓ O).subgroupOf U = O.subgroupOf U := by
    ext t
    exact and_iff_right t.property
  rw [h]
  infer_instance

omit [Finite B] in
theorem oddKernelIntersection_subgroupOf (O U : Subgroup B) :
    (U ⊓ O).subgroupOf U = O.subgroupOf U := by
  ext t
  exact and_iff_right t.property

omit [Finite B] in
theorem quotientImage_isTwoGroup (O A U : Subgroup B) [O.Normal]
    (hA : IsPGroup 2 A) (hU : U ≤ O ⊔ A) :
    IsPGroup 2 (U.map (QuotientGroup.mk' O)) := by
  have hOmap : O.map (QuotientGroup.mk' O) = ⊥ := by
    simpa only [QuotientGroup.ker_mk'] using
      (Subgroup.map_ker_self (QuotientGroup.mk' O))
  have hle : U.map (QuotientGroup.mk' O) ≤ A.map (QuotientGroup.mk' O) := by
    have h := Subgroup.map_mono (f := QuotientGroup.mk' O) hU
    rwa [Subgroup.map_sup, hOmap, bot_sup_eq] at h
  exact (hA.map (QuotientGroup.mk' O)).to_le hle

omit [Finite B] in
theorem oddKernelQuotient_isTwoGroup (O A U : Subgroup B) [O.Normal]
    (hA : IsPGroup 2 A) (hU : U ≤ O ⊔ A) :
    IsPGroup 2 (U ⧸ O.subgroupOf U) := by
  exact (quotientImage_isTwoGroup O A U hA hU).of_equiv
    (quotientImageEquiv O U).symm

omit [Finite B] in
theorem oddKernelIntersection_odd (O U : Subgroup B) (hO : Odd (Nat.card O)) :
    Odd (Nat.card (U ⊓ O : Subgroup B)) :=
  hO.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)

theorem Sylow_image_top_of_twoQuotient (D : Subgroup B) [D.Normal]
    (hQ : IsPGroup 2 (B ⧸ D)) (S : Sylow 2 B) :
    (S : Subgroup B).map (QuotientGroup.mk' D) = ⊤ := by
  have h := (quotientSylow D S).is_maximal' (hQ.to_subgroup ⊤) le_top
  exact (quotientSylow_coe D S).symm.trans h.symm

theorem normalKernel_sup_Sylow_of_twoQuotient (D : Subgroup B) [D.Normal]
    (hQ : IsPGroup 2 (B ⧸ D)) (S : Sylow 2 B) : D ⊔ (S : Subgroup B) = ⊤ := by
  have hmap : (S : Subgroup B).map (QuotientGroup.mk' D) =
      (⊤ : Subgroup B).map (QuotientGroup.mk' D) := by
    rw [Sylow_image_top_of_twoQuotient D hQ S, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective D)]
  have hsup := Subgroup.map_eq_map_iff.mp hmap
  rwa [QuotientGroup.ker_mk', top_sup_eq, sup_comm] at hsup

theorem oddKernel_sup_SylowIntersection (O A U : Subgroup B) [O.Normal] [U.Normal]
    (hA : IsPGroup 2 A) (hU : U ≤ O ⊔ A) (S : Sylow 2 B) :
    U = (U ⊓ O) ⊔ (U ⊓ (S : Subgroup B)) := by
  obtain ⟨P, hP⟩ := normal_subgroup_Sylow_intersection U S
  have h := normalKernel_sup_Sylow_of_twoQuotient (O.subgroupOf U)
    (oddKernelQuotient_isTwoGroup O A U hA hU) P
  have hm := congrArg (Subgroup.map U.subtype) h
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_comm O U, hP,
    Subgroup.map_top, Subgroup.range_subtype] at hm
  exact hm.symm

theorem oddKernel_mul_SylowIntersection (O A U : Subgroup B) [O.Normal] [U.Normal]
    (hA : IsPGroup 2 A) (hU : U ≤ O ⊔ A) (S : Sylow 2 B) :
    (U : Set B) = (U ⊓ O : Subgroup B) * (U ⊓ (S : Subgroup B) : Subgroup B) := by
  have h := congrArg (fun H : Subgroup B => (H : Set B))
    (oddKernel_sup_SylowIntersection O A U hA hU S)
  exact h.trans (Subgroup.normal_mul (U ⊓ O) (U ⊓ (S : Subgroup B)))

def normalIntersectionSylow (U : Subgroup B) [U.Normal] (S : Sylow 2 B) :
    Sylow 2 U :=
  (CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 U S).choose

theorem normalIntersectionSylow_coe (U : Subgroup B) [U.Normal] (S : Sylow 2 B) :
    (normalIntersectionSylow U S : Subgroup U) = (S : Subgroup B).subgroupOf U :=
  (CFSG.DisconnectedInvolutionGraph.Helpers.normal_subgroup_sylow_intersection 2 U S).choose_spec

theorem odd_kernel_Sylow_factorization (O A U : Subgroup B) [O.Normal] [U.Normal]
    (hO : Odd (Nat.card O)) (hA : IsPGroup 2 A) (hU : U ≤ O ⊔ A) (S : Sylow 2 B) :
    (U ⊓ O).Normal ∧ Odd (Nat.card (U ⊓ O : Subgroup B)) ∧
    ((U ⊓ O).subgroupOf U).Normal ∧ IsPGroup 2 (U ⧸ O.subgroupOf U) ∧
    U = (U ⊓ O) ⊔ (U ⊓ (S : Subgroup B)) ∧
    (U : Set B) = (U ⊓ O : Subgroup B) * (U ⊓ (S : Subgroup B) : Subgroup B) ∧
    ∃ P : Sylow 2 U, (P : Subgroup U) = (S : Subgroup B).subgroupOf U ∧
      (P : Subgroup U).map U.subtype = U ⊓ (S : Subgroup B) := by
  refine ⟨oddKernelIntersection_normal O U, oddKernelIntersection_odd O U hO,
    oddKernelIntersection_subgroupOf_normal O U, oddKernelQuotient_isTwoGroup O A U hA hU,
    oddKernel_sup_SylowIntersection O A U hA hU S,
    oddKernel_mul_SylowIntersection O A U hA hU S, normalIntersectionSylow U S,
    normalIntersectionSylow_coe U S, ?_⟩
  rw [normalIntersectionSylow_coe, Subgroup.subgroupOf_map_subtype, inf_comm]

end CFSG.Wreathed.OddKernelSylowQuotient
