module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullRank
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureInvertedHullAlgebra
import CFSG.FeitThompson.OddOrderTheorem

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u

variable {G : Type u} [Group G] [Finite G]

theorem properHull_rank_one_zStar {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    (QuotientGroup.mk (⟨z, hzY⟩ : Y) : Y ⧸ CFSG.oddCore Y) ∈
        Subgroup.center (Y ⧸ CFSG.oddCore Y) ∧
      ∀ y : Y, ∃ c ∈ Subgroup.centralizer ({(⟨z, hzY⟩ : Y)} : Set Y),
        ∃ r ∈ CFSG.oddCore Y, y = c * r := by
  exact native_zStar_of_isolated_involution
    ((Subgroup.orderOf_coe (⟨z, hzY⟩ : Y)).symm.trans h.distinguished_order)
    (properHull_rank_one_isolated h hzY hrank)

theorem properHull_rank_one_ambient_factorization {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    (Y : Set G) = (Y ⊓ Subgroup.centralizer ({z} : Set G) : Set G) *
      (properOddCore Y : Set G) := by
  ext y
  constructor
  · intro hy
    obtain ⟨c, hc, r, hr, heq⟩ :=
      (properHull_rank_one_zStar h hzY hrank).2 (⟨y, hy⟩ : Y)
    exact Set.mem_mul.mpr ⟨c, ⟨c.property,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc))⟩,
      r, Subgroup.mem_map_of_mem Y.subtype hr, (congrArg Subtype.val heq).symm⟩
  · rintro ⟨c, hc, r, hr, rfl⟩
    exact Y.mul_mem hc.1 (properOddCore_le Y hr)

theorem properHull_rank_one_quotient_hull_le {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    involutionPointHull (⟨z, hzY⟩ : Y) ≤
      (Subgroup.zpowers (QuotientGroup.mk (⟨z, hzY⟩ : Y) : Y ⧸ CFSG.oddCore Y)).comap
        (QuotientGroup.mk' (CFSG.oddCore Y)) := by
  let zY : Y := ⟨z, hzY⟩
  let q : Y →* Y ⧸ CFSG.oddCore Y := QuotientGroup.mk' (CFSG.oddCore Y)
  have hcenter := (properHull_rank_one_zStar h hzY hrank).1
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨y, rfl⟩
  change q (y⁻¹ * zY * y) ∈ Subgroup.zpowers (q zY)
  have hcomm : q zY * q y = q y * q zY :=
    (Subgroup.mem_center_iff.mp hcenter (q y)).symm
  rw [map_mul, map_mul, map_inv, mul_assoc, hcomm, inv_mul_cancel_left]
  exact Subgroup.mem_zpowers _

theorem properHull_rank_one_solvable {H Y : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (hzY : z ∈ Y)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    Group.IsSolvable (properHull Y z) := by
  let L := involutionPointHull (⟨z, hzY⟩ : Y)
  let q : Y →* Y ⧸ CFSG.oddCore Y := QuotientGroup.mk' (CFSG.oddCore Y)
  let C := Subgroup.zpowers (q (⟨z, hzY⟩ : Y))
  let f : L →* C := (q.comp L.subtype).codRestrict C
    (fun x => properHull_rank_one_quotient_hull_le h hzY hrank x.property)
  have hker_le : f.ker ≤ (CFSG.oddCore Y).subgroupOf L := by
    intro x hx
    have hqx : q (x : Y) = 1 := congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff (x : Y)).mp hqx
  have hker_odd : Odd (Nat.card f.ker) := by
    have hodd := CFSG.ComponentClassification.OddCore.odd_card Y
    let j : f.ker →* CFSG.oddCore Y :=
      (L.subtype.comp f.ker.subtype).codRestrict (CFSG.oddCore Y)
        (fun x => hker_le x.property)
    have hj : Function.Injective j := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun a : CFSG.oddCore Y => (a : Y)) hab
    have hdiv : Nat.card f.ker ∣ Nat.card (CFSG.oddCore Y) :=
      Subgroup.card_dvd_of_injective j hj
    exact Odd.of_dvd_nat hodd hdiv
  let : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard f.ker hker_odd
  let : IsMulCommutative C := Subgroup.zpowers_isMulCommutative _
  let : Group.IsSolvable C := Group.isSolvable_of_comm (fun a b : C => mul_comm' a b)
  let : Group.IsSolvable L :=
    Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [Subgroup.subtype_range])
  exact Group.isSolvable_of_surjective
    (f := (properHullEquiv Y hzY).toMonoidHom) (properHullEquiv Y hzY).surjective

theorem properHull_rank_one_solvable_supplement {H Y : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) (hY : Y < ⊤)
    (hzY : z ∈ Y) (hescape : ¬ Y ≤ H)
    (hrank : twoRank (properHull Y z) ≤ 1) :
    ∃ W : Subgroup G, W ≤ H ⊓ properHull Y z ∧ Odd (Nat.card W) ∧
      (W.subgroupOf (H ⊓ properHull Y z)).Normal ∧
      (H ⊓ properHull Y z : Set G) = (W : Set G) *
        (H ⊓ properHull Y z ⊓ Subgroup.centralizer ({z} : Set G) : Set G) ∧
      ¬ Subgroup.normalizer (W : Set G) ⊓ properHull Y z ≤ H := by
  let : Group.IsSolvable (properHull Y z) :=
    properHull_rank_one_solvable h.local_datum hzY hrank
  exact invertedHull_ambient_solvable_supplement (properHull Y z) H
    (properHull_strong_embedding h hY hzY hescape) z (distinguished_mem_properHull Y z)
    h.local_datum.distinguished_mem h.local_datum.distinguished_order

end CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
