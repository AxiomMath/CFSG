module

public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyGHCent

public section

open Subgroup

namespace CFSG.EvenSporadicStandard.TwoHS.GH312

variable {X : Type} [Group X]

theorem false_of_oneClass [Finite X] {T : Subgroup X} (hT : T.Normal)
    (hone : ∀ a b : ↥T, orderOf a = 2 → orderOf b = 2 → IsConj a b) {u : X} (huT : u ∈ T)
    (hu : orderOf u = 2) (P : Sylow 2 X) (hP : Nat.card ↥(P : Subgroup X) = 2 ^ 7)
    (hC : ¬ 2 ^ 7 ∣ Nat.card ↥(centralizer ({u} : Set X))) : False := by
  haveI := hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2T : 2 ∣ Nat.card ↥T := by
    have h : orderOf (⟨u, huT⟩ : ↥T) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hu
    rw [← h]
    exact orderOf_dvd_natCard _
  obtain ⟨n, ⟨hnT, hnP⟩, hn1⟩ := CFSG.EvenSporadicStandard.TwoHS.SAFyGH.exists_ne_one_mem_inf_sylow
    h2T P
  haveI : Group.IsNilpotent ↥(P : Subgroup X) := P.isPGroup'.isNilpotent
  have hQn : (T.subgroupOf (P : Subgroup X)).Normal := hT.subgroupOf _
  have hQne : T.subgroupOf (P : Subgroup X) ≠ ⊥ := by
    intro h
    have hmem : (⟨n, hnP⟩ : ↥(P : Subgroup X)) ∈ T.subgroupOf (P : Subgroup X) := hnT
    rw [h, Subgroup.mem_bot] at hmem
    exact hn1 (congrArg Subtype.val hmem)
  obtain ⟨⟨z, hzQ⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hQne)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') z
  have hk1 : 1 ≤ k := by
    by_contra hk0
    obtain rfl : k = 0 := by omega
    exact hz1' (orderOf_eq_one_iff.mp (by rw [hk]; rfl))
  set w : ↥(P : Subgroup X) := z ^ 2 ^ (k - 1) with hw
  have hwQ : w ∈ T.subgroupOf (P : Subgroup X) ⊓ Subgroup.center ↥(P : Subgroup X) :=
    Subgroup.pow_mem _ hzQ _
  have hw2 : orderOf w = 2 := by
    have hdvd : 2 ^ (k - 1) ∣ orderOf z := by
      rw [hk]
      exact pow_dvd_pow 2 (by omega)
    rw [hw, orderOf_pow_of_dvd (by positivity) hdvd, hk,
      show 2 ^ k = 2 ^ (k - 1) * 2 by rw [← pow_succ]; congr 1; omega]
    exact Nat.mul_div_cancel_left _ (by positivity)
  have hwT : (w : X) ∈ T := hwQ.1
  have hwc : ∀ p ∈ (P : Subgroup X), (w : X) * p = p * (w : X) := by
    intro p hp
    have := Subgroup.mem_center_iff.1 hwQ.2 ⟨p, hp⟩
    exact (congrArg Subtype.val this).symm
  have hwo : orderOf (⟨(w : X), hwT⟩ : ↥T) = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (w : X) = 2
    rw [Subgroup.orderOf_coe]
    exact hw2
  obtain ⟨c, hc⟩ := isConj_iff.1 (hone _ _ hwo ((Subgroup.orderOf_coe (⟨u, huT⟩ : ↥T)).symm.trans
    hu))
  have hcu : (c : X) * (w : X) * (c : X)⁻¹ = u := congrArg Subtype.val hc
  have hle : (P : Subgroup X).map (MulAut.conj (c : X)).toMonoidHom ≤
      centralizer ({u} : Set X) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hcu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    symm
    calc (c : X) * (w : X) * (c : X)⁻¹ * ((c : X) * p * (c : X)⁻¹)
        = (c : X) * ((w : X) * p) * (c : X)⁻¹ := by group
      _ = (c : X) * (p * (w : X)) * (c : X)⁻¹ := by rw [hwc p hp]
      _ = (c : X) * p * (c : X)⁻¹ * ((c : X) * (w : X) * (c : X)⁻¹) := by group
  apply hC
  have hcard : Nat.card ↥((P : Subgroup X).map (MulAut.conj (c : X)).toMonoidHom) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (c : X)).injective, hP]
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

end CFSG.EvenSporadicStandard.TwoHS.GH312
