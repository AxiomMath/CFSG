module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

import CFSG.Mathlib.GroupTheory.PermCenter

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Harada.L27

open Subgroup

private def threeCycleA5 : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
    Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
      (show Equiv.Perm.IsSwap (Equiv.swap (0 : Fin 5) 1) from ⟨0, 1, by decide, rfl⟩)
      (show Equiv.Perm.IsSwap (Equiv.swap (1 : Fin 5) 2) from ⟨1, 2, by decide, rfl⟩)⟩

private def permSignFin (σ : Equiv.Perm (Fin 5)) : ℤˣ :=
  ∏ j, ∏ i ∈ Finset.Iio j, (if σ i < σ j then 1 else -1)

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem exists_orderOf_eq_three_a5 : ∃ x : alternatingGroup (Fin 5), orderOf x = 3 := by
  refine ⟨threeCycleA5, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime
  · decide
  · decide

theorem exists_orderOf_eq_five_a5 : ∃ x : alternatingGroup (Fin 5), orderOf x = 5 := by
  refine ⟨⟨finRotate 5,
    Equiv.Perm.finRotate_bit1_mem_alternatingGroup (n := 2)⟩, ?_⟩
  simp only [Subgroup.orderOf_mk]
  rw [(isCycle_finRotate_of_le (n := 5) (by norm_num : 2 ≤ 5)).orderOf,
    support_finRotate_of_le (n := 5) (by norm_num : 2 ≤ 5)]
  simp

theorem commutator_eq_self_of_equiv_a5 {X : Type*} [Group X] (F : Subgroup X)
    (e : F ≃* alternatingGroup (Fin 5)) : ⁅F, F⁆ = F := by
  rw [← Subgroup.isPerfect_iff]
  have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem eq_one_of_forall_comm_of_equiv_a5 {X : Type*} [Group X] (F : Subgroup X)
    (e : F ≃* alternatingGroup (Fin 5)) {g : X} (hg : g ∈ F) (h : ∀ f ∈ F, f * g = g * f) :
    g = 1 := by
  have hmem : e ⟨g, hg⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨f, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (h f f.2))
  have h1 : e ⟨g, hg⟩ = 1 := by
    have hmem' := hmem
    rw [alternatingGroup.center_eq_bot (α := Fin 5) (by simp)] at hmem'
    exact Subgroup.mem_bot.mp hmem'
  have hsub : (⟨g, hg⟩ : F) = 1 := e.injective (by rw [h1, map_one])
  exact Subtype.ext_iff.mp hsub

theorem inf_eq_bot_of_equiv_a5 {X : Type*} [Group X] (F : Subgroup X)
    (e : F ≃* alternatingGroup (Fin 5)) (S : Subgroup X) [S.Normal] (hS : Group.IsSolvable S) :
    F ⊓ S = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥F := e.isSimpleGroup
  have : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have : Group.IsPerfect ↥F :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hNnormal : ((F ⊓ S).subgroupOf F).Normal := by
    have h : (F ⊓ S).subgroupOf F = S.subgroupOf F := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h]
    infer_instance
  rcases Subgroup.Normal.eq_bot_or_eq_top ((F ⊓ S).subgroupOf F) with hbot | htop
  · apply le_antisymm _ bot_le
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥F) ∈ (F ⊓ S).subgroupOf F :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hbot] at hx'
    exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hx')
  · exfalso
    have hFS : F ≤ S := by
      intro x hx
      have hx' : (⟨x, hx⟩ : ↥F) ∈ (F ⊓ S).subgroupOf F := by
        rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp hx').2
    have : Group.IsSolvable ↥S := hS
    let f : ↥F →* ↥S := F.subtype.codRestrict S (fun x => hFS x.2)
    have : Group.IsSolvable ↥F :=
      Group.isSolvable_of_isSolvable_injective (f := f) (by
        intro a b hab
        exact Subtype.ext (show (a : X) = (b : X) from congrArg (fun z : ↥S => (z : X)) hab))
    exact (Group.IsPerfect.not_isSolvable ↥F) inferInstance

theorem commutator_equiv_a5_of_equiv_perm_five {X : Type*} [Group X] (P : Subgroup X)
    (e : P ≃* Equiv.Perm (Fin 5)) : Nonempty (↥⁅P, P⁆ ≃* alternatingGroup (Fin 5)) := by
  have hmap : (commutator ↥P).map (e : ↥P →* Equiv.Perm (Fin 5)) =
      commutator (Equiv.Perm (Fin 5)) := by
    rw [commutator_def ↥P, commutator_def (Equiv.Perm (Fin 5)), Subgroup.map_commutator]
    simp
  refine ⟨?_⟩
  let g1 : ↥⁅P, P⁆ ≃* (commutator ↥P) :=
    ((Subgroup.equivMapOfInjective (commutator ↥P) P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator P))).symm
  let g2 : (commutator ↥P) ≃* ↥(commutator (Equiv.Perm (Fin 5))) :=
    (e.subgroupMap (commutator ↥P)).trans (MulEquiv.subgroupCongr hmap)
  exact g1.trans (g2.trans (MulEquiv.subgroupCongr
    (alternatingGroup.commutator_perm_eq (by simp))))

theorem inf_eq_bot_of_equiv_perm_five {X : Type*} [Group X] (P : Subgroup X)
    (e : P ≃* Equiv.Perm (Fin 5)) (S : Subgroup X) [S.Normal] (hS : Group.IsSolvable S) :
    P ⊓ S = ⊥ := by
  obtain ⟨eD⟩ := commutator_equiv_a5_of_equiv_perm_five P e
  have hDbot : ⁅P, P⁆ ⊓ S = ⊥ := inf_eq_bot_of_equiv_a5 ⁅P, P⁆ eD S hS
  have hND : (P ⊓ S) ⊓ ⁅P, P⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : x ∈ ⁅P, P⁆ ⊓ S := ⟨hx.2, hx.1.2⟩
    rw [hDbot] at hx'
    exact hx'
  have hNnormal : ((P ⊓ S).subgroupOf P).Normal := by
    have h : (P ⊓ S).subgroupOf P = S.subgroupOf P := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [h]
    infer_instance
  have hNle : ⁅P ⊓ S, P⁆ ≤ P ⊓ S := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right).mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hNnormal)
  have hcomm : ⁅P ⊓ S, P⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    calc ⁅P ⊓ S, P⁆ ≤ (P ⊓ S) ⊓ ⁅P, P⁆ :=
          le_inf hNle (Subgroup.commutator_mono inf_le_left le_rfl)
      _ = ⊥ := hND
  have hNcent : P ⊓ S ≤ Subgroup.centralizer (P : Set X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcenter : Subgroup.center ↥P = ⊥ := by
    have h := Subgroup.map_center_eq (e : ↥P ≃* Equiv.Perm (Fin 5))
    rw [CFSG.center_perm_eq_bot_of_three_le_card (α := Fin 5) (by simp)] at h
    apply le_antisymm _ bot_le
    intro z hz
    have hz' : e z ∈ (Subgroup.center ↥P).map (e : ↥P →* Equiv.Perm (Fin 5)) :=
      ⟨z, hz, rfl⟩
    rw [h] at hz'
    have hz1 : e z = 1 := Subgroup.mem_bot.mp hz'
    rw [← map_one e] at hz1
    simpa using e.injective hz1
  apply le_antisymm _ bot_le
  intro z hz
  have hzc : (⟨z, hz.1⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hNcent hz) (w : X) w.2)
  rw [hcenter] at hzc
  exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hzc)

private theorem filter_card_centralizer_involution :
    ∀ x : alternatingGroup (Fin 5), x ≠ 1 → x * x = 1 →
      (Finset.univ.filter (fun y : alternatingGroup (Fin 5) => y * x = x * y)).card = 4 := by
  have : DecidablePred (· ∈ alternatingGroup (Fin 5)) := fun σ =>
    decidable_of_iff (permSignFin σ = 1)
      (by
        change permSignFin σ = 1 ↔ σ ∈ alternatingGroup (Fin 5)
        rw [Equiv.Perm.mem_alternatingGroup]
        unfold permSignFin
        rw [← Equiv.Perm.sign_eq_prod_prod_Iio])
  decide

theorem card_centralizer_involution_a5 (x : alternatingGroup (Fin 5)) (hx : x ≠ 1)
    (hx2 : x * x = 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 := by
  have hcard : Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) =
      (Finset.univ.filter (fun y : alternatingGroup (Fin 5) => y * x = x * y)).card := by
    have : DecidablePred (· ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) :=
      fun y => decidable_of_iff (y * x = x * y)
        (Subgroup.mem_centralizer_singleton_iff.symm)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subgroup.mem_centralizer_singleton_iff
  rw [hcard]
  exact filter_card_centralizer_involution x hx hx2

end CFSG.EvenSporadicStandard.HNRecog.Harada.L27
