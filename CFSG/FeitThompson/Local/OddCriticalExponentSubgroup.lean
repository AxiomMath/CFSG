module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
public import CFSG.FeitThompson.Local.CharacteristicCriticalSubgroup
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Local.CriticalPrimeTorsionDetectsAutomorphisms

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {p : ℕ} {P : Type*} [Group P]

structure IsOddCriticalExponentSubgroup (p : ℕ) (H : Subgroup P) : Prop where
  ne_bot : H ≠ ⊥
  characteristic : H.Characteristic
  pow_eq_one : ∀ x ∈ H, x ^ p = 1
  commutator_self_le_center : ⁅H, H⁆ ≤ (center ↥H).map H.subtype
  commutator_top_le_center : ⁅H, (⊤ : Subgroup P)⁆ ≤ (center ↥H).map H.subtype
  isPGroup_fixingSubgroup : IsPGroup p (fixingSubgroup (MulAut P) (H : Set P))

namespace IsOddCriticalExponentSubgroup

variable {H : Subgroup P} (hH : IsOddCriticalExponentSubgroup p H)

include hH

theorem nontrivial : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hH.ne_bot

theorem exponent_dvd : Monoid.exponent ↥H ∣ p :=
  Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
    Subtype.ext (by simpa using hH.pow_eq_one g g.2)

theorem commutator_top_le_inf_centralizer :
    ⁅H, (⊤ : Subgroup P)⁆ ≤ H ⊓ centralizer (H : Set P) := by
  rw [← map_center_subtype_eq_inf_centralizer]; exact hH.commutator_top_le_center

theorem exists_natCard_fixingSubgroup_eq_pow (hp : p.Prime) [Finite P] :
    ∃ n : ℕ, Nat.card (fixingSubgroup (MulAut P) (H : Set P)) = p ^ n := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.mp hH.isPGroup_fixingSubgroup

end IsOddCriticalExponentSubgroup

theorem commutator_le_center_of_commutator_le_map_center {C : Subgroup P}
    (h : ⁅C, C⁆ ≤ (center ↥C).map C.subtype) : commutator ↥C ≤ center ↥C := by
  rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, Subgroup.map_subtype_commutator]
  exact h

theorem coe_map_omega1_subtype_of_commutator_le_center (hodd : Odd p) {C : Subgroup P}
    (hcl : commutator ↥C ≤ center ↥C) :
    ((omega1 p ↥C).map C.subtype : Set P) = {x : P | x ∈ C ∧ x ^ p = 1} := by
  ext x
  simp only [SetLike.mem_coe, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, by simpa using congrArg Subtype.val (pow_eq_one_of_mem_omega1 hodd hcl hy)⟩
  · rintro ⟨hx, hxp⟩
    exact ⟨⟨x, hx⟩, mem_omega1_of_pow_eq_one (Subtype.ext (by simpa using hxp)), rfl⟩

theorem isOddCriticalExponentSubgroup_map_omega1 [Finite P] [Nontrivial P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) {C : Subgroup P} (hC : IsThompsonCritical C) :
    IsOddCriticalExponentSubgroup p ((omega1 p ↥C).map C.subtype) := by
  have hCchar := hC.characteristic
  have hCnt : Nontrivial ↥C := C.nontrivial_iff_ne_bot.mpr hC.ne_bot
  have hcl : commutator ↥C ≤ center ↥C :=
    commutator_le_center_of_commutator_le_map_center hC.commutator_self_le_center
  set H : Subgroup P := (omega1 p ↥C).map C.subtype with hHdef
  have hHC : H ≤ C := Subgroup.map_subtype_le _
  have hHchar : H.Characteristic := Subgroup.characteristic_of_characteristic_of_characteristic
  have hcoe : (H : Set P) = {x : P | x ∈ C ∧ x ^ p = 1} :=
    coe_map_omega1_subtype_of_commutator_le_center hodd hcl
  have htop : ⁅H, (⊤ : Subgroup P)⁆ ≤ (center ↥H).map H.subtype := by
    rw [le_map_center_subtype_iff]
    refine ⟨Subgroup.commutator_le_left _ _, ?_⟩
    calc ⁅H, (⊤ : Subgroup P)⁆ ≤ ⁅C, (⊤ : Subgroup P)⁆ := Subgroup.commutator_mono hHC le_rfl
      _ = ⁅(⊤ : Subgroup P), C⁆ := Subgroup.commutator_comm _ _
      _ ≤ (center ↥C).map C.subtype := hC.commutator_top_le_center
      _ ≤ centralizer (C : Set P) := by
          rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_right
      _ ≤ centralizer (H : Set P) := centralizer_le (by exact_mod_cast hHC)
  refine ⟨?_, hHchar, ?_, ?_, htop, ?_⟩
  · rw [hHdef, Ne, Subgroup.map_eq_bot_iff_of_injective (hf := C.subtype_injective)]
    exact ((omega1 p ↥C).nontrivial_iff_ne_bot).mp (omega1_nontrivial hp (hP.to_subgroup C))
  · intro x hx
    have hx' : x ∈ (H : Set P) := hx
    rw [hcoe] at hx'
    exact hx'.2
  · exact (Subgroup.commutator_mono le_rfl le_top).trans htop
  · rw [hcoe]
    exact isPGroup_fixingSubgroup_pow_eq_one_of_critical hp hodd hP C hC.frattini_le_center
      hC.centralizer_eq_center

theorem exists_isOddCriticalExponentSubgroup [Finite P] [Nontrivial P] (hp : p.Prime)
    (hodd : Odd p) (hP : IsPGroup p P) :
    ∃ H : Subgroup P, IsOddCriticalExponentSubgroup p H := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  obtain ⟨C, hC⟩ := exists_isThompsonCritical hp hn
  exact ⟨_, isOddCriticalExponentSubgroup_map_omega1 hp hodd hP hC⟩

theorem exists_characteristic_exponent_prime_subgroup {n : ℕ} [Nontrivial P] (hp : p.Prime)
    (hodd : Odd p) (hP : Nat.card P = p ^ n) :
    ∃ H : Subgroup P, H ≠ ⊥ ∧ H.Characteristic ∧ (∀ x ∈ H, x ^ p = 1) ∧
      ⁅H, H⁆ ≤ (center ↥H).map H.subtype ∧
      ⁅H, (⊤ : Subgroup P)⁆ ≤ (center ↥H).map H.subtype ∧
      ∃ m : ℕ, Nat.card (fixingSubgroup (MulAut P) (H : Set P)) = p ^ m := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  obtain ⟨H, hH⟩ := exists_isOddCriticalExponentSubgroup hp hodd (IsPGroup.of_card hP)
  exact ⟨H, hH.ne_bot, hH.characteristic, hH.pow_eq_one, hH.commutator_self_le_center,
    hH.commutator_top_le_center, hH.exists_natCard_fixingSubgroup_eq_pow hp⟩

end

end CFSG.FeitThompson
