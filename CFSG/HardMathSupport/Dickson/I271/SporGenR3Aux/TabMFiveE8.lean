module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabMFive

open Equiv Equiv.Perm

@[expose] def e8A : Perm (Fin 12) := swap 0 1 * swap 2 3

@[expose] def e8B : Perm (Fin 12) := swap 0 2 * swap 1 3

@[expose] def e8C : Perm (Fin 12) := swap 4 5 * swap 6 7

theorem e8_gen_comm : ∀ x ∈ ({e8A, e8B, e8C} : Set (Perm (Fin 12))),
    ∀ y ∈ ({e8A, e8B, e8C} : Set (Perm (Fin 12))), x * y = y * x := by
  unfold e8A e8B e8C
  rintro x (rfl | rfl | rfl) y (rfl | rfl | rfl) <;> decide +kernel

theorem e8_gen_sq : ∀ x ∈ ({e8A, e8B, e8C} : Set (Perm (Fin 12))), x * x = 1 := by
  unfold e8A e8B e8C
  rintro x (rfl | rfl | rfl) <;> decide +kernel

theorem e8_gen_alt :
    ∀ x ∈ ({e8A, e8B, e8C} : Set (Perm (Fin 12))), x ∈ alternatingGroup (Fin 12) := by
  unfold e8A e8B e8C
  rintro x (rfl | rfl | rfl) <;> (rw [mem_alternatingGroup]; decide +kernel)

@[expose] def e8Map : Bool × Bool × Bool → Perm (Fin 12) := fun x =>
  (if x.1 then e8A else 1) * (if x.2.1 then e8B else 1) * (if x.2.2 then e8C else 1)

theorem e8Map_injective : Function.Injective e8Map := by
  unfold e8Map e8A e8B e8C
  intro x y
  revert x y
  decide +kernel

@[expose] def e8Sub : Subgroup (Perm (Fin 12)) := Subgroup.closure {e8A, e8B, e8C}

theorem e8Sub_comm : ∀ x ∈ e8Sub, ∀ y ∈ e8Sub, x * y = y * x := by
  letI : CommGroup ↥e8Sub :=
    Subgroup.closureCommGroupOfComm fun x hx y hy _ => e8_gen_comm x hx y hy
  intro x hx y hy
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥e8Sub) ⟨y, hy⟩)

theorem e8Sub_sq : ∀ x ∈ e8Sub, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact e8_gen_sq x hx
  | one => simp
  | mul x y hx hy hx' hy' =>
    have h := e8Sub_comm x hx y hy
    calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
      _ = x * (x * y) * y := by rw [h]
      _ = x * x * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hx', hy', mul_one]
  | inv x hx hx' =>
    rw [← mul_inv_rev, hx', inv_one]

theorem e8Sub_le_alt : e8Sub ≤ alternatingGroup (Fin 12) :=
  (Subgroup.closure_le _).2 fun x hx => e8_gen_alt x hx

theorem e8Map_mem (x : Bool × Bool × Bool) : e8Map x ∈ e8Sub := by
  have hA : e8A ∈ e8Sub := Subgroup.subset_closure (by simp)
  have hB : e8B ∈ e8Sub := Subgroup.subset_closure (by simp)
  have hC : e8C ∈ e8Sub := Subgroup.subset_closure (by simp)
  unfold e8Map
  refine e8Sub.mul_mem (e8Sub.mul_mem ?_ ?_) ?_
  · split_ifs
    exacts [hA, e8Sub.one_mem]
  · split_ifs
    exacts [hB, e8Sub.one_mem]
  · split_ifs
    exacts [hC, e8Sub.one_mem]

theorem card_e8Sub : 8 ≤ Nat.card e8Sub := by
  have h := Nat.card_le_card_of_injective (fun x : Bool × Bool × Bool => (⟨e8Map x, e8Map_mem x⟩ :
    ↥e8Sub)) (fun x y hxy => e8Map_injective (congrArg Subtype.val hxy))
  have h8 : Nat.card (Bool × Bool × Bool) = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

theorem exists_e8_map {G : Type*} [Group G] (ψ : alternatingGroup (Fin 12) →* G)
    (hψ : Function.Injective ψ) :
    ∃ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ (∀ a ∈ A, a ^ 2 = 1) ∧
      8 ≤ Nat.card ↥A ∧ A ≤ ψ.range := by
  set S : Subgroup (alternatingGroup (Fin 12)) := e8Sub.subgroupOf (alternatingGroup (Fin 12))
    with hS
  refine ⟨S.map ψ, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨s', hs', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (e8Sub_comm _ hs _ hs')
  · rintro _ ⟨s, hs, rfl⟩
    rw [sq, ← map_mul]
    have : s * s = 1 := Subtype.ext (e8Sub_sq _ hs)
    rw [this, map_one]
  · rw [Subgroup.card_map_of_injective hψ, hS,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe e8Sub_le_alt).toEquiv]
    exact card_e8Sub
  · exact Subgroup.map_le_range ψ S

end CFSG.HardMathSupport.Dickson.I271.TabMFive
