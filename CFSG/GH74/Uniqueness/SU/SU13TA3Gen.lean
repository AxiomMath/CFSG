module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

public section

namespace CFSG.GH74.Uniqueness.SU.SU13.TA

open Subgroup Equiv Equiv.Perm

theorem card_sup_of_commute {P : Type*} [Group P] {X Y : Subgroup P}
    (hc : ∀ x ∈ X, ∀ y ∈ Y, Commute x y) (hd : Disjoint X Y) :
    Nat.card ↥(X ⊔ Y) = Nat.card X * Nat.card Y := by
  have hcomm : ∀ (m : X) (n : Y), Commute (X.subtype m) (Y.subtype n) := fun m n =>
    hc m m.2 n n.2
  have hinj : Function.Injective (MonoidHom.noncommCoprod X.subtype Y.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨X.subtype_injective, Y.subtype_injective, by simpa [Subgroup.range_subtype] using hd⟩
  have hr := MonoidHom.noncommCoprod_range X.subtype Y.subtype hcomm
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm

section Parity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_centralizer_alternatingGroup {g : alternatingGroup α} {ρ : Perm α}
    (hρ : Perm.sign ρ = -1) (hc : Commute ρ (g : Perm α)) :
    Nat.card (centralizer ({g} : Set (alternatingGroup α))) * 2 =
      Nat.card (centralizer ({(g : Perm α)} : Set (Perm α))) := by
  set C : Subgroup (Perm α) := centralizer ({(g : Perm α)} : Set (Perm α)) with hC
  have hρC : ρ ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact hc.eq
  have hidx : ((alternatingGroup α).subgroupOf C).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨ρ, hρC⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Perm.mem_alternatingGroup, Subgroup.coe_mul, map_mul, hρ]
    rcases Int.units_eq_one_or (Perm.sign (b : Perm α)) with h | h
    · simp [h]
    · simp [h]
  have h1 := Subgroup.card_mul_index ((alternatingGroup α).subgroupOf C)
  rw [hidx] at h1
  have h2 : Nat.card (centralizer ({g} : Set (alternatingGroup α))) =
      Nat.card ((alternatingGroup α).subgroupOf C) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨(x.1 : Perm α), ?_⟩, x.1.2⟩
        invFun := fun y => ⟨⟨(y.1 : Perm α), y.2⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by
        have := Subgroup.mem_centralizer_singleton_iff.mp y.1.2
        exact this)
  rw [h2]
  exact h1

end Parity

end CFSG.GH74.Uniqueness.SU.SU13.TA
