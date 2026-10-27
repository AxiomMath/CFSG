module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem y7b_relIndex_eq_ncard_image {Q : Type*} {X C : Subgroup G} (hCX : C ≤ X) (β : G → Q)
    (hβ : ∀ x ∈ X, ∀ y ∈ X, β x = β y ↔ x⁻¹ * y ∈ C) :
    C.relIndex X = (β '' (X : Set G)).ncard := by
  have hcard : C.relIndex X = Nat.card (X ⧸ (C.subgroupOf X)) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
  let g : X → ↥(β '' (X : Set G)) := fun x => ⟨β (x : G), x, x.2, rfl⟩
  have hg : ∀ x y : X, QuotientGroup.leftRel (C.subgroupOf X) x y → g x = g y := by
    intro x y hxy
    apply Subtype.ext
    refine (hβ x x.2 y y.2).mpr ?_
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_inv, Subgroup.coe_mul]
      using QuotientGroup.leftRel_apply.mp hxy
  let f : (X ⧸ (C.subgroupOf X)) → ↥(β '' (X : Set G)) := fun q => Quotient.liftOn' q g hg
  have hf : ∀ x : X, f (QuotientGroup.mk x) = g x := by
    intro x
    exact QuotientGroup.quotient_liftOn_mk g hg x
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      induction a, b using Quotient.inductionOn₂' with
      | _ x y =>
        rw [hf x, hf y] at hab
        apply QuotientGroup.eq.mpr
        have h2 : (x : G)⁻¹ * (y : G) ∈ C :=
          (hβ x x.2 y y.2).mp (congrArg Subtype.val hab)
        simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_inv, Subgroup.coe_mul] using h2
    · rintro ⟨q, x, hx, hq⟩
      refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      rw [hf ⟨x, hx⟩]
      exact Subtype.ext hq
  calc C.relIndex X = Nat.card (X ⧸ (C.subgroupOf X)) := hcard
    _ = Nat.card ↥(β '' (X : Set G)) := Nat.card_congr (Equiv.ofBijective f hbij)
    _ = (β '' (X : Set G)).ncard := Nat.card_coe_set_eq _

theorem y7b_eq_of_relIndex_le {C Z X : Subgroup G} (hCZ : C ≤ Z) (hZX : Z ≤ X) {n m : ℕ}
    (hn : C.relIndex Z = n) (hpos : 0 < n) (hm : C.relIndex X ≤ m) (hlt : m < 2 * n) :
    Z = X := by
  have hmul : n * Z.relIndex X = C.relIndex X := by
    rw [← hn, Subgroup.relIndex_mul_relIndex C Z X hCZ hZX]
  have hCpos : 0 < C.relIndex X := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos
  have hZpos : 0 < Z.relIndex X := by
    rcases Nat.eq_zero_or_pos (Z.relIndex X) with h | h
    · rw [h, mul_zero] at hmul
      omega
    · exact h
  have hone : Z.relIndex X = 1 := by
    by_contra hne
    have h2 : 2 ≤ Z.relIndex X := by omega
    have : 2 * n ≤ C.relIndex X := by
      rw [← hmul, Nat.mul_comm 2 n]
      exact Nat.mul_le_mul_left n h2
    omega
  have hXZ : X ≤ Z := Subgroup.relIndex_eq_one.mp hone
  exact le_antisymm hZX hXZ

end CFSG.OddStandard.HigherRank.YamadaG23
