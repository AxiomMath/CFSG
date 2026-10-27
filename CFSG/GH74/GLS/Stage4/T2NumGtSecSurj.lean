module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Prime.Defs

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

theorem ng_not_dvd_pow_sub_one {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) : ¬ p ∣ p ^ m - 1 := by
  intro hd
  have h1 : p ∣ p ^ m := dvd_pow_self p (by omega)
  have h2 : p ∣ p ^ m - (p ^ m - 1) := Nat.dvd_sub h1 hd
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at h2
  exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

theorem ng_sec_surj {G : Type} [Group G] [Finite G] {A B : Subgroup G} {V : Type} [AddCommGroup V] [Finite V]
    (π : ↥A → V) (hcard : Nat.card V = B.relIndex A) (hπ0 : ∀ a, π a = 0 ↔ (a : G) ∈ B)
    (hπadd : ∀ a a', π (a * a') = π a + π a') : Function.Surjective π := by
  classical
  have hπ1 : π 1 = 0 := by
    have h := hπadd 1 1
    rw [mul_one] at h
    have h' : π 1 + π 1 = π 1 + 0 := by rw [← h, add_zero]
    exact add_left_cancel h'
  have hπinv : ∀ a, π a⁻¹ = - π a := fun a => by
    have := hπadd a⁻¹ a
    rw [inv_mul_cancel, hπ1] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  let g : (↥A ⧸ B.subgroupOf A) → V :=
    Quotient.lift (s := QuotientGroup.leftRel (B.subgroupOf A)) π (fun a b hab => by
      have hab' : a⁻¹ * b ∈ B.subgroupOf A := (QuotientGroup.leftRel_apply).1 hab
      have h0 : π (a⁻¹ * b) = 0 := (hπ0 _).2 (Subgroup.mem_subgroupOf.1 hab')
      have := hπadd a (a⁻¹ * b)
      rw [mul_inv_cancel_left, h0, add_zero] at this
      exact this.symm)
  have hg : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    have hπab : π a = π b := hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    apply (hπ0 _).1
    rw [hπadd, hπinv, hπab, neg_add_cancel]
  have hle : Nat.card V ≤ Nat.card (↥A ⧸ B.subgroupOf A) := by
    rw [hcard, ← Subgroup.index_eq_card]
    rfl
  have hbij := hg.bijective_of_nat_card_le hle
  intro v
  obtain ⟨x, hx⟩ := hbij.2 v
  induction x using QuotientGroup.induction_on with | H a => ?_
  exact ⟨a, hx⟩

end CFSG.GH74.GLS.Stage4.Rest
