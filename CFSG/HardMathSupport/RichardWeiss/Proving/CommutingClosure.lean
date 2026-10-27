module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Commute.Basic

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

theorem commute_of_mem_closure_of_pairwise {G : Type} [Group G] {X : Set G}
    (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {g k : G} (hg : g ∈ Subgroup.closure X)
    (hk : k ∈ Subgroup.closure X) : g * k = k * g := by
  have hX : ∀ x ∈ X, x ∈ Subgroup.centralizer (Subgroup.closure X : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem y hy => exact hc y hy x hx
    | one => simp
    | mul a b ha hb iha ihb =>
      calc a * b * x = a * (b * x) := mul_assoc _ _ _
        _ = a * (x * b) := by rw [ihb]
        _ = (a * x) * b := (mul_assoc _ _ _).symm
        _ = (x * a) * b := by rw [iha]
        _ = x * (a * b) := mul_assoc _ _ _
    | inv a ha iha => exact Commute.inv_left (show Commute a x from iha)
  have hcl : Subgroup.closure X ≤ Subgroup.centralizer (Subgroup.closure X : Set G) :=
    (Subgroup.closure_le _).mpr hX
  exact ((Subgroup.mem_centralizer_iff.mp (hcl hg)) k hk).symm

theorem sq_eq_one_of_mem_closure_of_pairwise {G : Type} [Group G] {X : Set G}
    (h2 : ∀ x ∈ X, x ^ 2 = 1) (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) {g : G}
    (hg : g ∈ Subgroup.closure X) : g ^ 2 = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h2 x hx
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := commute_of_mem_closure_of_pairwise hc ha hb
    rw [Commute.mul_pow hab, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem pairwise_closure_sq_and_commute {G : Type} [Group G] (X : Set G)
    (h2 : ∀ x ∈ X, x ^ 2 = 1) (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    (∀ g ∈ Subgroup.closure X, g ^ 2 = 1) ∧
      ∀ g ∈ Subgroup.closure X, ∀ h ∈ Subgroup.closure X, g * h = h * g :=
  ⟨fun _ hg => sq_eq_one_of_mem_closure_of_pairwise h2 hc hg,
   fun _ hg _ hh => commute_of_mem_closure_of_pairwise hc hg hh⟩

end CFSG.HardMathSupport.RichardWeiss.Proving

end
