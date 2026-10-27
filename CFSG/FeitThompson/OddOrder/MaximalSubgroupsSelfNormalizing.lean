module
public import Mathlib.GroupTheory.Solvable
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G]

theorem not_isCoatom_bot_of_not_isMulCommutative (h : ¬ IsMulCommutative G) :
    ¬ IsCoatom (⊥ : Subgroup G) := by
  intro hbot
  have hnt : Nontrivial G := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hbot.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  have htop : Subgroup.zpowers a = ⊤ :=
    hbot.2 _ (bot_lt_iff_ne_bot.2 (by simpa [Subgroup.zpowers_eq_bot] using ha))
  have : IsCyclic G := isCyclic_iff_exists_zpowers_eq_top.2 ⟨a, htop⟩
  exact h inferInstance

theorem normalizer_coe_eq_of_isCoatom [IsSimpleGroup G] (h : ¬ IsMulCommutative G)
    {M : Subgroup G} (hM : IsCoatom M) : Subgroup.normalizer (M : Set G) = M := by
  rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with hle | hlt
  · exact hle.symm
  · have hnormal : M.Normal := Subgroup.normalizer_eq_top_iff.1 (hM.2 _ hlt)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with rfl | rfl
    · exact absurd hM (not_isCoatom_bot_of_not_isMulCommutative h)
    · exact absurd rfl hM.1

theorem mem_iff_forall_conj_mem_of_isCoatom [IsSimpleGroup G] (h : ¬ IsMulCommutative G)
    {M : Subgroup G} (hM : IsCoatom M) (g : G) :
    g ∈ M ↔ ∀ x : G, x ∈ M ↔ g⁻¹ * x * g ∈ M := by
  rw [← Subgroup.mem_normalizer_iff'' (H := M) (g := g), normalizer_coe_eq_of_isCoatom h hM]

theorem normalizer_coe_eq_of_isCoatom_of_oddOrder_of_proper_solvable
    [Finite G] [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (_hodd : Odd (Nat.card G))
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H)
    {M : Subgroup G} (hM : IsCoatom M) : Subgroup.normalizer (M : Set G) = M :=
  normalizer_coe_eq_of_isCoatom hna hM

end CFSG.FeitThompson
