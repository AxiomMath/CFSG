module

public import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.SubgroupIndicatorElementaryPlane
import CFSG.FeitThompson.Foundations.SolvablePerfectTrivial
public import Mathlib.GroupTheory.Nilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} {A K : Type*} [Group A] [Group K]

theorem exists_ne_one_autFixedSubgroup_not_le_commutator (hp : p.Prime)
    (hcard : Nat.card A = p ^ 2) (hexp : ∀ a : A, a ^ p = 1) [Finite K] [Group.IsSolvable K]
    [Nontrivial K] (ρ : A →* MulAut K) (hpK : ¬ p ∣ Nat.card K) :
    ∃ a : A, a ≠ 1 ∧ ¬ autFixedSubgroup (ρ a) ≤ _root_.commutator K := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have htop : (⊤ : Subgroup K) ≤ _root_.commutator K := by
    rw [← iSup_autFixedSubgroup_eq_top hp hcard hexp ρ hpK]
    exact iSup₂_le h
  exact not_subsingleton K
    (subsingleton_of_isSolvable_of_commutator_eq_top K (top_le_iff.mp htop))

theorem exists_ne_one_exists_apply_eq_self_not_mem_commutator (hp : p.Prime)
    (hcard : Nat.card A = p ^ 2) (hexp : ∀ a : A, a ^ p = 1) [Finite K] [Group.IsSolvable K]
    [Nontrivial K] (ρ : A →* MulAut K) (hpK : ¬ p ∣ Nat.card K) :
    ∃ a : A, a ≠ 1 ∧ ∃ x : K, ρ a x = x ∧ x ∉ _root_.commutator K := by
  obtain ⟨a, ha, hnot⟩ :=
    exists_ne_one_autFixedSubgroup_not_le_commutator hp hcard hexp ρ hpK
  obtain ⟨x, hx, hxc⟩ := SetLike.not_le_iff_exists.mp hnot
  exact ⟨a, ha, x, mem_autFixedSubgroup.mp hx, hxc⟩

theorem exists_ne_one_autFixedSubgroup_not_le_commutator_of_mulEquiv
    (e : A ≃* Multiplicative (ZMod p × ZMod p)) (hp : p.Prime) [Finite K] [Group.IsSolvable K]
    [Nontrivial K] (ρ : A →* MulAut K) (hpK : ¬ p ∣ Nat.card K) :
    ∃ a : A, a ≠ 1 ∧ ¬ autFixedSubgroup (ρ a) ≤ _root_.commutator K :=
  exists_ne_one_autFixedSubgroup_not_le_commutator hp (card_eq_sq_of_mulEquiv e hp)
    (pow_eq_one_of_mulEquiv e hp) ρ hpK

end CFSG.FeitThompson
