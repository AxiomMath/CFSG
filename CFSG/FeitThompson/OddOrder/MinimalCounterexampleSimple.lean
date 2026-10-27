module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
import CFSG.FeitThompson.Foundations.AbelianSolvable
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Foundations.SolvableExtensionNormalQuotient

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

universe u

variable {G : Type u} [Group G]

theorem nontrivial_of_not_isSolvable (hns : ¬ Group.IsSolvable G) : Nontrivial G :=
  not_subsingleton_iff_nontrivial.1 fun _ =>
    hns (Group.isSolvable_of_top_eq_bot G (Subsingleton.elim _ _))

theorem not_isMulCommutative_of_not_isSolvable (hns : ¬ Group.IsSolvable G) :
    ¬ IsMulCommutative G :=
  fun h => hns (isSolvable_of_isMulCommutative (G := G))

variable [Finite G] (hodd : Odd (Nat.card G)) (hns : ¬ Group.IsSolvable G)
  (hmin : ∀ (H : Type u) [Group H] [Finite H], Odd (Nat.card H) → Nat.card H < Nat.card G →
    Group.IsSolvable H)

include hodd hmin in
theorem isSolvable_of_ne_top_of_minimal {H : Subgroup G} (hH : H ≠ ⊤) : Group.IsSolvable H :=
  hmin H (odd_natCard_subgroup hodd H) (natCard_lt_natCard_of_ne_top hH)

include hodd hns hmin in
theorem isSimpleGroup_of_not_isSolvable_of_minimal : IsSimpleGroup G := by
  have := nontrivial_of_not_isSolvable hns
  refine (isSimpleGroup_iff G).2 ⟨inferInstance, fun N hN => ?_⟩
  by_contra hcon
  obtain ⟨hbot, htop⟩ := not_or.1 hcon
  have := hN
  have : Group.IsSolvable N := isSolvable_of_ne_top_of_minimal hodd hmin htop
  have : Group.IsSolvable (G ⧸ N) :=
    hmin (G ⧸ N) (odd_natCard_quotient N hodd)
      (natCard_quotient_lt_natCard_of_bot_lt N (bot_lt_iff_ne_bot.2 hbot))
  exact hns (isSolvable_of_normal_of_quotient N)

include hodd hns hmin in
theorem isSimpleGroup_and_not_isMulCommutative_and_forall_isSolvable :
    IsSimpleGroup G ∧ ¬ IsMulCommutative G ∧ ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H :=
  ⟨isSimpleGroup_of_not_isSolvable_of_minimal hodd hns hmin,
    not_isMulCommutative_of_not_isSolvable hns,
    fun _ h => isSolvable_of_ne_top_of_minimal hodd hmin h⟩

theorem isSolvable_of_odd_natCard_of_no_minimal_simple
    (h : ∀ (H : Type u) [Group H] [Finite H], Odd (Nat.card H) → IsSimpleGroup H →
      ¬ IsMulCommutative H → (∀ K : Subgroup H, K ≠ ⊤ → Group.IsSolvable K) → False)
    (n : ℕ) : ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n → Odd (Nat.card H) →
      Group.IsSolvable H := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro H _ _ hcard hoddH
    by_contra hnsH
    have hm : ∀ (K : Type u) [Group K] [Finite K], Odd (Nat.card K) →
        Nat.card K < Nat.card H → Group.IsSolvable K :=
      fun K _ _ hK hlt => ih (Nat.card K) (hcard ▸ hlt) K rfl hK
    obtain ⟨h1, h2, h3⟩ :=
      isSimpleGroup_and_not_isMulCommutative_and_forall_isSolvable hoddH hnsH hm
    exact h H hoddH h1 h2 h3

theorem isSolvable_of_odd_natCard_of_no_minimal_simple'
    (h : ∀ (H : Type u) [Group H] [Finite H], Odd (Nat.card H) → IsSimpleGroup H →
      ¬ IsMulCommutative H → (∀ K : Subgroup H, K ≠ ⊤ → Group.IsSolvable K) → False)
    (hodd : Odd (Nat.card G)) : Group.IsSolvable G :=
  isSolvable_of_odd_natCard_of_no_minimal_simple h (Nat.card G) G rfl hodd

end CFSG.FeitThompson
