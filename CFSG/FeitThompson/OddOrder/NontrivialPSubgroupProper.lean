module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Foundations.PGroupNontrivialCenter
import CFSG.FeitThompson.Local.SimpleGroupNormalizerProper

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p n : ℕ}

private theorem nontrivial_of_top_ne_bot (h : (⊤ : Subgroup G) ≠ ⊥) : Nontrivial G := by
  obtain ⟨x, y, hxy⟩ := (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup G)).mpr h
  exact ⟨x, y, by simpa using hxy⟩

theorem lt_top_of_isPGroup [Finite G] [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hp : p.Prime) {P : Subgroup G} (hP : P ≠ ⊥) (hPp : IsPGroup p P) : P < ⊤ := by
  have := Fact.mk hp
  refine lt_top_iff_ne_top.2 fun hPtop => ?_
  subst hPtop
  have := nontrivial_of_top_ne_bot hP
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hPp.of_equiv Subgroup.topEquiv)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd (by simpa using hm) Finite.one_lt_card.ne'
    · exact h
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact center_ne_bot hp hm hm1 h
  · exact hG (Subgroup.center_eq_top_iff.mp h)

theorem normalizer_lt_top_of_isPGroup [Finite G] [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hp : p.Prime) {P : Subgroup G} (hP : P ≠ ⊥) (hPp : IsPGroup p P) :
    normalizer (P : Set G) < ⊤ :=
  normalizer_lt_top_of_isSimpleGroup (bot_lt_iff_ne_bot.2 hP) (lt_top_of_isPGroup hG hp hP hPp)

theorem not_normal_of_isPGroup [Finite G] [IsSimpleGroup G] (hG : ¬ IsMulCommutative G)
    (hp : p.Prime) {P : Subgroup G} (hP : P ≠ ⊥) (hPp : IsPGroup p P) : ¬ P.Normal := fun h =>
  (normalizer_lt_top_of_isPGroup hG hp hP hPp).ne (normalizer_eq_top_iff.2 h)

theorem lt_top_and_normalizer_lt_top_of_natCard_eq_pow [Finite G] (_hodd : Odd (Nat.card G))
    (hsimple : IsSimpleGroup G) (hG : ¬ IsMulCommutative G)
    (_hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) (hp : p.Prime) {P : Subgroup G}
    (hP : P ≠ ⊥) (hPn : Nat.card P = p ^ n) : P < ⊤ ∧ normalizer (P : Set G) < ⊤ :=
  have := hsimple
  have hPp : IsPGroup p P := IsPGroup.of_card hPn
  ⟨lt_top_of_isPGroup hG hp hP hPp, normalizer_lt_top_of_isPGroup hG hp hP hPp⟩

end CFSG.FeitThompson
