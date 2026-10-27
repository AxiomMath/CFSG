module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPreimage
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHullFixedPoints
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.AS76b

namespace Lemma39

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull

theorem exists_odd_preimage {Q Q' : Type*} [Group Q] [Finite Q] [Group Q'] (f : Q →* Q') (x : Q)
    (hx : Odd (orderOf (f x))) : ∃ y ∈ zpowers x, Odd (orderOf y) ∧ f y = f x := by
  have hpos : 0 < orderOf (f x) := hx.pos
  obtain ⟨e, q, hq, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hx' : Odd (orderOf (x ^ 2 ^ e)) := by
    refine Odd.of_dvd_nat hq (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, ← hn, pow_orderOf_eq_one]
  rcases Nat.lt_or_ge 1 (orderOf (f x)) with h1 | h1
  · have hcop : Nat.Coprime (2 ^ e) (orderOf (f x)) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hx)
    obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
    refine ⟨(x ^ 2 ^ e) ^ j, pow_mem (pow_mem (mem_zpowers x) _) _,
      Odd.of_dvd_nat hx' (orderOf_pow_dvd j), ?_⟩
    rw [map_pow, map_pow, ← pow_mul, ← pow_mod_orderOf, hj, pow_one]
  · have hfx : f x = 1 := orderOf_eq_one_iff.mp (by omega)
    exact ⟨1, one_mem _, by rw [orderOf_one]; exact odd_one, by rw [map_one, hfx]⟩

variable {G : Type} [Group G] [Finite G]

end Lemma39

end CFSG.ComponentClassification.AS76b
