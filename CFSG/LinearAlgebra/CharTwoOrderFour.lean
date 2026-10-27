module

public import Mathlib.GroupTheory.OrderOfElement
import CFSG.RankThree.PartOne.K133.PerfectUnip4
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.LinearAlgebra

theorem sq_eq_one_of_pow_four_eq_one_of_finrank_le_two {F V : Type*} [Field F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (hV : Module.finrank F V ≤ 2)
    {g : V ≃ₗ[F] V} (hg : g ^ 4 = 1) : g ^ 2 = 1 := by
  rcases subsingleton_or_nontrivial V with hV0 | hV0
  · exact LinearEquiv.ext fun v => Subsingleton.elim _ _
  have : CharP (Module.End F V) 2 :=
    charP_of_injective_algebraMap (algebraMap F (Module.End F V)).injective 2
  have hcoe : ∀ n : ℕ, ((g ^ n : V ≃ₗ[F] V) : Module.End F V) = (g : Module.End F V) ^ n :=
    map_pow (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := F) (M := V)) g
  have hf4 : (g : Module.End F V) ^ 4 = 1 := by
    rw [← hcoe, hg]
    rfl
  have hnil : IsNilpotent ((g : Module.End F V) - 1) := by
    refine IsNilpotent.mk _ 4 ?_
    have h : ((g : Module.End F V) - 1) ^ 2 ^ 2 = 0 := by
      rw [sub_pow_char_pow_of_commute (p := 2) (n := 2)
        (Commute.one_right (g : Module.End F V))]
      rw [show (2 : ℕ) ^ 2 = 4 from rfl, hf4, one_pow, sub_self]
    exact h
  have hsq : ((g : Module.End F V) - 1) ^ 2 = 0 :=
    pow_eq_zero_of_le hV (CFSG.RankThree.PartOne.K133.pow_finrank_eq_zero_of_isNilpotent hnil)
  have hf2 : (g : Module.End F V) ^ 2 = 1 := by
    have h := sub_pow_char_of_commute (p := 2) (Commute.one_right (g : Module.End F V))
    rw [hsq, one_pow] at h
    exact sub_eq_zero.mp h.symm
  apply LinearEquiv.toLinearMap_injective
  rw [hcoe, hf2]
  rfl

theorem three_le_finrank_of_injective_of_orderOf_eq_four {G F V : Type*} [Group G] [Field F]
    [CharP F 2] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {ρ : G →* (V ≃ₗ[F] V)} (hρ : Function.Injective ρ) {x : G} (hx : orderOf x = 4) :
    3 ≤ Module.finrank F V := by
  by_contra h
  have hV : Module.finrank F V ≤ 2 := by omega
  have hx4 : x ^ 4 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have h1 : (ρ x) ^ 4 = 1 := by rw [← map_pow, hx4, map_one]
  have h2 : (ρ x) ^ 2 = 1 := sq_eq_one_of_pow_four_eq_one_of_finrank_le_two hV h1
  have hx2 : x ^ 2 = 1 := hρ (by rw [map_pow, h2, map_one])
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at hdvd
  omega

end CFSG.LinearAlgebra
