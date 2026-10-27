module

public import CFSG.LargeExtraspecial.S4CESmallMinus
public import CFSG.LargeExtraspecial.S4CESmallPlusMain
public import CFSG.LargeExtraspecial.S4CEA6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem ker_eq_bot_of_omegaPair_four {K : Type*} [Group K] [Finite K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (h4 : finrank (ZMod 2) V = 4) (ha0 : a ≠ 0)
    (hQa : Q a = 0) (h : CEHyp π E a (omegaGroup Q hQ) (pointRadical Q a)) : π.ker = ⊥ := by
  by_cases hP : S10.PlusType4 Q
  · exact ker_eq_bot_of_omegaPair_plus_four hQ h4 hP ha0 hQa h
  · refine ker_eq_bot_of_omegaPair_minus_four hQ h4 (fun U hU => ?_) ha0 hQa h
    by_contra hc
    push Not at hc
    exact hP ⟨U, hU, hc⟩

theorem centralExtInput_of_omegaPair_four {K : Type*} [Group K] [Finite K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (ha0 : a ≠ 0) (h4 : finrank (ZMod 2) V = 4) {Q : QuadraticForm (ZMod 2) V}
    (hQ : Q.polarBilin.Nondegenerate) (hQa : Q a = 0) (hX : X = omegaGroup Q hQ)
    (hE₀ : E₀ = pointRadical Q a) (h : CEHyp π E a X E₀) :
    π.ker = ⊥ ∨ (A6Pair X E₀ a ∧ Nat.card π.ker = 3) := by
  subst hX hE₀
  exact Or.inl (ker_eq_bot_of_omegaPair_four hQ h4 ha0 hQa h)

theorem centralExtInput_of_a6Pair {K : Type*} [Group K] [Finite K]
    {π : K →* (V ≃ₗ[ZMod 2] V)} {E : Subgroup K} {a : V} {X E₀ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (ha0 : a ≠ 0) (hA : A6Pair X E₀ a) (h : CEHyp π E a X E₀) :
    π.ker = ⊥ ∨ (A6Pair X E₀ a ∧ Nat.card π.ker = 3) :=
  (ker_eq_bot_or_card_eq_three_of_a6Pair ha0 hA h).imp_right fun h3 => ⟨hA, h3⟩

end CFSG.LargeExtraspecial.S4
