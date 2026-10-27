module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GH74.GLS.Bg.TwoGroups.Models

public section

namespace CFSG.OddStandard.ThmC.O2.A8

open CFSG Subgroup

structure Hyp {K : Type} [Group K] {A : Type} [Group A] (ρ : K →* MulAut A) (V : Sylow 2 K)
    (Z : Subgroup A) : Prop where
  comm : ∀ a b : A, a * b = b * a
  sq : ∀ a : A, a * a = 1
  cardA : Nat.card A = 16
  inj : Function.Injective ρ
  cardV : Nat.card (V : Subgroup K) = 4
  sqV : ∀ v ∈ (V : Subgroup K), v * v = 1
  cardZ : Nat.card Z = 4
  fix : ∀ v ∈ (V : Subgroup K), v ≠ 1 → ∀ a : A, ρ v a = a ↔ a ∈ Z
  notinv : ¬ ∀ k : K, ∀ a ∈ Z, ρ k a ∈ Z

end CFSG.OddStandard.ThmC.O2.A8
