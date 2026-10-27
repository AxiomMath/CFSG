module

public import CFSG.LargeExtraspecial.S3Qa
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourDefs

public section

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.LargeExtraspecial CFSG.RankThree.PartOne.KCOrthogonal Module
open scoped MatrixGroups

@[expose] def HermStabFacts : Prop :=
  ∀ (E : Type) [Field E] [Algebra (ZMod 2) E] (P : EvenNormPlane (ZMod 2) E), Nat.card E = 4 →
    ∀ X : hermFourSpace P.σ, hermFourForm P X = 1 →
      Nat.card {h : SL(2, E) // hermFourRho P h X = X} = 6 ∧
      (∀ Y : hermFourSpace P.σ,
        (∀ h : SL(2, E), hermFourRho P h X = X → hermFourRho P h Y = Y) → Y = 0 ∨ Y = X) ∧
      (∀ c : SL(2, E), (∀ h : SL(2, E), hermFourRho P h X = X → c * h = h * c) → c = 1) ∧
      (∀ c : SL(2, E), (∀ h : SL(2, E), hermFourRho P h X = X →
        hermFourRho P (c * h * c⁻¹) X = X) → hermFourRho P c X = X)

variable {G : Type} [Group G] [Finite G]

structure ThompsonInput (S : Setting G) (g x : G) (K Y : Subgroup S.O) : Prop where
  mem_QG : x ∈ S.QG
  mem_Qa : x ∈ S.Qa g
  orderOf_eq : orderOf x = 2
  ne_z : x ≠ S.z
  cl_ne : S.cl x ≠ S.cl (g * S.z * g⁻¹)
  mem_Y : ∀ m : S.O, m ∈ Y ↔ m ∈ S.Mbar ∧ (m : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl x) = S.cl x
  quasisimple : CFSG.Open.IsQuasisimple K
  subnormal : CFSG.Open.IsSubnormal K Y
  le_closure : K ≤ Subgroup.closure {k : S.O | k ∈ K ∧ k ^ 5 = 1}
  finrank_le : ∀ C : Submodule (ZMod 2) S.Qt,
    (∀ v ∈ C, ∀ k ∈ K, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → finrank (ZMod 2) C ≤ 2
  eq_one : ∀ l ∈ S.Lbar g, (∀ k ∈ K, l * k = k * l) → l = 1

end CFSG.GF2Type.Smith1979.W4Swap
