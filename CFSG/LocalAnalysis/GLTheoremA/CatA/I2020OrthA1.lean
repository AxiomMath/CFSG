module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020NotJType
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open Polynomial Module CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory
  CFSG.ComponentClassification.CatLeaf

variable {K V : Type} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p q f : ℕ} {x : V ≃ₗ[K] V}

section Cert



theorem not_jType_componentImage_of_mult_two (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : primaryMultiplicity x.toLinearMap h = 2)
    (hqs : CFSG.IsQuasisimple ↥(specialBlock Q x h))
    (hcardPSL2 : ∃ f' : ℕ, 1 ≤ f' ∧ Nat.card (PSimple p (componentImage Q x h)) * 2 =
      (q ^ f') * ((q ^ f') ^ 2 - 1)) :
    ¬ JType p q (componentImage Q x h) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨f', hf'1, hf'⟩ := hcardPSL2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hgcd : Nat.gcd 2 (q ^ f' - 1) = 2 := gcd_two_pow_sub_one hqodd (by omega)
  have hcard : Nat.card (PSimple p (componentImage Q x h)) *
      lieOrderDivisor .PSL 2 (q ^ f') = lieOrderNumerator .PSL 2 (q ^ f') := by
    simp only [lieOrderDivisor, lieOrderNumerator_PSL_two, hgcd]
    exact hf'
  exact not_jType_of_card hq hq2 (Or.inl ⟨rfl, rfl⟩) hf'1 hcard

theorem not_jType_fixedFactor_of_finrank_four (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hring : ringChar K = q) (hcardK : Nat.card K = q ^ f)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0)
    (hx : OddOrderIsometry Q p x)
    (hdim0 : Module.finrank K (fixedSpace x) = 4)
    {F : Subgroup (V ≃ₗ[K] V)} (hFq : CFSG.IsQuasisimple ↥F)
    (hFle : F ≤ supportedFixedDerived Q x)
    (hFn : (F.subgroupOf (supportedFixedDerived Q x)).Normal)
    (hcardPSL2 : ∃ f' : ℕ, 1 ≤ f' ∧
      Nat.card (PSimple p ((F.subgroupOf (orthDerived Q)).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) * 2 =
        (q ^ f') * ((q ^ f') ^ 2 - 1)) :
    ¬ JType p q ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨f', hf'1, hf'⟩ := hcardPSL2
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hgcd : Nat.gcd 2 (q ^ f' - 1) = 2 := gcd_two_pow_sub_one hqodd (by omega)
  have hcard : Nat.card (PSimple p ((F.subgroupOf (orthDerived Q)).map
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))))) *
      lieOrderDivisor .PSL 2 (q ^ f') = lieOrderNumerator .PSL 2 (q ^ f') := by
    simp only [lieOrderDivisor, lieOrderNumerator_PSL_two, hgcd]
    exact hf'
  exact not_jType_of_card hq hq2 (Or.inl ⟨rfl, rfl⟩) hf'1 hcard

end Cert

end CFSG.LocalAnalysis.GLTheoremA.I2020

end
