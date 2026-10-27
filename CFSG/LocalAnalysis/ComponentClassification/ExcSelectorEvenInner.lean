module

public import CFSG.LieType.Chevalley.RootLocalComponentFree
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.CLSOddToralOrdinaryComponentRootFactor
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.ExcSelector

open CFSG Subgroup CFSG.LieType.Chevalley
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem fixedSubgroup_conj {C : Type*} [Group C] (c : C) :
    fixedSubgroup (MulAut.conj c) = centralizer ({c} : Set C) := by
  ext x
  change c * x * c⁻¹ = x ↔ _
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * c = c * x * c⁻¹ * c := by rw [h]
      _ = c * x := by group
  · intro h
    rw [← h]
    group

theorem not_isComponentOf_fixedSubgroup_conj {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : RootWeightDatum K) {c : D.group} (hc : c ≠ 1) (hc2 : c ^ 2 = 1)
    (L : Subgroup D.group) : ¬ Assembly.IsComponentOf L (fixedSubgroup (MulAut.conj c)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hL
  rw [fixedSubgroup_conj] at hL
  set Q := zpowers c with hQ
  have hQp : IsPGroup 2 Q := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      show ((2 : ℕ) : ℤ) = 2 from rfl, zpow_two, ← sq, hc2, one_zpow, Subgroup.coe_one]
  have hQ1 : Q ≠ ⊥ := fun h => hc (by
    have : c ∈ Q := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at this
    exact this)
  have hcent : centralizer (Q : Set D.group) = centralizer ({c} : Set D.group) := by
    rw [hQ, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  obtain ⟨-, hfree⟩ := D.defining_characteristic_root_local_groups_component_free 2 Q hQp hQ1
    (centralizer (Q : Set D.group)) (Or.inr rfl)
  rw [hcent] at hfree
  exact hfree _ (OddToralOrdinary.isComponent_subgroupOf_of_isComponentOf hL)

end CFSG.ComponentClassification.ExcSelector
