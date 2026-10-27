module

public import CFSG.Open.GLADefs
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def k631Triv (O J : Subgroup G) : Subgroup G where
  carrier := {q | q ∈ normalizer (O : Set G) ∧ q ∈ normalizer (J : Set G) ∧
    ∀ j ∈ J, ⁅q, j⁆ ∈ O}
  one_mem' := ⟨one_mem _, one_mem _, fun j _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haO, haJ, ha⟩ ⟨hbO, hbJ, hb⟩
    refine ⟨mul_mem haO hbO, mul_mem haJ hbJ, fun j hj => ?_⟩
    have e : ⁅a * b, j⁆ = a * ⁅b, j⁆ * a⁻¹ * ⁅a, j⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact O.mul_mem ((mem_normalizer_iff.mp haO _).mp (hb j hj)) (ha j hj)
  inv_mem' := by
    rintro a ⟨haO, haJ, ha⟩
    refine ⟨inv_mem haO, inv_mem haJ, fun j hj => ?_⟩
    have e : ⁅a⁻¹, j⁆ = a⁻¹ * ⁅a, j⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : ⁅a, j⁆⁻¹ ∈ O := O.inv_mem (ha j hj)
    simpa [mul_assoc] using (mem_normalizer_iff.mp (inv_mem haO) _).mp h1

variable [Finite G]

structure LayerHyp (f : ℕ) (X Q : Subgroup G) : Prop where
  prime : f.Prime
  ne_two : f ≠ 2
  kgroup : IsKGroup ↥X
  le : Q ≤ X
  pgroup : IsPGroup f Q
  sylow : ¬ f ∣ (Q.subgroupOf X).index
  comm : IsMulCommutative Q
  odd : Odd (Nat.card ↥(GLAPPrimeCoreOf f X))

end CFSG.LocalAnalysis.RankThreeTheoremC
