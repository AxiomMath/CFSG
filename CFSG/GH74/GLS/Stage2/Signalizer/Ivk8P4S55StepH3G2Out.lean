module

public import CFSG.RankThree.PartTwo.KFacts.AutG2
import CFSG.RankThree.Chevalley.OddExceptionalRealRootElement
import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.KFacts

@[expose] noncomputable def rootElt
    (K : Type) [Field K] : ↥(adjointGroup Tag.G2 K) :=
  ⟨xUnit Tag.G2 K ⟨0, by decide⟩ 1, xUnit_mem_adjointGroup _ 1⟩


variable {K : Type} [Field K]

theorem g2FieldHom_xUnit_one (σ : K ≃+* K) : g2FieldHom K σ (rootElt K) = rootElt K := by
  have hu : ((rootElt K : ↥(adjointGroup Tag.G2 K)) : ModGL Tag.G2 K) =
      xUnit Tag.G2 K ⟨0, by decide⟩ 1 := rfl
  refine Subtype.ext (Units.ext ?_)
  rw [coe_g2FieldHom, Units.coe_map, hu, coe_xUnit]
  have h := entrywise_xOp σ.toRingHom (τ := Tag.G2) ⟨0, by decide⟩ (1 : K)
  rw [map_one] at h
  exact h

theorem orderOf_rootElt {r : ℕ} [Fact r.Prime] [CharP K r] : orderOf (rootElt K) = r := by
  rw [← Subgroup.orderOf_coe]
  exact CFSG.RankThree.Chevalley.orderOf_xUnit_one (τ := Tag.G2) (K := K) (p := r) ⟨0, by decide⟩

theorem exists_rgroup_of_outer [Finite K] {r : ℕ} [Fact r.Prime] [CharP K r]
    (hK3 : ringChar K ≠ 3) (hK4 : 4 ≤ Nat.card K) {α : MulAut ↥(adjointGroup Tag.G2 K)}
    (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    ∃ E : Subgroup ↥(adjointGroup Tag.G2 K), E ≠ ⊥ ∧ IsPGroup r ↥E ∧ ∀ x ∈ E, α x ∈ E := by
  obtain ⟨σ, -, k, rfl⟩ := g2_order_three_field_descent hK3 hK4 hα hout
  set v : ↥(adjointGroup Tag.G2 K) := MulAut.conj k (rootElt K) with hvdef
  have hv : orderOf v = r := by
    rw [hvdef, MulEquiv.orderOf_eq, orderOf_rootElt]
  have hfix : (MulAut.conj k * g2FieldHom K σ * (MulAut.conj k)⁻¹) v = v := by
    rw [hvdef, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, g2FieldHom_xUnit_one]
  refine ⟨zpowers v, ?_, ?_, ?_⟩
  · intro h
    have h1 : v = 1 := by
      have : v ∈ zpowers v := mem_zpowers v
      rwa [h, mem_bot] at this
    rw [h1, orderOf_one] at hv
    exact (Fact.out : r.Prime).one_lt.ne hv
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  · intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    rw [map_zpow, hfix]
    exact zpow_mem (mem_zpowers v) n

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.StepH3G2
