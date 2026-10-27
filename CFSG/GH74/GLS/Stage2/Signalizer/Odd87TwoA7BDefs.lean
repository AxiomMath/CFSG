module

public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG CFSG.ComponentClassification Subgroup

@[expose] def BTwo (X : Type) [Group X] (z : X) : Prop :=
  ∀ S : Subgroup ↥(FixedCommutingProduct.fixedSubgroup (MulAut.conj z)),
    CFSG.IsPComponent 2 S → CFSG.IsQuasisimple ↥S

theorem fixedSubgroup_conj_eq_centralizer_gen {X : Type*} [Group X] (z : X) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj z) = Subgroup.centralizer {z} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff]
  change MulAut.conj z x = x ↔ x * z = z * x
  rw [MulAut.conj_apply]
  constructor
  · intro h
    calc x * z = (z * x * z⁻¹) * z := by rw [h]
      _ = z * x := by group
  · intro h
    calc z * x * z⁻¹ = (x * z) * z⁻¹ := by rw [h]
      _ = x := by group

theorem orderOf_conj_eq_two {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) {z : X}
    (hz : orderOf z = 2) : orderOf (MulAut.conj z : MulAut X) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have h1 := pow_orderOf_eq_one z
    rw [hz] at h1
    rw [h1, map_one]
  · intro h
    have hz1 : z ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hz
      omega
    apply hz1
    have hzc : z ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun a : MulAut X => a g) h
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * z = (z * g * z⁻¹) * z := by rw [this]
        _ = z * g := by group
    rw [hZ] at hzc
    exact Subgroup.mem_bot.mp hzc

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
