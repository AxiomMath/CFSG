module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Pairs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS Equiv.Perm.OnCycleFactors
open scoped commutatorElement

theorem solvable_ker_toPermHom {β : Type*} [Fintype β] [DecidableEq β] (σ : Perm β)
    (hfix : Nat.card (Function.fixedPoints σ) ≤ 4) : Group.IsSolvable ↥(toPermHom σ).ker := by
  have h1 : Group.IsSolvable (Perm (Function.fixedPoints σ)) := Equiv.Perm.isSolvable hfix
  have h2 : Group.IsSolvable ((c : σ.cycleFactorsFinset) → Subgroup.zpowers c.val) := by
    refine Group.isSolvable_of_comm fun u v => funext fun c => ?_
    apply Subtype.ext
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (u c).2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (v c).2
    show ((u c : Subgroup.zpowers c.val) : Perm β) * (v c) = (v c) * (u c)
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self c.val i j).eq
  have h3 : Group.IsSolvable (Perm (Function.fixedPoints σ) ×
      ((c : σ.cycleFactorsFinset) → Subgroup.zpowers c.val)) := inferInstance
  let e := MonoidHom.ofInjective (kerParam_injective σ)
  have h4 : Group.IsSolvable ↥(kerParam σ).range :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  rw [kerParam_range_eq] at h4
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (toPermHom σ).ker (Subgroup.subtype _)
      (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.injective _)

namespace AhatData

variable {n : ℕ} {K : Type} [Group K]

theorem card_support_eq_two_of_mem_cycleFactorsFinset {β : Type*} [Fintype β] [DecidableEq β]
    {σ : Perm β} {k : ℕ} (h2 : σ * σ = 1) (hk : σ.support.card = 2 * k) {c : Perm β}
    (hc : c ∈ σ.cycleFactorsFinset) : c.support.card = 2 := by
  have hcyc := cycleType_eq_replicate_of_involution h2 hk
  have : c.support.card ∈ σ.cycleType := by
    rw [cycleType_def]
    exact Multiset.mem_map.2 ⟨c, hc, rfl⟩
  rw [hcyc] at this
  exact Multiset.eq_of_mem_replicate this

theorem card_cycleFactorsFinset_of_involution {β : Type*} [Fintype β] [DecidableEq β]
    {σ : Perm β} {k : ℕ} (h2 : σ * σ = 1) (hk : σ.support.card = 2 * k) :
    Fintype.card σ.cycleFactorsFinset = k := by
  have hcyc := cycleType_eq_replicate_of_involution h2 hk
  have h1 : σ.cycleType.card = σ.cycleFactorsFinset.card := by
    rw [cycleType_def, Multiset.card_map]
    rfl
  rw [hcyc, Multiset.card_replicate] at h1
  rw [Fintype.card_coe]
  exact h1.symm

end AhatData

end CFSG.OddStandard.Solomon75
