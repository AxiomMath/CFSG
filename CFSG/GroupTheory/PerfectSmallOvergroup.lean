module

public import Mathlib.GroupTheory.IsPerfect

public noncomputable section

namespace CFSG

universe u v w

theorem perfect_subgroup_eq_commutator_of_card_le_twice
    {A : Type u} [Group A] [Finite A] (H : Subgroup A) [Group.IsPerfect H]
    (hcard : Nat.card A ≤ 2 * Nat.card H) : H = commutator A := by
  have hmul := H.index_mul_card
  have hpositive : 0 < Nat.card H := Nat.card_pos
  have hindex : H.index = 1 ∨ H.index = 2 := by
    have hne : H.index ≠ 0 := H.index_ne_zero_of_finite
    have hle : H.index ≤ 2 := by nlinarith
    omega
  have hderived : H ≤ commutator A := by
    rw [← Subgroup.commutator_eq_self (H := H), commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  apply le_antisymm hderived
  rcases hindex with hindex | hindex
  · rw [Subgroup.index_eq_one.mp hindex]
    exact le_top
  · let : H.Normal := Subgroup.normal_of_index_eq_two hindex
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hquotient : Nat.card (A ⧸ H) = 2 := H.index_eq_card.symm.trans hindex
    let : IsCyclic (A ⧸ H) := isCyclic_of_prime_card hquotient
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

theorem perfect_embedding_range_eq_commutator_of_card_le_twice
    {A : Type u} {M : Type v} [Group A] [Finite A]
    [Group M] [Finite M] [Group.IsPerfect M]
    (rho : M →* A) (hrho : Function.Injective rho)
    (hcard : Nat.card A ≤ 2 * Nat.card M) : rho.range = commutator A := by
  let : Group.IsPerfect rho.range := Group.IsPerfect.range rho
  apply perfect_subgroup_eq_commutator_of_card_le_twice rho.range
  simpa only [Nat.card_congr (MonoidHom.ofInjective hrho).toEquiv] using hcard

theorem perfect_equal_order_embeddings_in_small_common_overgroup
    {A : Type u} {M : Type v} {N : Type w}
    [Group A] [Finite A] [Group M] [Finite M] [Group.IsPerfect M]
    [Group N] [Finite N] [Group.IsPerfect N]
    (m : ℕ) (_hm : 1 ≤ m) (hM : Nat.card M = m) (hN : Nat.card N = m)
    (rho : M →* A) (sigma : N →* A)
    (hrho : Function.Injective rho) (hsigma : Function.Injective sigma)
    (hA : Nat.card A ≤ 2 * m) :
    rho.range = commutator A ∧ sigma.range = commutator A ∧
      ∃! f : M ≃* N, sigma.comp f.toMonoidHom = rho := by
  have hR : rho.range = commutator A :=
    perfect_embedding_range_eq_commutator_of_card_le_twice rho hrho (by omega)
  have hS : sigma.range = commutator A :=
    perfect_embedding_range_eq_commutator_of_card_le_twice sigma hsigma (by omega)
  let f : M ≃* N := (MonoidHom.ofInjective hrho).trans
    ((MulEquiv.subgroupCongr (hR.trans hS.symm)).trans (MonoidHom.ofInjective hsigma).symm)
  have hf : sigma.comp f.toMonoidHom = rho := by
    ext member
    change sigma ((MonoidHom.ofInjective hsigma).symm
      ((MulEquiv.subgroupCongr (hR.trans hS.symm)) (MonoidHom.ofInjective hrho member))) =
        rho member
    rw [MonoidHom.apply_ofInjective_symm]
    exact MonoidHom.ofInjective_apply hrho
  refine ⟨hR, hS, f, hf, ?_⟩
  intro g hg
  apply MulEquiv.ext
  intro member
  apply hsigma
  have hgmember := DFunLike.congr_fun hg member
  have hfmember := DFunLike.congr_fun hf member
  exact hgmember.trans hfmember.symm

end CFSG
