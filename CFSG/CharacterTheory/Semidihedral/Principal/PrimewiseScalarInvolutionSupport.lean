module

public import CFSG.GroupTheory.OddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

open scoped Pointwise

namespace CFSG.Semidihedral.Principal.PrimewiseScalar

variable {M : Type*} [Group M]

noncomputable abbrev zpowersConjAction (N : Subgroup M) {s : M}
    (hs : s ∈ Subgroup.normalizer (N : Set M)) : MulDistribMulAction (Subgroup.zpowers s) N :=
  MulDistribMulAction.compHom N (Subgroup.inclusion (Subgroup.zpowers_le.mpr hs))

theorem zpowersConjAction_smul_coe (N : Subgroup M) {s : M}
    (hs : s ∈ Subgroup.normalizer (N : Set M)) (g : Subgroup.zpowers s) (x : N) :
    letI := zpowersConjAction N hs
    ((g • x : N) : M) = (g : M) * x * (g : M)⁻¹ := rfl

theorem inv_eq_self_of_orderOf_two {s : M} (hs : orderOf s = 2) : s⁻¹ = s :=
  CFSG.OddInversion.inv_eq_self_of_orderOf_eq_two hs

theorem zpow_eq_one_or_self {s : M} (hs : orderOf s = 2) (k : ℤ) : s ^ k = 1 ∨ s ^ k = s := by
  have hs2 : s ^ 2 = 1 := by rw [← hs, pow_orderOf_eq_one]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← two_mul, zpow_mul, zpow_ofNat, hs2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hs2, one_zpow, one_mul, zpow_one]

section Action

variable {N : Subgroup M} {s : M} (hsN : s ∈ Subgroup.normalizer (N : Set M))
  (hs : orderOf s = 2)

include hs in
theorem mem_fixedPointSubgroup_iff (x : N) :
    letI := zpowersConjAction N hsN
    x ∈ fixedPointSubgroup (Subgroup.zpowers s) N ↔ s * (x : M) * s⁻¹ = x := by
  let _ := zpowersConjAction N hsN
  constructor
  · intro hx
    exact congrArg Subtype.val (hx ⟨s, Subgroup.mem_zpowers s⟩)
  · intro hx ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    apply Subtype.ext
    rw [zpowersConjAction_smul_coe]
    rcases zpow_eq_one_or_self hs k with h | h
    · simp only [h, one_mul, inv_one, mul_one]
    · simp only [h]
      exact hx

include hs in
theorem smul_mem_of_conj_mem {K : Subgroup N}
    (hK : ∀ x ∈ K, (⟨s * (x : M) * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN x).mp x.2⟩ : N) ∈ K) :
    letI := zpowersConjAction N hsN
    ∀ g : Subgroup.zpowers s, ∀ x ∈ K, g • x ∈ K := by
  let _ := zpowersConjAction N hsN
  rintro ⟨g, hg⟩ x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rcases zpow_eq_one_or_self hs k with h | h
  · have : (⟨s ^ k, hg⟩ : Subgroup.zpowers s) • x = x := by
      apply Subtype.ext
      rw [zpowersConjAction_smul_coe]
      simp only [h, one_mul, inv_one, mul_one]
    rw [this]
    exact hx
  · have : (⟨s ^ k, hg⟩ : Subgroup.zpowers s) • x =
        ⟨s * (x : M) * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsN x).mp x.2⟩ := by
      apply Subtype.ext
      rw [zpowersConjAction_smul_coe]
      simp only [h]
    rw [this]
    exact hK x hx

include hs in
theorem card_zpowers_eq_two : Nat.card (Subgroup.zpowers s) = 2 := by
  rw [Nat.card_zpowers, hs]

end Action

end CFSG.Semidihedral.Principal.PrimewiseScalar
