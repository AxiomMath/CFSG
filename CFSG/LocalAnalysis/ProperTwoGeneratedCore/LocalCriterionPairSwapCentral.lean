module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap

universe u

variable {K : Type u} [Group K]

theorem odd_subgroup_disjoint_two_subgroup
    (P J : Subgroup K) (hP : IsPGroup 2 P) (hJodd : Odd (Nat.card J)) :
    Disjoint P J := by
  rw [Subgroup.disjoint_def]
  intro x hxP hxJ
  apply orderOf_eq_one_iff.mp
  obtain ⟨n, hn⟩ := hP.exists_orderOf_dvd_pow (⟨x, hxP⟩ : P)
  have hp : orderOf x ∣ 2 ^ n := by
    simpa only [Subgroup.orderOf_mk] using hn
  exact Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_left.mpr hJodd).pow_left n) hp
    (J.orderOf_dvd_natCard hxJ)

theorem odd_quotient_injective_on_two_subgroup
    (P J : Subgroup K) [J.Normal]
    (hP : IsPGroup 2 P) (hJodd : Odd (Nat.card J)) :
    Function.Injective ((QuotientGroup.mk' J).comp P.subtype) := by
  intro x y hxy
  have hJ : (x : K)⁻¹ * (y : K) ∈ J := QuotientGroup.eq.mp hxy
  have hPxy : (x : K)⁻¹ * (y : K) ∈ P :=
    P.mul_mem (P.inv_mem x.property) y.property
  have hone : (x : K)⁻¹ * (y : K) = 1 :=
    Subgroup.disjoint_def.mp (odd_subgroup_disjoint_two_subgroup P J hP hJodd)
      hPxy hJ
  apply Subtype.ext
  exact inv_mul_eq_one.mp hone

theorem quotient_central_in_two_subgroup
    (P J : Subgroup K) [J.Normal]
    (hP : IsPGroup 2 P) (hJodd : Odd (Nat.card J))
    (t : K) (htP : t ∈ P)
    (htcentral : QuotientGroup.mk' J t ∈ Subgroup.center (K ⧸ J)) :
    ∀ x : K, x ∈ P → Commute x t := by
  intro x hxP
  let f : P →* K ⧸ J := (QuotientGroup.mk' J).comp P.subtype
  have hinj : Function.Injective f :=
    odd_quotient_injective_on_two_subgroup P J hP hJodd
  have hquot : Commute (f (⟨x, hxP⟩ : P)) (f (⟨t, htP⟩ : P)) := by
    rw [commute_iff_eq]
    exact Subgroup.mem_center_iff.mp htcentral (QuotientGroup.mk' J x)
  have hcomm : Commute (⟨x, hxP⟩ : P) (⟨t, htP⟩ : P) :=
    Commute.of_map hinj hquot
  exact hcomm.map P.subtype

end CFSG.ProperTwoGeneratedCore.LocalCriterionPairSwap
