module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.ProperTwoGeneratedCore

open CFSG.BenderSuzuki.PFAppendixIII

variable {P : Type*} [Group P] [Finite P]

theorem normal_two_subgroup_contains_central_involution
    (hP : IsPGroup 2 P) (N : Subgroup P) [N.Normal] (hN : N ≠ ⊥) :
    ∃ v : P, v ∈ N ∧ v ∈ Subgroup.center P ∧ orderOf v = 2 := by
  let : Group.IsNilpotent P := hP.isNilpotent
  let I := N ⊓ Subgroup.center P
  have hI : I ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN
  have hIp : IsPGroup 2 I := hP.to_subgroup I
  have hInontrivial : Nontrivial I := (Subgroup.nontrivial_iff_ne_bot I).mpr hI
  obtain ⟨n, hn, hcard⟩ := hIp.nontrivial_iff_card.mp hInontrivial
  have htwo : 2 ∣ Nat.card I := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := I) 2 htwo
  exact ⟨v, v.property.1, v.property.2, (Subgroup.orderOf_coe v).trans hv⟩

end CFSG.ProperTwoGeneratedCore
