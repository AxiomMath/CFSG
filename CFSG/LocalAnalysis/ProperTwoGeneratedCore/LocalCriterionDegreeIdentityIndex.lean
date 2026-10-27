module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

universe u

variable {G : Type u} [Group G] [Finite G]

theorem relative_index_ratio
    (C A B D : Subgroup G) (hCA : C ≤ A) (hCB : C ≤ B)
    (hAD : A ≤ D) (hBD : B ≤ D) :
    (B.relIndex D : ℚ) / A.relIndex D =
      (C.relIndex A : ℚ) / C.relIndex B := by
  have hA := Subgroup.relIndex_mul_relIndex C A D hCA hAD
  have hB := Subgroup.relIndex_mul_relIndex C B D hCB hBD
  have hAQ : (C.relIndex A : ℚ) * A.relIndex D = C.relIndex D := by
    exact_mod_cast hA
  have hBQ : (C.relIndex B : ℚ) * B.relIndex D = C.relIndex D := by
    exact_mod_cast hB
  have hADQ : (A.relIndex D : ℚ) ≠ 0 := by
    have h0 : A.relIndex D ≠ 0 := by
      change (A.subgroupOf D).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    exact_mod_cast h0
  have hCBQ : (C.relIndex B : ℚ) ≠ 0 := by
    have h0 : C.relIndex B ≠ 0 := by
      change (C.subgroupOf B).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    exact_mod_cast h0
  apply (div_eq_div_iff hADQ hCBQ).mpr
  nlinarith [hAQ, hBQ]

omit [Finite G] in
theorem generated_centralizer_le_elements (D : Subgroup G) (u t : G) :
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    D ⊓ Subgroup.centralizer (V : Set G) ≤
        D ⊓ Subgroup.centralizer ({u} : Set G) ∧
      D ⊓ Subgroup.centralizer (V : Set G) ≤
        D ⊓ Subgroup.centralizer ({u * t} : Set G) := by
  let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  have huV : u ∈ V := (show Subgroup.zpowers u ≤ V from le_sup_left)
    (Subgroup.mem_zpowers u)
  have htV : t ∈ V := (show Subgroup.zpowers t ≤ V from le_sup_right)
    (Subgroup.mem_zpowers t)
  constructor
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huV)) hx.2
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (V.mul_mem huV htV))) hx.2

theorem generated_centralizer_index_ratio (D : Subgroup G) (u t : G) :
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    let C := D ⊓ Subgroup.centralizer (V : Set G)
    let A := D ⊓ Subgroup.centralizer ({u} : Set G)
    let B := D ⊓ Subgroup.centralizer ({u * t} : Set G)
    ((Subgroup.centralizer ({u * t} : Set G)).relIndex D : ℚ) /
        (Subgroup.centralizer ({u} : Set G)).relIndex D =
      (C.relIndex A : ℚ) / C.relIndex B := by
  let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  let C := D ⊓ Subgroup.centralizer (V : Set G)
  let A := D ⊓ Subgroup.centralizer ({u} : Set G)
  let B := D ⊓ Subgroup.centralizer ({u * t} : Set G)
  have hle := generated_centralizer_le_elements D u t
  have hA : (Subgroup.centralizer ({u} : Set G)).subgroupOf D = A.subgroupOf D := by
    ext x
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
  have hB : (Subgroup.centralizer ({u * t} : Set G)).subgroupOf D = B.subgroupOf D := by
    ext x
    exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩
  change (((Subgroup.centralizer ({u * t} : Set G)).subgroupOf D).index : ℚ) /
      ((Subgroup.centralizer ({u} : Set G)).subgroupOf D).index = _
  rw [hA, hB]
  exact relative_index_ratio C A B D hle.1 hle.2 inf_le_left inf_le_left

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
