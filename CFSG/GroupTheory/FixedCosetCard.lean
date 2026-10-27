module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

public noncomputable section

namespace CFSG

variable {G : Type*} [Group G]

theorem fixedCoset_card_mul (H : Subgroup G) (t : G) :
    Set.ncard {x : G ⧸ H | t • x = x} * Nat.card H =
      Nat.card {g : G // g⁻¹ * t * g ∈ H} := by
  let F : Set (G ⧸ H) := {x | t • x = x}
  have hpre : QuotientGroup.mk ⁻¹' F = {g : G | g⁻¹ * t * g ∈ H} := by
    ext g
    change ((QuotientGroup.mk (t * g) : G ⧸ H) = QuotientGroup.mk g) ↔ _
    rw [eq_comm, QuotientGroup.eq]
    simp only [Set.mem_ofPred_eq, mul_assoc]
  calc
    Set.ncard F * Nat.card H = Nat.card F * Nat.card H := rfl
    _ = Nat.card (H × F) := by rw [Nat.card_prod, mul_comm]
    _ = Nat.card (QuotientGroup.mk ⁻¹' F) :=
      (Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H F)).symm
    _ = Nat.card {g : G // g⁻¹ * t * g ∈ H} := by rw [hpre]; rfl

theorem fixedCoset_card_congr {K : Type*} [Group K] [Finite G] [Finite K]
    (e : G ≃* K) (H : Subgroup G) (L : Subgroup K) (hmap : H.map e = L) (t : G) :
    Set.ncard {x : G ⧸ H | t • x = x} =
      Set.ncard {x : K ⧸ L | e t • x = x} := by
  have hmem (x : G) : x ∈ H ↔ e x ∈ L := by
    rw [← hmap]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      exact e.injective heq ▸ hy
  have hcard : Nat.card {g : G // g⁻¹ * t * g ∈ H} =
      Nat.card {g : K // g⁻¹ * e t * g ∈ L} := by
    apply Nat.card_congr
    exact e.toEquiv.subtypeEquiv fun g => by
      change (g⁻¹ * t * g ∈ H) ↔ ((e g)⁻¹ * e t * e g ∈ L)
      simpa only [map_mul, map_inv] using hmem (g⁻¹ * t * g)
  have hHcard : Nat.card H = Nat.card L := by
    rw [← hmap, Subgroup.card_map_of_injective e.injective]
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card L)
  rw [← hHcard, fixedCoset_card_mul, hHcard, fixedCoset_card_mul]
  exact hcard

end CFSG
