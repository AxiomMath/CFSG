module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Step3
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.EvenSporadicStandard.J4Std.YExists

open Subgroup

variable {G : Type} [Group G] {L U T0 : Subgroup G} {z : G}

theorem sq_mem_U (hS : Setting L z) (hD : LocalData L U T0)
    (htrans : ∀ u ∈ U, ∃ n ∈ Nsub U z, n * z * n⁻¹ = z * u) {w : G} (hw : w ∈ Csub U z) :
    w * w ∈ U := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  have hww : w * w ∈ Csub U z := mul_mem hw hw
  have hphi : phiVal z (w * w) = 1 := by
    rw [phiVal_mul hS hD hw hw]
    exact hD.U_sq _ (phiVal_mem hS hD (mem_Csub.1 hw).1)
  obtain ⟨u, hu, hcase⟩ := (mem_Vsub_iff hS hUL).1
    (Csub_comm_mem_V hS hD hww ((phiVal_eq_one_iff hS).1 hphi))
  rcases hcase with h | h
  · rw [h]; exact hu
  · exfalso
    obtain ⟨n, -, hn⟩ := htrans u hu
    exact hS.not_isConj_of_sq ⟨w, rfl⟩ (isConj_iff.2 ⟨n, by rw [hn, h]⟩)

theorem V_le_centralizer (hS : Setting L z) (hUL : U ≤ L) :
    Vsub U z ≤ centralizer ({z} : Set G) := by
  refine sup_le (fun u hu => ?_) ?_
  · exact mem_centralizer_singleton_iff.2 (z_comm_U hS hUL hu).symm
  · rw [zpowers_le]
    exact mem_centralizer_singleton_iff.2 rfl

theorem ker_phiHom (hS : Setting L z) (hD : LocalData L U T0) :
    (phiHom hS hD).ker = (Vsub U z).subgroupOf (Csub U z) := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  ext ⟨c, hc⟩
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    exact Csub_comm_mem_V hS hD hc ((phiVal_eq_one_iff hS).1 h)
  · intro hv
    exact (phiVal_eq_one_iff hS).2
      (mem_centralizer_singleton_iff.1 (V_le_centralizer hS hUL hv)).symm

theorem exists_phi_eq [Finite G] (hS : Setting L z) (hD : LocalData L U T0)
    (hcard : Nat.card (Csub U z) = 2 ^ 23) : ∀ u ∈ U, ∃ w ∈ Csub U z, phiVal z w = u := by
  have hUL : U ≤ L := hD.U_le_T0.trans hD.T0_le_L
  let φ := phiHom hS hD
  have hrange : φ.range ≤ U := by
    rintro _ ⟨c, rfl⟩
    exact phiVal_mem hS hD (mem_Csub.1 c.2).1
  have hker : Nat.card φ.ker = 2 ^ 12 := by
    rw [ker_phiHom hS hD, Nat.card_congr (subgroupOfEquivOfLe (V_le_Csub hS hD)).toEquiv,
      card_Vsub hS hUL, hD.card_U]
    norm_num
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hker, hcard] at hmul
  have hr : Nat.card φ.range = Nat.card U := by
    rw [hD.card_U]
    omega
  have heq : φ.range = U := Subgroup.eq_of_le_of_card_ge hrange hr.ge
  intro u hu
  have hu' : u ∈ φ.range := by rw [heq]; exact hu
  obtain ⟨⟨w, hw⟩, hwu⟩ := hu'
  exact ⟨w, hw, hwu⟩

end CFSG.EvenSporadicStandard.J4Std.YExists
