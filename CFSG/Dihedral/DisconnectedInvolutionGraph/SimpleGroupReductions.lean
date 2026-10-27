module

public import CFSG.Mathlib.GroupTheory.Basic
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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [IsSimpleGroup G]

theorem simple_nonabelian_perfect (hnonab : ∃ first second : G, first * second ≠ second * first) :
    Group.IsPerfect G := by
  constructor
  rcases CFSG.eq_bot_or_eq_top_of_normal (commutator G) inferInstance with
    hbot | htop
  · have _ : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbot
    obtain ⟨first, second, hne⟩ := hnonab
    exact (hne (mul_comm' first second)).elim
  · exact htop

theorem simple_nonabelian_center_eq_bot
    (hnonab : ∃ first second : G, first * second ≠ second * first) :
    Subgroup.center G = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with
    hbot | htop
  · exact hbot
  · obtain ⟨first, second, hne⟩ := hnonab
    have hmem : second ∈ Subgroup.center G := by rw [htop]; trivial
    exact (hne (Subgroup.mem_center_iff.mp hmem first)).elim

theorem simple_odd_normal_subgroup_eq_bot (heven : Even (Nat.card G))
    (subgroup : Subgroup G) (hnormal : subgroup.Normal) (hodd : Odd (Nat.card subgroup)) :
    subgroup = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal subgroup hnormal with hbot | htop
  · exact hbot
  · rw [htop, Subgroup.card_top] at hodd
    exact ((Nat.not_even_iff_odd.mpr hodd) heven).elim

theorem simple_even_sylow_two_not_cyclic [Finite G]
    (hnonab : ∃ first second : G, first * second ≠ second * first)
    (heven : Even (Nat.card G)) (sylow : Sylow 2 G) :
    ¬ IsCyclic (sylow : Subgroup G) := by
  intro hcyclic
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmin : (Nat.card G).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr
    (even_iff_two_dvd.mp heven)
  let transfer := MonoidHom.transferSylow sylow (hcyclic.normalizer_le_centralizer hmin)
  have hcomplement : transfer.ker.IsComplement' (sylow : Subgroup G) :=
    hcyclic.isComplement' hmin
  rcases CFSG.eq_bot_or_eq_top_of_normal transfer.ker inferInstance with hbot | htop
  · have hsylowTop : (sylow : Subgroup G) = ⊤ := by
      have hsup := hcomplement.sup_eq_top
      rw [hbot, bot_sup_eq] at hsup
      exact hsup
    have _ : IsCyclic (sylow : Subgroup G) := hcyclic
    obtain ⟨first, second, hne⟩ := hnonab
    have hfirst : first ∈ (sylow : Subgroup G) := by rw [hsylowTop]; trivial
    have hsecond : second ∈ (sylow : Subgroup G) := by rw [hsylowTop]; trivial
    have hcomm := mul_comm' (⟨first, hfirst⟩ : (sylow : Subgroup G))
      (⟨second, hsecond⟩ : (sylow : Subgroup G))
    exact hne (congrArg (fun element : (sylow : Subgroup G) => (element : G)) hcomm)
  · have hsylowBot : (sylow : Subgroup G) = ⊥ := by
      rw [htop] at hcomplement
      exact Subgroup.isComplement'_top_left.mp hcomplement
    exact sylow.ne_bot_of_dvd_card (even_iff_two_dvd.mp heven) hsylowBot

end CFSG.DisconnectedInvolutionGraph.Helpers
