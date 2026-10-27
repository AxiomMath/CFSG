module

public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.PointChainCard
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
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.KS.PC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.Perm.Native CFSG.Sporadic.Th.Native
  CFSG.KS.PCC

variable {n NL m : Nat} {letters : Array Table} {base Q qb : Array Nat} {L : Nat → Nat → Nat}
  {B : Nat → Nat} {QL : List Nat} {QB CNT : Nat → Nat} {PTS POS PAR LAB TI : Nat → Nat → Nat}

theorem sig_mem_Gs (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {i l : Nat} (hi : i ≤ m) (hl : l ∈ lvK L B NL i) :
    sig n letters l ∈ Gs (grp n NL letters) (bF hn B) i := by
  obtain ⟨hl', hfix⟩ := mem_lvK.1 hl
  rw [mem_Gs]
  refine ⟨sig_mem ⟨l, hl'⟩, fun k hk => Fin.ext ?_⟩
  rw [sig_val H hl', bF_val H hn (by omega), hfix k hk]

theorem tw_mem (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {i : Nat} (hi : i < m) : ∀ k < CNT i,
      twL n letters PAR LAB i k ∈ Gs (grp n NL letters) (bF hn B) i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [twL, tw_eq]
    by_cases hc : 0 < k ∧ r32 (PAR i) k < k
    · rw [ite_eq_left hc]
      exact Subgroup.mul_mem _ (sig_mem_Gs H hn hi.le (lab_mem H hi hk hc.1)) (ih _ hc.2 (by omega))
    · rw [ite_eq_right hc]
      exact Subgroup.one_mem _

theorem dSet_sub_orbit (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) {l : Nat} (hl : l < m) :
    (↑(dSet hn CNT PTS l) : Set (Fin n)) ⊆
      MulAction.orbit (Gs (grp n NL letters) (bF hn B) l) (bF hn B l) := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
  rw [Finset.mem_range] at hk
  refine mem_orbit_Gs.2 ⟨_, tw_mem H hn hl k hk, Fin.ext ?_⟩
  rw [← actN_fin, bF_val H hn hl, tw_pt H hl k hk]
  exact (Nat.mod_eq_of_lt ((rep_of H hl).pt k hk).lt).symm

theorem card_ge (H : ChainHyp n NL m letters base Q qb L B QL QB CNT PTS POS PAR LAB TI)
    (hn : 0 < n) : ((List.range m).map CNT).prod ≤ Nat.card (grp n NL letters) := by
  rw [card_chain (grp n NL letters) (bF hn B) m, prod_range_map]
  refine le_trans ?_ (Nat.le_mul_of_pos_right _ Nat.card_pos)
  refine Finset.prod_le_prod' fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [← dSet_card H hn hl', ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard (dSet_sub_orbit H hn hl') (Set.toFinite _)

end CFSG.KS.PC

end
