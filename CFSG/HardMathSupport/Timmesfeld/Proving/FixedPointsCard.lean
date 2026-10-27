module

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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.HardMathSupport.Timmesfeld.Proving

variable {V : Type*} [CommGroup V]

def coboundary (σ : V →* V) : V →* V :=
  MonoidHom.mk' (fun v => v⁻¹ * σ v) (fun a b => by
    simp only [map_mul, mul_inv]
    ac_rfl)

theorem coboundary_apply (σ : V →* V) (v : V) : coboundary σ v = v⁻¹ * σ v := by
  simp only [coboundary, MonoidHom.mk'_apply]

theorem card_fixed_le [Finite V] {p : ℕ} (hp : p.Prime) (hexp : ∀ v : V, v ^ p = 1)
    (σ : V →* V) (z : V) (hgen : ∀ v : V, v ∈ Subgroup.closure ({z, σ z, σ (σ z)} : Set V)) :
    Nat.card {v : V // σ v = v} ≤ p := by
  set δ := coboundary σ with hδ
  set R := δ.range with hR
  have hker : Nat.card {v : V // σ v = v} = Nat.card δ.ker := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [MonoidHom.mem_ker, hδ, coboundary_apply, inv_mul_eq_one, eq_comm]
  have hpos : 0 < Nat.card R := Nat.card_pos
  have hsplit : Nat.card δ.ker * Nat.card R = Nat.card V := Subgroup.card_ker_mul_card_range δ
  have hidx : R.index * Nat.card R = Nat.card V := Subgroup.index_mul_card R
  have hker_eq : Nat.card δ.ker = R.index := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hsplit, hidx]
  have hσz : σ z = z * δ z := by
    rw [hδ, coboundary_apply, mul_inv_cancel_left]
  have hK : ∀ v : V, v ∈ Subgroup.zpowers z ⊔ R := by
    have hle : Subgroup.closure ({z, σ z, σ (σ z)} : Set V) ≤ Subgroup.zpowers z ⊔ R := by
      rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · rw [hσz]
        exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩))
      · have hσσ : σ (σ z) = σ z * δ (σ z) := by
          rw [hδ, coboundary_apply, mul_inv_cancel_left]
        have hσz' : σ z ∈ Subgroup.zpowers z ⊔ R := by
          rw [hσz]
          exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
            (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨z, rfl⟩))
        rw [hσσ]
        exact mul_mem hσz' (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨σ z, rfl⟩))
    intro v
    exact hle (hgen v)
  have hz1 : z ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]
    exact hexp z
  have hzk : ∀ k : ℤ, z ^ k = z ^ (k % (p : ℤ)) := by
    intro k
    conv_lhs => rw [← Int.emod_add_mul_ediv k p]
    rw [zpow_add, zpow_mul, hz1, one_zpow, mul_one]
  have hsurj : Function.Surjective
      (fun i : Fin p => (QuotientGroup.mk (z ^ (i : ℕ)) : V ⧸ R)) := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, w, hw, hyw⟩ := Subgroup.mem_sup.mp (hK v)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hnn : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne_zero)
    have hlt : k % (p : ℤ) < (p : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hp.pos)
    refine ⟨⟨(k % (p : ℤ)).toNat, by omega⟩, ?_⟩
    have hpow : z ^ (k % (p : ℤ)).toNat = z ^ k := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnn, hzk k]
    show (QuotientGroup.mk (z ^ (k % (p : ℤ)).toNat) : V ⧸ R) = QuotientGroup.mk v
    rw [QuotientGroup.eq, ← hyw, hpow, inv_mul_cancel_left]
    exact hw
  have hcard : Nat.card (V ⧸ R) ≤ p := by
    have := Nat.card_le_card_of_surjective _ hsurj
    simpa using this
  rw [hker, hker_eq]
  exact hcard

end CFSG.HardMathSupport.Timmesfeld.Proving

end
