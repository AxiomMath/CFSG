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
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Transfer
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

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

theorem central_mem_commutator_of_perfect {Y : Type*} [Group Y] [Finite Y] [hY : Group.IsPerfect Y]
    {p : ℕ} [Fact p.Prime] (P : Subgroup Y) {z : Y} (hz : z ∈ Subgroup.center Y) (hzP : z ∈ P)
    (hzp : orderOf z = p) (hidx : ¬ p ∣ P.index) :
    (⟨z, hzP⟩ : ↥P) ∈ commutator ↥P := by
  classical
  haveI : P.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  set ϕ : ↥P →* Abelianization ↥P := Abelianization.of with hϕ
  have hker : ϕ.ker = commutator ↥P := Abelianization.ker_of ↥P
  have hkey : ∀ (k : ℕ) (g₀ : Y), g₀⁻¹ * z ^ k * g₀ ∈ P → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center Y := Subgroup.pow_mem _ hz k
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hc g₀), ← mul_assoc, inv_mul_cancel, one_mul]
  have htrans := MonoidHom.transfer_eq_pow ϕ z hkey
  have hone : ϕ.transfer z = 1 := by
    have hperf : commutator Y = ⊤ := hY.commutator_eq_top
    have hz' : z ∈ commutator Y := by rw [hperf]; trivial
    have hle : commutator Y ≤ (ϕ.transfer).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    exact hle hz'
  rw [hone] at htrans
  have hmem : (⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ : ↥P) ∈ commutator ↥P := by
    rw [← hker, MonoidHom.mem_ker]; exact htrans.symm
  have hcop : Nat.Coprime P.index p := (Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hidx |>.symm
  obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Fact.out : p.Prime).one_lt
  have hzm : (z ^ P.index) ^ m = z := by
    rw [← pow_mul]
    have : z ^ (P.index * m) = z ^ (P.index * m % p) := by
      conv_lhs => rw [← Nat.div_add_mod (P.index * m) p, pow_add, pow_mul, ← hzp,
        pow_orderOf_eq_one, one_pow, one_mul]
      rw [hzp]
    rw [this, hm.2, pow_one]
  have : (⟨z, hzP⟩ : ↥P) = (⟨z ^ P.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ : ↥P) ^ m := by
    apply Subtype.ext
    simpa using hzm.symm
  rw [this]
  exact Subgroup.pow_mem _ hmem m

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
