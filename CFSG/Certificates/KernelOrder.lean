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

namespace CFSG.Certificates

open Subgroup

theorem twelve_le_card_ker {F : Type*} [Group F] [Finite F] {G : Type*} [Group G]
    (θ : F →* G) (ε : F →* Multiplicative (ZMod 2)) {g₁ g₂ : F}
    (h₁ : θ g₁ = 1) (h₂ : θ g₂ = 1) (hε₁ : ε g₁ ≠ 1) (hε₂ : ε g₂ = 1)
    (h6 : 6 ∣ orderOf g₁) (h2 : 2 ∣ orderOf g₂) : 12 ≤ Nat.card θ.ker := by
  set T : Subgroup F := θ.ker with hT
  have hg₁T : g₁ ∈ T := h₁
  have hg₂T : g₂ ∈ T := h₂
  set K : T →* Multiplicative (ZMod 2) := ε.comp T.subtype with hK
  set M : Subgroup T := K.ker with hM
  have hrange : K.range = ⊤ := by
    have hcard : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]; decide
    have : Fact (Nat.card (Multiplicative (ZMod 2))).Prime :=
      ⟨by rw [hcard]; exact Nat.prime_two⟩
    rcases K.range.eq_bot_or_eq_top_of_prime_card with hb | ht
    · exfalso
      apply hε₁
      have : K ⟨g₁, hg₁T⟩ ∈ K.range := ⟨_, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact this
    · exact ht
  have hidx : M.index = 2 := by
    rw [hM, Subgroup.index_ker, hrange, Subgroup.card_top]
    rw [Nat.card_eq_fintype_card]; decide
  have hTcard : Nat.card M * 2 = Nat.card T := by
    have := M.card_mul_index
    rwa [hidx] at this
  have hsq : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  have hu₁ : (⟨g₁ ^ 2, T.pow_mem hg₁T 2⟩ : T) ∈ M := by
    rw [hM, MonoidHom.mem_ker]
    show ε (g₁ ^ 2) = 1
    rw [map_pow]; exact hsq _
  have hu₂ : (⟨g₂, hg₂T⟩ : T) ∈ M := by
    rw [hM, MonoidHom.mem_ker]
    exact hε₂
  have hdvd₁ : orderOf (g₁ ^ 2) ∣ Nat.card M := by
    have := orderOf_dvd_natCard (⟨_, hu₁⟩ : M)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
  have hdvd₂ : orderOf g₂ ∣ Nat.card M := by
    have := orderOf_dvd_natCard (⟨_, hu₂⟩ : M)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at this
  have h3 : 3 ∣ orderOf (g₁ ^ 2) := by
    obtain ⟨k, hk⟩ := h6
    rw [orderOf_pow' _ (by norm_num : 2 ≠ 0), hk]
    have : Nat.gcd (6 * k) 2 = 2 := by
      rw [Nat.gcd_comm]; exact Nat.gcd_eq_left (by omega)
    rw [this, show 6 * k / 2 = 3 * k by omega]
    exact Dvd.intro k rfl
  have h6M : 6 ∣ Nat.card M := by
    have h3M : 3 ∣ Nat.card M := h3.trans hdvd₁
    have h2M : 2 ∣ Nat.card M := h2.trans hdvd₂
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3M h2M
  have hpos : 0 < Nat.card M := Nat.card_pos
  have : 6 ≤ Nat.card M := Nat.le_of_dvd hpos h6M
  omega

theorem mul_card_le_of_surjective {F : Type*} [Group F] [Finite F] {G : Type*} [Group G]
    (θ : F →* G) (hθ : Function.Surjective θ) {q : ℕ} (hq : q ≤ Nat.card θ.ker) :
    q * Nat.card G ≤ Nat.card F := by
  have h1 := θ.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective θ hθ, Subgroup.card_top] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hq

end CFSG.Certificates
