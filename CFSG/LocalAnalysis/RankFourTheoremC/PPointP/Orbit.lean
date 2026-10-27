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

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open Subgroup

theorem not_dvd_card_orbit_of_sylow_le_stabilizer {N X : Type*} [Group N] [Finite N]
    [MulAction N X] {r : ℕ} [hr : Fact r.Prime] (S : Sylow r N) (x₀ : X)
    (hS : (S : Subgroup N) ≤ MulAction.stabilizer N x₀) :
    ¬ r ∣ Nat.card (MulAction.orbit N x₀) := by
  intro hdvd
  have hidx : (MulAction.stabilizer N x₀).index = Nat.card (MulAction.orbit N x₀) :=
    MulAction.index_stabilizer N x₀
  have hmul := (MulAction.stabilizer N x₀).index_mul_card
  have hSdvd : Nat.card S ∣ Nat.card (MulAction.stabilizer N x₀) :=
    Subgroup.card_dvd_of_le hS
  obtain ⟨v, hv⟩ : ∃ v, v = (Nat.card N).factorization r := ⟨_, rfl⟩
  rw [Sylow.card_eq_multiplicity, ← hv] at hSdvd
  have hN : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have h1 : r ^ (v + 1) ∣ Nat.card N := by
    rw [← hmul, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul (hidx ▸ hdvd) hSdvd
  have h2 := (hr.out.pow_dvd_iff_le_factorization hN).mp h1
  omega

variable {G : Type*} [Group G]

@[expose, instance_reducible] def conjAct (N : Subgroup G) : MulAction N (Subgroup G) where
  smul m L := L.map (MulAut.conj (m : G)).toMonoidHom
  one_smul L := by
    have : (MulAut.conj ((1 : N) : G)).toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    change L.map (MulAut.conj ((1 : N) : G)).toMonoidHom = L
    rw [this, Subgroup.map_id]
  mul_smul a b L := by
    change L.map (MulAut.conj (((a * b : N)) : G)).toMonoidHom =
      (L.map (MulAut.conj (b : G)).toMonoidHom).map (MulAut.conj (a : G)).toMonoidHom
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp [mul_assoc]

variable [Finite G]

theorem not_dvd_card_of_centralizes {W : Subgroup G} {x : G} (hxW : x ∈ W) {r : ℕ}
    [hr : Fact r.Prime] (𝒟 : Set (Subgroup G))
    (hx : zpowers x ∈ 𝒟)
    (hclosed : ∀ m ∈ normalizer (W : Set G), ∀ L ∈ 𝒟,
      L.map (MulAut.conj m).toMonoidHom ∈ 𝒟)
    (htrans : ∀ L ∈ 𝒟, ∃ m ∈ normalizer (W : Set G),
      L = (zpowers x).map (MulAut.conj m).toMonoidHom)
    (hcent : ∀ m ∈ normalizer (W : Set G), IsPGroup r (zpowers m) → ∀ w ∈ W, m * w = w * m) :
    ¬ r ∣ Nat.card 𝒟 := by
  classical
  let _inst : MulAction (normalizer (W : Set G)) (Subgroup G) := conjAct (normalizer (W : Set G))
  have horb : MulAction.orbit (normalizer (W : Set G)) (zpowers x) = 𝒟 := by
    ext L
    constructor
    · rintro ⟨m, rfl⟩
      exact hclosed m m.2 _ hx
    · intro hL
      obtain ⟨m, hm, rfl⟩ := htrans L hL
      exact ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow r (normalizer (W : Set G))))
  have hSstab : (S : Subgroup (normalizer (W : Set G))) ≤
      MulAction.stabilizer (normalizer (W : Set G)) (zpowers x) := by
    intro m hm
    rw [MulAction.mem_stabilizer_iff]
    change (zpowers x).map (MulAut.conj (m : G)).toMonoidHom = zpowers x
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp S.isPGroup' ⟨m, hm⟩
    have hk' : orderOf (m : G) = r ^ k := by
      have h1 : orderOf m = orderOf (⟨m, hm⟩ : S) := Subgroup.orderOf_coe (⟨m, hm⟩ : S)
      rw [Subgroup.orderOf_coe, h1]
      exact hk
    have hpg : IsPGroup r (zpowers (m : G)) := IsPGroup.of_card (n := k) (by
      rw [Nat.card_zpowers, hk'])
    have hc := hcent m m.2 hpg x hxW
    rw [MonoidHom.map_zpowers]
    congr 1
    change (m : G) * x * (m : G)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hc
  have := not_dvd_card_orbit_of_sylow_le_stabilizer S (zpowers x) hSstab
  rwa [horb] at this

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
