module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open Subgroup

@[expose] def CenterIs {G : Type*} [Group G] (S : Subgroup G) (z : G) : Prop :=
  ∀ x : G, (x ∈ S ∧ ∀ s ∈ S, s * x = x * s) ↔ x ∈ Subgroup.zpowers z

theorem centerIs_iff {G : Type*} [Group G] (S : Subgroup G) (z : G) :
    (Subgroup.center ↥S).map S.subtype = Subgroup.zpowers z ↔ CenterIs S z := by
  have key : ∀ x : G, x ∈ (Subgroup.center ↥S).map S.subtype ↔
      (x ∈ S ∧ ∀ s ∈ S, s * x = x * s) := by
    intro x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun s hs => ?_⟩
      have := Subgroup.mem_center_iff.1 hy ⟨s, hs⟩
      exact congrArg Subtype.val this
    · rintro ⟨hx, hc⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g.1 g.2)
  constructor
  · intro h x
    rw [← key, h]
  · intro h
    ext x
    rw [key, h]

theorem CenterIs.map_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {S : Subgroup G} {z : G}
    (h : CenterIs S z) : CenterIs (S.map e.toMonoidHom) (e z) := by
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  constructor
  · rintro ⟨hx, hc⟩
    have hxS : x ∈ S := by
      obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.1 hx
      have : x' = x := e.injective hxx'
      exact this ▸ hx'
    have hxc : ∀ s ∈ S, s * x = x * s := by
      intro s hs
      apply e.injective
      rw [map_mul, map_mul]
      exact hc (e s) ⟨s, hs, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ((h x).1 ⟨hxS, hxc⟩)
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← hn, map_zpow]⟩
  · intro hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hx' : x ∈ Subgroup.zpowers z :=
      Subgroup.mem_zpowers_iff.2 ⟨n, e.injective (by rw [map_zpow, hn])⟩
    obtain ⟨hxS, hxc⟩ := (h x).2 hx'
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    show e s * e x = e x * e s
    rw [← map_mul, ← map_mul, hxc s hs]

noncomputable def sylowMap {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (S : Sylow 2 G) : Sylow 2 H := by
  refine Sylow.ofCard ((S : Subgroup G).map e.toMonoidHom) ?_
  rw [Subgroup.card_map_of_injective e.injective, Sylow.card_eq_multiplicity,
    Nat.card_congr e.toEquiv]

theorem coe_sylowMap {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (S : Sylow 2 G) : (sylowMap e S : Subgroup H) = (S : Subgroup G).map e.toMonoidHom := by
  unfold sylowMap
  exact Sylow.coe_ofCard _ _

theorem sylow_center_transport {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (S₁ : Sylow 2 H) (z₁ : H) (hz : orderOf z₁ = 2) (h : CenterIs (S₁ : Subgroup H) z₁) :
    ∀ S : Sylow 2 G, ∃ z : G, orderOf z = 2 ∧
      (Subgroup.center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = Subgroup.zpowers z := by
  intro S
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₁ (sylowMap e S)
  have hcoe : ((g • S₁ : Sylow 2 H) : Subgroup H) =
      (S₁ : Subgroup H).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have h1 : CenterIs ((sylowMap e S : Sylow 2 H) : Subgroup H) ((MulAut.conj g) z₁) := by
    rw [← hg, hcoe]
    exact h.map_equiv (MulAut.conj g)
  have h2 := h1.map_equiv e.symm
  refine ⟨e.symm ((MulAut.conj g) z₁), ?_, (centerIs_iff _ _).2 ?_⟩
  · rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hz]
  · have hmap : ((sylowMap e S : Subgroup H)).map e.symm.toMonoidHom = (S : Subgroup G) := by
      rw [coe_sylowMap, Subgroup.map_map]
      have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
        ext x; simp
      rw [this, Subgroup.map_id]
    rw [hmap] at h2
    exact h2

theorem eq_of_mem_zpowers_of_orderOf_two {G : Type*} [Group G] {c x : G} (hc : orderOf c = 2)
    (hx : orderOf x = 2) (hmem : x ∈ Subgroup.zpowers c) : x = c := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h := zpow_mod_orderOf c k
  rw [hc] at h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    have : c ^ k = 1 := by
      rw [← h]
      have : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
      rw [this]; simp
    rw [this, orderOf_one] at hx
    omega
  · have : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [← h, this, zpow_one]

theorem exists_equiv_of_center {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (e : G ≃* H)
    (S₁ : Sylow 2 H) (z₁ : H) (hz : orderOf z₁ = 2) (h : CenterIs (S₁ : Subgroup H) z₁)
    (S : Sylow 2 G) (z : G) (hz' : orderOf z = 2)
    (hc : (Subgroup.center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = Subgroup.zpowers z) :
    ∃ Φ : G ≃* H, Φ z = z₁ := by
  have hcz : CenterIs (S : Subgroup G) z := (centerIs_iff _ _).1 hc
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₁ (sylowMap e S)
  have hcoe : ((g • S₁ : Sylow 2 H) : Subgroup H) =
      (S₁ : Subgroup H).map (MulAut.conj g).toMonoidHom := toSubmonoid_inj.mp rfl
  have h1 : CenterIs ((sylowMap e S : Sylow 2 H) : Subgroup H) ((MulAut.conj g) z₁) := by
    rw [← hg, hcoe]
    exact h.map_equiv (MulAut.conj g)
  have h2 : CenterIs ((sylowMap e S : Sylow 2 H) : Subgroup H) (e z) := by
    rw [coe_sylowMap]
    exact hcz.map_equiv e
  have hmem : e z ∈ Subgroup.zpowers ((MulAut.conj g) z₁) :=
    (h1 (e z)).1 ((h2 (e z)).2 (Subgroup.mem_zpowers _))
  have hord1 : orderOf ((MulAut.conj g) z₁) = 2 := by rw [MulEquiv.orderOf_eq, hz]
  have hord2 : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq, hz']
  have hez : e z = (MulAut.conj g) z₁ := eq_of_mem_zpowers_of_orderOf_two hord1 hord2 hmem
  refine ⟨e.trans (MulAut.conj g⁻¹), ?_⟩
  show (MulAut.conj g⁻¹) (e z) = z₁
  rw [hez]
  simp only [MulAut.conj_apply]
  group

theorem card_pPrimeCore_centralizer_of_equiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (z : G) :
    Nat.card ↥(CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({z} : Set G))) =
      Nat.card ↥(CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({Φ z} : Set H))) := by
  have hmap : (Subgroup.centralizer ({z} : Set G)).map Φ.toMonoidHom =
      Subgroup.centralizer ({Φ z} : Set H) := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      show Φ y * Φ z = Φ z * Φ y
      rw [← map_mul, ← map_mul, hy]
    · intro hx
      refine ⟨Φ.symm x, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hx
  let ψ : ↥(Subgroup.centralizer ({z} : Set G)) ≃* ↥(Subgroup.centralizer ({Φ z} : Set H)) :=
    (MulEquiv.subgroupMap Φ _).trans (MulEquiv.subgroupCongr hmap)
  have := CFSG.pPrimeCore_map_iso 2 ψ
  rw [← this]
  exact (Subgroup.card_map_of_injective ψ.injective).symm

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
