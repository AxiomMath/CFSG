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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup LinearMap QuadraticMap

namespace CFSG.GF2Type.Widths1112

section Eichler

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem polar_map_isometry {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ u, q (g u) = q u) (a b : V) : polar q (g a) (g b) = polar q a b := by
  have hab : g a + g b = g (a + b) := (_root_.map_add g a b).symm
  simp only [QuadraticMap.polar, hab, hg]

theorem exists_polar_eq_one {q : QuadraticForm (ZMod 2) V}
    (hnd : (QuadraticMap.polarBilin q).Nondegenerate) {v : V} (hv : v ≠ 0) :
    ∃ y, polar q v y = 1 := by
  by_contra hcon
  have key : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  apply hv
  apply hnd.1 v
  intro y
  rw [QuadraticMap.polarBilin_apply_apply]
  exact key _ (fun h => hcon ⟨y, h⟩)

theorem polar_map_sub_self {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ u, q (g u) = q u) {v y : V} (hgv : g v = v) (hy : polar q v y = 1) :
    polar q v (g y - y) = 0 := by
  have h1 : polar q v (g y) = polar q v y := by
    have h := polar_map_isometry hg v y
    rw [hgv] at h
    exact h
  rw [QuadraticMap.polar_sub_right, h1, sub_self]

theorem eq_one_of_fix {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ u, q (g u) = q u) {v y : V} (hgv : g v = v) (hy : polar q v y = 1) (hgy : g y = y)
    (hgt : ∀ u, polar q u v = 0 → g u - u ∈ Submodule.span (ZMod 2) {v}) : g = 1 := by
  have key : ∀ w : V, polar q v w = 0 → g w = w := by
    intro w hw
    have hwv : polar q w v = 0 := by
      rw [QuadraticMap.polar_comm]
      exact hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hgt w hwv)
    have hgw : g w = w + a • v := by
      rw [ha]
      abel
    have h0 := polar_map_isometry hg w y
    rw [hgy, hgw, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hy,
      smul_eq_mul] at h0
    have ha0 : a = 0 := by
      linear_combination h0
    rw [hgw, ha0, zero_smul, add_zero]
  apply LinearEquiv.ext
  intro u
  have hw : polar q v (u - polar q v u • y) = 0 := by
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hy, smul_eq_mul,
      mul_one, sub_self]
  have hfix := key _ hw
  rw [_root_.map_sub, _root_.map_smul, hgy] at hfix
  exact sub_left_inj.1 hfix

theorem map_sub_self_ne {q : QuadraticForm (ZMod 2) V} {g : V ≃ₗ[ZMod 2] V}
    (hg : ∀ u, q (g u) = q u) {v y : V} (hqv : q v = 0) (hy : polar q v y = 1) :
    g y - y ≠ v := by
  intro h
  have h1 : g y = y + v := by
    rw [← h]
    abel
  have h2 : q (y + v) = q y := by
    rw [← h1]
    exact hg y
  rw [QuadraticMap.map_add q y v, hqv, add_zero] at h2
  have hc : polar q y v = polar q v y := QuadraticMap.polar_comm q y v
  have h3 : (1 : ZMod 2) = 0 := by
    linear_combination h2 - hc - hy
  exact absurd h3 (by decide)

def eichK (q : QuadraticForm (ZMod 2) V) (v : V) (S : Subgroup (V ≃ₗ[ZMod 2] V)) :
    Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | g ∈ S ∧ g v = v ∧ (∀ u, polar q (g u) v = polar q u v) ∧
    ∀ u, polar q u v = 0 → g u - u ∈ Submodule.span (ZMod 2) {v}}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨haS, hav, haP, haT⟩ := ha
    obtain ⟨hbS, hbv, hbP, hbT⟩ := hb
    refine ⟨S.mul_mem haS hbS, ?_, ?_, ?_⟩
    · show a (b v) = v
      rw [hbv, hav]
    · intro u
      show polar q (a (b u)) v = polar q u v
      rw [haP (b u), hbP u]
    · intro u hu
      show a (b u) - u ∈ Submodule.span (ZMod 2) {v}
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hbT u hu)
      have h1 : a (b u - u) ∈ Submodule.span (ZMod 2) {v} := by
        rw [Submodule.mem_span_singleton]
        exact ⟨c, by rw [← hc, map_smul, hav]⟩
      have h2 : a (b u) - u = a (b u - u) + (a u - u) := by
        rw [map_sub, sub_add_sub_cancel]
      rw [h2]
      exact Submodule.add_mem _ h1 (haT u hu)
  one_mem' := by
    refine ⟨S.one_mem, rfl, fun u => rfl, fun u _ => ?_⟩
    show u - u ∈ Submodule.span (ZMod 2) {v}
    rw [sub_self]
    exact Submodule.zero_mem _
  inv_mem' := by
    intro g hg
    obtain ⟨hgS, hgv, hgP, hgT⟩ := hg
    have hinvv : ∀ x : V, g (g⁻¹ x) = x := fun x => g.apply_symm_apply x
    have hinvP : ∀ x : V, polar q (g⁻¹ x) v = polar q x v := fun x => by
      rw [← hgP (g⁻¹ x), hinvv x]
    have hinvv' : g⁻¹ v = v := by
      have h : g⁻¹ (g v) = v := g.symm_apply_apply v
      rw [hgv] at h
      exact h
    refine ⟨S.inv_mem hgS, hinvv', fun u => hinvP u, fun u hu => ?_⟩
    show g⁻¹ u - u ∈ Submodule.span (ZMod 2) {v}
    have hu' : polar q (g⁻¹ u) v = 0 := (hinvP u).trans hu
    have h := hgT (g⁻¹ u) hu'
    rw [hinvv u] at h
    rw [← neg_sub]
    exact Submodule.neg_mem _ h

theorem finrank_ker_polarBilin [Finite V] {q : QuadraticForm (ZMod 2) V} {v y : V}
    (hy : polar q v y = 1) :
    Module.finrank (ZMod 2) (LinearMap.ker (QuadraticMap.polarBilin q v)) + 1 =
      Module.finrank (ZMod 2) V := by
  have hfy : QuadraticMap.polarBilin q v y = 1 := by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact hy
  have hsurj : LinearMap.range (QuadraticMap.polarBilin q v) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨c • y, ?_⟩
    rw [map_smul, hfy, smul_eq_mul, mul_one]
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (QuadraticMap.polarBilin q v)) = 1 := by
    rw [hsurj, finrank_top, Module.finrank_self]
  have key := LinearMap.finrank_range_add_finrank_ker (QuadraticMap.polarBilin q v)
  omega

theorem card_map_mkQ_ker [Finite V] {q : QuadraticForm (ZMod 2) V} {v y : V} (hv : v ≠ 0)
    (hqv : q v = 0) (hy : polar q v y = 1) :
    Nat.card (Submodule.map (Submodule.mkQ (Submodule.span (ZMod 2) {v}))
      (LinearMap.ker (QuadraticMap.polarBilin q v))) = 2 ^ (Module.finrank (ZMod 2) V - 2) := by
  have hK := finrank_ker_polarBilin hy
  have hvK : v ∈ LinearMap.ker (QuadraticMap.polarBilin q v) := by
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, hqv,
      smul_zero]
  have hWK : Submodule.span (ZMod 2) {v} ≤ LinearMap.ker (QuadraticMap.polarBilin q v) :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 hvK)
  have hW : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = 1 :=
    finrank_span_singleton (K := ZMod 2) hv
  have hkerfin : Module.finrank (ZMod 2)
      (LinearMap.ker ((Submodule.span (ZMod 2) {v}).mkQ ∘ₗ
        (LinearMap.ker (QuadraticMap.polarBilin q v)).subtype)) = 1 := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    exact (Submodule.comapSubtypeEquivOfLe hWK).finrank_eq.trans hW
  have hrn := LinearMap.finrank_range_add_finrank_ker
    ((Submodule.span (ZMod 2) {v}).mkQ ∘ₗ (LinearMap.ker (QuadraticMap.polarBilin q v)).subtype)
  rw [hkerfin, LinearMap.range_comp, Submodule.range_subtype] at hrn
  have hT : Module.finrank (ZMod 2)
      (Submodule.map (Submodule.mkQ (Submodule.span (ZMod 2) {v}))
        (LinearMap.ker (QuadraticMap.polarBilin q v))) = Module.finrank (ZMod 2) V - 2 := by
    omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hT]

private theorem eichK_mem_iff {q : QuadraticForm (ZMod 2) V} {v : V}
    {S : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ eichK q v S ↔ g ∈ S ∧ g v = v ∧ (∀ u, polar q (g u) v = polar q u v) ∧
      ∀ u, polar q u v = 0 → g u - u ∈ Submodule.span (ZMod 2) {v} :=
  Iff.rfl

private theorem eichK_theta_mem {q : QuadraticForm (ZMod 2) V} {v y : V}
    {S : Subgroup (V ≃ₗ[ZMod 2] V)} (hSq : ∀ g ∈ S, ∀ u, q (g u) = q u)
    (hy : polar q v y = 1) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ eichK q v S) :
    g y - y ∈ LinearMap.ker (QuadraticMap.polarBilin q v) := by
  obtain ⟨hS, hgv, -, -⟩ := eichK_mem_iff.mp hg
  rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
  exact polar_map_sub_self (hSq g hS) hgv hy

private theorem eichK_delta_mul {q : QuadraticForm (ZMod 2) V} {v y : V}
    {S : Subgroup (V ≃ₗ[ZMod 2] V)} (hSq : ∀ g ∈ S, ∀ u, q (g u) = q u)
    (hy : polar q v y = 1) {g h : V ≃ₗ[ZMod 2] V} (hg : g ∈ eichK q v S)
    (hh : h ∈ eichK q v S) :
    Submodule.mkQ (Submodule.span (ZMod 2) {v}) ((g * h) y - y) =
      Submodule.mkQ (Submodule.span (ZMod 2) {v}) (g y - y) +
        Submodule.mkQ (Submodule.span (ZMod 2) {v}) (h y - y) := by
  obtain ⟨-, -, -, hgt⟩ := eichK_mem_iff.mp hg
  obtain ⟨hhS, hhv, -, -⟩ := eichK_mem_iff.mp hh
  have hhY : polar q v (h y - y) = 0 := polar_map_sub_self (hSq h hhS) hhv hy
  have hk : g (h y - y) - (h y - y) ∈ Submodule.span (ZMod 2) {v} :=
    hgt _ (by rw [polar_comm]; exact hhY)
  have hsplit : (g * h) y - y = g (h y - y) + (g y - y) := by
    rw [LinearEquiv.mul_apply, map_sub]
    abel
  have hkey : Submodule.mkQ (Submodule.span (ZMod 2) {v}) (g (h y - y)) =
      Submodule.mkQ (Submodule.span (ZMod 2) {v}) (h y - y) := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply]
    exact (Submodule.Quotient.eq _).mpr hk
  rw [hsplit, map_add, hkey]
  exact add_comm _ _

private theorem eichK_eq_one_of_delta {q : QuadraticForm (ZMod 2) V} {v y : V}
    {S : Subgroup (V ≃ₗ[ZMod 2] V)} (hSq : ∀ g ∈ S, ∀ u, q (g u) = q u) (hqv : q v = 0)
    (hy : polar q v y = 1) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ eichK q v S)
    (h0 : Submodule.mkQ (Submodule.span (ZMod 2) {v}) (g y - y) = 0) : g = 1 := by
  obtain ⟨hS, hgv, -, hgt⟩ := eichK_mem_iff.mp hg
  have hmem : g y - y ∈ Submodule.span (ZMod 2) {v} := (Submodule.Quotient.mk_eq_zero _).mp h0
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) a with rfl | rfl
  · rw [zero_smul] at ha
    exact eq_one_of_fix (hSq g hS) hgv hy (sub_eq_zero.mp ha.symm) hgt
  · rw [one_smul] at ha
    exact absurd ha.symm (map_sub_self_ne (hSq g hS) hqv hy)

theorem card_eichK_of_span_eq [Finite V] {q : QuadraticForm (ZMod 2) V}
    (hnd : (QuadraticMap.polarBilin q).Nondegenerate) {v : V} (hv : v ≠ 0) (hqv : q v = 0)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hSq : ∀ g ∈ S, ∀ u, q (g u) = q u)
    (hSv : ∀ g ∈ S, g v = v) {y : V} (hy : polar q v y = 1)
    (hspan : Submodule.span (ZMod 2) ({v} ∪ {u | ∃ g ∈ eichK q v S, u = g y - y}) =
      LinearMap.ker (QuadraticMap.polarBilin q v)) :
    Nat.card (eichK q v S) = 2 ^ (Module.finrank (ZMod 2) V - 2) := by
  have h1y : ∀ z : V, (1 : V ≃ₗ[ZMod 2] V) z = z := fun z => rfl
  have hgen : ∀ u ∈ LinearMap.ker (QuadraticMap.polarBilin q v), ∃ g ∈ eichK q v S,
      Submodule.mkQ (Submodule.span (ZMod 2) {v}) u =
        Submodule.mkQ (Submodule.span (ZMod 2) {v}) (g y - y) := by
    intro u hu
    rw [← hspan] at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      rcases hx with hx | ⟨g, hg, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        have hv0 : Submodule.mkQ (Submodule.span (ZMod 2) {v}) v = 0 :=
          (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self v)
        refine ⟨1, (eichK q v S).one_mem, ?_⟩
        rw [hx, hv0]
        simp [h1y]
      · exact ⟨g, hg, rfl⟩
    | zero => exact ⟨1, (eichK q v S).one_mem, by simp [h1y]⟩
    | add x z _ _ ihx ihz =>
      obtain ⟨g, hg, hgx⟩ := ihx
      obtain ⟨h, hh, hhz⟩ := ihz
      refine ⟨h * g, (eichK q v S).mul_mem hh hg, ?_⟩
      rw [map_add, hgx, hhz, eichK_delta_mul hSq hy hh hg]
      exact add_comm _ _
    | smul a x _ ih =>
      obtain ⟨g, hg, hgx⟩ := ih
      rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) a with rfl | rfl
      · exact ⟨1, (eichK q v S).one_mem, by simp [h1y]⟩
      · rw [one_smul]
        exact ⟨g, hg, hgx⟩
  let f : ↥(eichK q v S) →
      ↥(Submodule.map (Submodule.mkQ (Submodule.span (ZMod 2) {v}))
        (LinearMap.ker (QuadraticMap.polarBilin q v))) :=
    fun g => ⟨Submodule.mkQ (Submodule.span (ZMod 2) {v}) (g.1 y - y),
      Submodule.mem_map.mpr ⟨g.1 y - y, eichK_theta_mem hSq hy g.2, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro g h hgh
    have hgh' : Submodule.mkQ (Submodule.span (ZMod 2) {v}) (g.1 y - y) =
        Submodule.mkQ (Submodule.span (ZMod 2) {v}) (h.1 y - y) := congrArg Subtype.val hgh
    have hk : g.1 * h.1⁻¹ ∈ eichK q v S :=
      (eichK q v S).mul_mem g.2 ((eichK q v S).inv_mem h.2)
    have h1 := eichK_delta_mul hSq hy hk h.2
    rw [inv_mul_cancel_right] at h1
    have h2 : Submodule.mkQ (Submodule.span (ZMod 2) {v}) ((g.1 * h.1⁻¹) y - y) +
        Submodule.mkQ (Submodule.span (ZMod 2) {v}) (h.1 y - y) =
        0 + Submodule.mkQ (Submodule.span (ZMod 2) {v}) (h.1 y - y) := by
      rw [zero_add]
      exact h1.symm.trans hgh'
    have hk0 := add_right_cancel h2
    exact Subtype.ext (mul_inv_eq_one.mp (eichK_eq_one_of_delta hSq hqv hy hk hk0))
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨u, hu, hux⟩ := Submodule.mem_map.mp x.2
    obtain ⟨g, hg, hgu⟩ := hgen u hu
    exact ⟨⟨g, hg⟩, Subtype.ext (hgu.symm.trans hux)⟩
  exact (Nat.card_eq_of_bijective f ⟨hinj, hsurj⟩).trans (card_map_mkQ_ker hv hqv hy)

private theorem mem_eichK_iff' {q : QuadraticForm (ZMod 2) V} {v : V}
    {S : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} :
    g ∈ eichK q v S ↔ g ∈ S ∧ g v = v ∧ (∀ u, polar q (g u) v = polar q u v) ∧
      ∀ u, polar q u v = 0 → g u - u ∈ Submodule.span (ZMod 2) {v} :=
  Iff.rfl

private theorem polar_apply_fix {q : QuadraticForm (ZMod 2) V} {v : V} {k : V ≃ₗ[ZMod 2] V}
    (hkq : ∀ u, q (k u) = q u) (hkv : k v = v) (w : V) :
    polar q (k w) v = polar q w v := by
  have h1 := polar_map_isometry (g := k) hkq w v
  rw [hkv] at h1
  exact h1

private theorem zmod2_eq_zero_or_one : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem eichK_dichotomy [Finite V] {q : QuadraticForm (ZMod 2) V}
    (hnd : (QuadraticMap.polarBilin q).Nondegenerate)
    {v : V} (hv : v ≠ 0) (hqv : q v = 0)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hSq : ∀ g ∈ S, ∀ u, q (g u) = q u)
    (hSv : ∀ g ∈ S, g v = v) (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hHS : H ≤ S)
    (hirr : ∀ U : Submodule (ZMod 2) V, v ∈ U → U ≤ LinearMap.ker (QuadraticMap.polarBilin q v) →
      (∀ g ∈ H, U.map (g : V →ₗ[ZMod 2] V) = U) →
      U = Submodule.span (ZMod 2) {v} ∨ U = LinearMap.ker (QuadraticMap.polarBilin q v)) :
    eichK q v S = ⊥ ∨ Nat.card (eichK q v S) = 2 ^ (Module.finrank (ZMod 2) V - 2) := by
  by_cases hK : eichK q v S = ⊥
  · exact Or.inl hK
  refine Or.inr ?_
  obtain ⟨y, hy⟩ := exists_polar_eq_one hnd hv
  obtain ⟨U, hU⟩ : ∃ U : Submodule (ZMod 2) V,
      U = Submodule.span (ZMod 2) ({v} ∪ {u | ∃ g ∈ eichK q v S, u = g y - y}) := ⟨_, rfl⟩
  have hvU : v ∈ U := by
    rw [hU]
    exact Submodule.subset_span (Set.mem_union_left _ (Set.mem_singleton v))
  have hθU : ∀ g ∈ eichK q v S, g y - y ∈ U := by
    intro g hg
    rw [hU]
    exact Submodule.subset_span (Set.mem_union_right _ ⟨g, hg, rfl⟩)
  have hUker : U ≤ LinearMap.ker (QuadraticMap.polarBilin q v) := by
    rw [hU, Submodule.span_le]
    rintro x (hx | ⟨g, hg, rfl⟩)
    · rw [Set.mem_singleton_iff.mp hx, SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply,
        polar_self, hqv, smul_zero]
    · obtain ⟨hgS, hgv, -, -⟩ := mem_eichK_iff'.mp hg
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
      exact polar_map_sub_self (hSq g hgS) hgv hy
  have hinv : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) ≤ U := by
    intro h hh
    have hhS : h ∈ S := hHS hh
    have hhq : ∀ u, q (h u) = q u := hSq h hhS
    have hhv : h v = v := hSv h hhS
    have hh'S : h⁻¹ ∈ S := S.inv_mem hhS
    have hh'q : ∀ u, q (h⁻¹ u) = q u := hSq h⁻¹ hh'S
    have hh'v : h⁻¹ v = v := hSv h⁻¹ hh'S
    have hhinv : ∀ u, h (h⁻¹ u) = u := fun u => LinearEquiv.apply_symm_apply h u
    have hkey : ∀ m ∈ ({v} ∪ {u | ∃ g ∈ eichK q v S, u = g y - y} : Set V),
        (h : V →ₗ[ZMod 2] V) m ∈ U := by
      rintro m (hm | ⟨g, hg, rfl⟩)
      · rw [Set.mem_singleton_iff.mp hm]
        show h v ∈ U
        rw [hhv]
        exact hvU
      · obtain ⟨hgS, hgv, hgpol, hgt⟩ := mem_eichK_iff'.mp hg
        have hg'K : h * g * h⁻¹ ∈ eichK q v S := by
          refine mem_eichK_iff'.mpr ⟨S.mul_mem (S.mul_mem hhS hgS) hh'S, ?_, ?_, ?_⟩
          · show h (g (h⁻¹ v)) = v
            rw [hh'v, hgv, hhv]
          · intro u
            show polar q (h (g (h⁻¹ u))) v = polar q u v
            rw [polar_apply_fix hhq hhv, hgpol, polar_apply_fix hh'q hh'v]
          · intro u hu
            show h (g (h⁻¹ u)) - u ∈ Submodule.span (ZMod 2) {v}
            have hz : polar q (h⁻¹ u) v = 0 := by
              rw [polar_apply_fix hh'q hh'v]
              exact hu
            obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hgt (h⁻¹ u) hz)
            have e1 : h (g (h⁻¹ u)) - u = h (g (h⁻¹ u) - h⁻¹ u) := by
              rw [map_sub, hhinv u]
            rw [e1, ← ha, map_smul, hhv]
            exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v)
        show h (g y - y) ∈ U
        have hdpol : polar q (y - h⁻¹ y) v = 0 := by
          rw [polar_sub_left, polar_apply_fix hh'q hh'v, sub_self]
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hgt _ hdpol)
        have hav : h (a • v) = a • v := by
          rw [map_smul, hhv]
        have hsum : h (g y - y) = (h (g (h⁻¹ y)) - y) + a • v := by
          rw [← hav, ha]
          simp only [map_sub, hhinv y]
          abel
        rw [hsum]
        exact Submodule.add_mem U (hθU _ hg'K) (Submodule.smul_mem U a hvU)
    rw [hU] at hkey ⊢
    exact (Submodule.map_span_le _ _ _).mpr hkey
  have hinv_all : ∀ h ∈ H, U.map (h : V →ₗ[ZMod 2] V) = U := by
    intro h hh
    refine le_antisymm (hinv h hh) ?_
    intro x hx
    have hx' : (h⁻¹ : V ≃ₗ[ZMod 2] V) x ∈ U :=
      hinv h⁻¹ (H.inv_mem hh) (Submodule.mem_map_of_mem hx)
    exact Submodule.mem_map.mpr ⟨h⁻¹ x, hx', LinearEquiv.apply_symm_apply h x⟩
  rcases hirr U hvU hUker hinv_all with hUs | hUk
  · exfalso
    apply hK
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨hgS, hgv, hgpol, hgt⟩ := mem_eichK_iff'.mp hg
    have hθ : g y - y ∈ Submodule.span (ZMod 2) {v} := by
      rw [← hUs]
      exact hθU g hg
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hθ
    have hgy : g y = y := by
      rcases zmod2_eq_zero_or_one a with rfl | rfl
      · rw [zero_smul] at ha
        exact sub_eq_zero.mp ha.symm
      · rw [one_smul] at ha
        exact absurd ha.symm (map_sub_self_ne (hSq g hgS) hqv hy)
    exact eq_one_of_fix (hSq g hgS) hgv hy hgy hgt
  · exact card_eichK_of_span_eq hnd hv hqv S hSq hSv hy (hU.symm.trans hUk)

theorem eichler_eq_one [Finite V] (q : QuadraticForm (ZMod 2) V)
    (hnd : (QuadraticMap.polarBilin q).Nondegenerate)
    {v : V} (hv : v ≠ 0) (hqv : q v = 0)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hSq : ∀ g ∈ S, ∀ u, q (g u) = q u)
    (hSv : ∀ g ∈ S, g v = v) (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hHS : H ≤ S)
    (hirr : ∀ U : Submodule (ZMod 2) V, v ∈ U → U ≤ LinearMap.ker (QuadraticMap.polarBilin q v) →
      (∀ g ∈ H, U.map (g : V →ₗ[ZMod 2] V) = U) →
      U = Submodule.span (ZMod 2) {v} ∨ U = LinearMap.ker (QuadraticMap.polarBilin q v))
    (h2 : ¬ 2 ^ (Module.finrank (ZMod 2) V - 2) ∣ Nat.card S) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ S)
    (hgt : ∀ u, QuadraticMap.polar q u v = 0 → g u - u ∈ Submodule.span (ZMod 2) {v}) :
    g = 1 := by
  have hdich := eichK_dichotomy hnd hv hqv S hSq hSv H hHS hirr
  have hgK : g ∈ eichK q v S := by
    refine ⟨hg, hSv g hg, fun u => ?_, hgt⟩
    calc polar q (g u) v = polar q (g u) (g v) := by rw [hSv g hg]
      _ = polar q u v := polar_map_isometry (hSq g hg) u v
  rcases hdich with h | h
  · rw [h] at hgK
    exact Subgroup.mem_bot.mp hgK
  · exfalso
    have hle : eichK q v S ≤ S := fun x hx => hx.1
    have hdvd : Nat.card (eichK q v S) ∣ Nat.card S := Subgroup.card_dvd_of_le hle
    rw [h] at hdvd
    exact h2 hdvd

end Eichler

private theorem exists_second_fixed {G : Type*} [Group G] (hG : IsPGroup 2 G) {α : Type*}
    [Finite α] [MulAction G α] {a : α} (hdvd : 2 ∣ Nat.card α) (ha : ∀ g : G, g • a = a) :
    ∃ b : α, (∀ g : G, g • b = b) ∧ b ≠ a := by
  obtain ⟨b, hb, hab⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point α hdvd
    (MulAction.mem_fixedPoints.2 ha)
  exact ⟨b, MulAction.mem_fixedPoints.1 hb, fun h => hab h.symm⟩

theorem exists_fixed_mod {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (Y U : Submodule (ZMod 2) V) (hUY : U < Y)
    (N : Subgroup (V ≃ₗ[ZMod 2] V)) (hN2 : IsPGroup 2 N)
    (hY : ∀ g ∈ N, Y.map (g : V →ₗ[ZMod 2] V) = Y)
    (hU : ∀ g ∈ N, U.map (g : V →ₗ[ZMod 2] V) = U) :
    ∃ y ∈ Y, y ∉ U ∧ ∀ g ∈ N, g y - y ∈ U := by
  have hYs : ∀ g ∈ N, ∀ y ∈ Y, g y ∈ Y := by
    intro g hg y hy
    have h : (g : V →ₗ[ZMod 2] V) y ∈ Y.map (g : V →ₗ[ZMod 2] V) :=
      Submodule.mem_map_of_mem hy
    rw [hY g hg] at h
    exact h
  have hUs : ∀ g ∈ N, ∀ y ∈ U, g y ∈ U := by
    intro g hg y hy
    have h : (g : V →ₗ[ZMod 2] V) y ∈ U.map (g : V →ₗ[ZMod 2] V) :=
      Submodule.mem_map_of_mem hy
    rw [hU g hg] at h
    exact h
  let W : Submodule (ZMod 2) Y := U.comap Y.subtype
  have hWmem : ∀ x : Y, x ∈ W ↔ (x : V) ∈ U := fun x => Iff.rfl
  let gY : N → (Y →ₗ[ZMod 2] Y) := fun g =>
    LinearMap.restrict (g.1 : V →ₗ[ZMod 2] V) (fun y hy => hYs g.1 g.2 y hy)
  have hWs : ∀ (g : N) (x : Y), x ∈ W → gY g x ∈ W := by
    intro g x hx
    rw [hWmem] at hx ⊢
    exact hUs g.1 g.2 _ hx
  let gQ : N → (Y ⧸ W) →ₗ[ZMod 2] (Y ⧸ W) := fun g =>
    Submodule.mapQ W W (gY g) (fun x hx => (Submodule.mem_comap).2 (hWs g x hx))
  letI act : MulAction N (Y ⧸ W) :=
    { smul := fun g x => gQ g x
      one_smul := fun x => by
        refine Submodule.Quotient.induction_on W x (fun z => ?_)
        show Submodule.Quotient.mk (gY 1 z) = Submodule.Quotient.mk z
        rw [show gY 1 z = z from Subtype.ext rfl]
      mul_smul := fun g h x => by
        refine Submodule.Quotient.induction_on W x (fun z => ?_)
        show Submodule.Quotient.mk (gY (g * h) z) = Submodule.Quotient.mk (gY g (gY h z))
        rw [show gY (g * h) z = gY g (gY h z) from Subtype.ext rfl] }
  obtain ⟨y0, hy0Y, hy0U⟩ : ∃ y ∈ Y, y ∉ U := by
    obtain ⟨y, hyY, hyU⟩ := SetLike.exists_of_lt hUY
    exact ⟨y, hyY, hyU⟩
  have hne : (Submodule.Quotient.mk (⟨y0, hy0Y⟩ : Y) : Y ⧸ W) ≠ 0 := by
    intro h
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact hy0U ((hWmem _).1 h)
  haveI : Nontrivial (Y ⧸ W) := ⟨⟨_, 0, hne⟩⟩
  haveI : Finite (Y ⧸ W) :=
    Finite.of_surjective (Submodule.Quotient.mk : Y → Y ⧸ W) (Submodule.Quotient.mk_surjective W)
  haveI : Module.Finite (ZMod 2) (Y ⧸ W) := Module.finite_iff_finite.mpr inferInstance
  have hcard : Nat.card (Y ⧸ W) = 2 ^ Module.finrank (ZMod 2) (Y ⧸ W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hk : Module.finrank (ZMod 2) (Y ⧸ W) ≠ 0 := by
    intro h0
    have h1 : 1 < Nat.card (Y ⧸ W) := Finite.one_lt_card
    rw [hcard, h0, pow_zero] at h1
    exact lt_irrefl _ h1
  have hdvd : 2 ∣ Nat.card (Y ⧸ W) := by
    rw [hcard]
    exact dvd_pow_self 2 hk
  have h0fix : ∀ g : N, g • (0 : Y ⧸ W) = 0 := fun g => map_zero (gQ g)
  obtain ⟨b, hbfix, hb0⟩ := exists_second_fixed hN2 hdvd h0fix
  obtain ⟨⟨y, hyY⟩, rfl⟩ := Submodule.Quotient.mk_surjective W b
  refine ⟨y, hyY, ?_, ?_⟩
  · intro hyU
    apply hb0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hWmem ⟨y, hyY⟩).2 hyU
  · intro g hg
    have h1 : (Submodule.Quotient.mk (gY ⟨g, hg⟩ ⟨y, hyY⟩) : Y ⧸ W) =
        Submodule.Quotient.mk ⟨y, hyY⟩ := hbfix ⟨g, hg⟩
    rw [Submodule.Quotient.eq] at h1
    have h2 : ((gY ⟨g, hg⟩ ⟨y, hyY⟩ - ⟨y, hyY⟩ : Y) : V) = g y - y := rfl
    rw [← h2]
    exact (hWmem _).1 h1

end CFSG.GF2Type.Widths1112
