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

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup

variable {G P : Type*} [Group G] [Group P] {C : Subgroup G}

@[expose] def push (ι : ↥C →* P) (H : Subgroup G) : Subgroup P := (H.subgroupOf C).map ι

theorem push_def (ι : ↥C →* P) (H : Subgroup G) : push ι H = (H.subgroupOf C).map ι := rfl

theorem mem_push (ι : ↥C →* P) {H : Subgroup G} {p : P} :
    p ∈ push ι H ↔ ∃ c : ↥C, (c : G) ∈ H ∧ ι c = p := by
  change p ∈ (H.subgroupOf C).map ι ↔ ∃ c : ↥C, (c : G) ∈ H ∧ ι c = p
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem push_mono (ι : ↥C →* P) {H H' : Subgroup G} (h : H ≤ H') : push ι H ≤ push ι H' := by
  change (H.subgroupOf C).map ι ≤ (H'.subgroupOf C).map ι
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono C h)

theorem push_inf {ι : ↥C →* P} (hι : Function.Injective ι) (H H' : Subgroup G) :
    push ι (H ⊓ H') = push ι H ⊓ push ι H' := by
  have h : (H ⊓ H').subgroupOf C = H.subgroupOf C ⊓ H'.subgroupOf C :=
    Subgroup.comap_inf H H' C.subtype
  calc push ι (H ⊓ H') = ((H ⊓ H').subgroupOf C).map ι := rfl
    _ = (H.subgroupOf C ⊓ H'.subgroupOf C).map ι := by rw [h]
    _ = (H.subgroupOf C).map ι ⊓ (H'.subgroupOf C).map ι := Subgroup.map_inf _ _ ι hι
    _ = push ι H ⊓ push ι H' := rfl

theorem push_le_push_iff {ι : ↥C →* P} (hι : Function.Injective ι) {H H' : Subgroup G}
    (hH : H ≤ C) : push ι H ≤ push ι H' ↔ H ≤ H' := by
  constructor
  · intro h x hx
    have hmem : ι ⟨x, hH hx⟩ ∈ push ι H' := by
      apply h
      rw [mem_push]
      exact ⟨⟨x, hH hx⟩, hx, rfl⟩
    rw [mem_push] at hmem
    obtain ⟨c, hc, hci⟩ := hmem
    have hc_eq : c = (⟨x, hH hx⟩ : ↥C) := hι hci
    rw [hc_eq] at hc
    simpa using hc
  · intro h
    exact push_mono ι h

theorem push_injective_of_le {ι : ↥C →* P} (hι : Function.Injective ι) {H H' : Subgroup G}
    (hH : H ≤ C) (hH' : H' ≤ C) (h : push ι H = push ι H') : H = H' := by
  apply le_antisymm
  · exact (push_le_push_iff hι hH).mp (le_of_eq h)
  · exact (push_le_push_iff hι hH').mp (le_of_eq h.symm)

theorem card_push {ι : ↥C →* P} (hι : Function.Injective ι) {H : Subgroup G} (hH : H ≤ C) :
    Nat.card ↥(push ι H) = Nat.card ↥H := by
  calc Nat.card ↥(push ι H) = Nat.card ↥(H.subgroupOf C) :=
        Subgroup.card_map_of_injective hι
    _ = Nat.card ↥H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv

theorem push_bot (ι : ↥C →* P) : push ι (⊥ : Subgroup G) = ⊥ := by
  change ((⊥ : Subgroup G).subgroupOf C).map ι = ⊥
  simp

theorem push_self (ι : ↥C →* P) : push ι C = ι.range := by
  change (C.subgroupOf C).map ι = ι.range
  rw [Subgroup.subgroupOf_self, Subgroup.map_top]

theorem push_commutator (ι : ↥C →* P) {H H' : Subgroup G} (hH : H ≤ C) (hH' : H' ≤ C) :
    push ι ⁅H, H'⁆ = ⁅push ι H, push ι H'⁆ := by
  have hcomm : ⁅H, H'⁆ ≤ C := Subgroup.commutator_le_of_le hH hH'
  have key : ⁅H, H'⁆.subgroupOf C = ⁅H.subgroupOf C, H'.subgroupOf C⁆ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le hcomm, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hH, Subgroup.map_subgroupOf_eq_of_le hH']
  calc push ι ⁅H, H'⁆ = (⁅H, H'⁆.subgroupOf C).map ι := rfl
    _ = (⁅H.subgroupOf C, H'.subgroupOf C⁆).map ι := by rw [key]
    _ = ⁅(H.subgroupOf C).map ι, (H'.subgroupOf C).map ι⁆ :=
        Subgroup.map_commutator (H.subgroupOf C) (H'.subgroupOf C) ι
    _ = ⁅push ι H, push ι H'⁆ := rfl

theorem push_sup (ι : ↥C →* P) {H H' : Subgroup G} (hH : H ≤ C) (hH' : H' ≤ C) :
    push ι (H ⊔ H') = push ι H ⊔ push ι H' := by
  calc push ι (H ⊔ H') = ((H ⊔ H').subgroupOf C).map ι := rfl
    _ = (H.subgroupOf C ⊔ H'.subgroupOf C).map ι := by rw [Subgroup.subgroupOf_sup hH hH']
    _ = (H.subgroupOf C).map ι ⊔ (H'.subgroupOf C).map ι := Subgroup.map_sup _ _ ι
    _ = push ι H ⊔ push ι H' := rfl

theorem push_centralizer_singleton {ι : ↥C →* P} (hι : Function.Injective ι) {g : G} (hg : g ∈ C) :
    push ι (centralizer ({g} : Set G)) = centralizer ({ι ⟨g, hg⟩} : Set P) ⊓ ι.range := by
  ext p
  rw [Subgroup.mem_inf, mem_push]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    constructor
    · rw [← map_mul, ← map_mul]
      apply congrArg ι
      apply Subtype.ext
      simpa using hc
    · exact ⟨c, rfl⟩
  · rintro ⟨hp, hr⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hp
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hr
    refine ⟨c, ?_, hc⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * ⟨g, hg⟩ = ⟨g, hg⟩ * c := by
      apply hι
      rw [map_mul, map_mul, hc]
      exact hp
    simpa using congrArg (fun x : ↥C => (x : G)) h1

theorem push_centralizer {ι : ↥C →* P} (hι : Function.Injective ι) {H : Subgroup G} (hH : H ≤ C) :
    push ι (centralizer (H : Set G)) = centralizer (push ι H : Set P) ⊓ ι.range := by
  ext p
  rw [Subgroup.mem_inf, mem_push]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨?_, ⟨c, rfl⟩⟩
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro q hq
    change q ∈ push ι H at hq
    rw [mem_push] at hq
    obtain ⟨a, ha, rfl⟩ := hq
    have h1 : a * c = c * a := by
      apply Subtype.ext
      simpa using hc (a : G) ha
    rw [← map_mul, ← map_mul, h1]
  · rintro ⟨hp, hr⟩
    rw [Subgroup.mem_centralizer_iff] at hp
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hr
    refine ⟨c, ?_, hc⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hb : ι ⟨h, hH hh⟩ ∈ push ι H := by
      rw [mem_push]
      exact ⟨⟨h, hH hh⟩, hh, rfl⟩
    have h2 : (⟨h, hH hh⟩ : ↥C) * c = c * ⟨h, hH hh⟩ := by
      apply hι
      rw [map_mul, map_mul, hc]
      exact hp _ hb
    simpa using congrArg (fun x : ↥C => (x : G)) h2

theorem push_map_conj (ι : ↥C →* P) {c : G} (hc : c ∈ C) {H : Subgroup G} (hH : H ≤ C) :
    push ι (H.map (MulAut.conj c).toMonoidHom) =
      (push ι H).map (MulAut.conj (ι ⟨c, hc⟩)).toMonoidHom := by
  let φ : G →* G := (MulAut.conj c).toMonoidHom
  let ψ : ↥C →* ↥C := (MulAut.conj (⟨c, hc⟩ : ↥C)).toMonoidHom
  let χ : P →* P := (MulAut.conj (ι ⟨c, hc⟩)).toMonoidHom
  have hφC : H.map φ ≤ C := by
    rintro x hx
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hx
    have hφh : φ h = c * h * c⁻¹ := by simp [φ, MulAut.conj_apply]
    rw [hφh]
    exact C.mul_mem (C.mul_mem hc (hH hh)) (C.inv_mem hc)
  have hcomp1 : C.subtype.comp ψ = φ.comp C.subtype := by
    ext a
    show C.subtype (MulAut.conj (⟨c, hc⟩ : ↥C) a) = MulAut.conj c (C.subtype a)
    simp [MulAut.conj_apply]
  have hcomp2 : ι.comp ψ = χ.comp ι := by
    ext a
    show ι (MulAut.conj (⟨c, hc⟩ : ↥C) a) = MulAut.conj (ι ⟨c, hc⟩) (ι a)
    simp [MulAut.conj_apply]
  have key : (H.map φ).subgroupOf C = (H.subgroupOf C).map ψ := by
    apply Subgroup.map_subtype_inj.mp
    rw [Subgroup.map_subgroupOf_eq_of_le hφC]
    rw [Subgroup.map_map, hcomp1, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hH]
  change push ι (H.map φ) = (push ι H).map χ
  calc push ι (H.map φ) = ((H.map φ).subgroupOf C).map ι := rfl
    _ = ((H.subgroupOf C).map ψ).map ι := by rw [key]
    _ = (H.subgroupOf C).map (ι.comp ψ) := by rw [Subgroup.map_map]
    _ = (H.subgroupOf C).map (χ.comp ι) := by rw [hcomp2]
    _ = ((H.subgroupOf C).map ι).map χ := by rw [Subgroup.map_map]
    _ = (push ι H).map χ := rfl

end CFSG.EvenSporadicStandard.M12Std.PropA
