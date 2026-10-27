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

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open Subgroup

variable {E X : Type*} [Group E] [Group X]

theorem eps_mem_ker {q : E →* X} {β : E ≃* E} {r : X} (hβq : ∀ e, q (β e) = r * q e * r⁻¹)
    {Q : Subgroup X} (hQ : ∀ t ∈ Q, r * t = t * r) {p : E} (hp : q p ∈ Q) :
    p⁻¹ * β p ∈ q.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hβq, hQ _ hp, mul_inv_cancel_right, inv_mul_cancel]

@[expose] def epsHom (q : E →* X) (hcen : q.ker ≤ center E) (β : E ≃* E) (r : X)
    (hβq : ∀ e, q (β e) = r * q e * r⁻¹) (Q : Subgroup X) (hQ : ∀ t ∈ Q, r * t = t * r) :
    Q.comap q →* q.ker :=
  MonoidHom.mk' (fun p => ⟨(p : E)⁻¹ * β p, eps_mem_ker hβq hQ p.2⟩) fun a b => by
    apply Subtype.ext
    have hc : (a : E)⁻¹ * β a ∈ center E := hcen (eps_mem_ker hβq hQ a.2)
    show ((a : E) * b)⁻¹ * β ((a : E) * b) = (a : E)⁻¹ * β a * ((b : E)⁻¹ * β b)
    rw [map_mul, mul_inv_rev]
    calc (b : E)⁻¹ * (a : E)⁻¹ * (β a * β b) = (b : E)⁻¹ * ((a : E)⁻¹ * β a) * β b := by group
      _ = (a : E)⁻¹ * β a * (b : E)⁻¹ * β b := by rw [(mem_center_iff.mp hc _)]
      _ = (a : E)⁻¹ * β a * ((b : E)⁻¹ * β b) := by group

theorem epsHom_apply (q : E →* X) (hcen : q.ker ≤ center E) (β : E ≃* E) (r : X)
    (hβq : ∀ e, q (β e) = r * q e * r⁻¹) (Q : Subgroup X) (hQ : ∀ t ∈ Q, r * t = t * r)
    (p : Q.comap q) : (epsHom q hcen β r hβq Q hQ p : E) = (p : E)⁻¹ * β p := by
  simp [epsHom]

theorem card_comap_eq [Finite E] (q : E →* X) (Q : Subgroup X) (hQq : Q ≤ q.range) :
    Nat.card (Q.comap q) = Nat.card Q * Nat.card q.ker := by
  set f : Q.comap q →* Q := (q.comp (Q.comap q).subtype).codRestrict Q (fun p => p.2) with hf
  have hfs : Function.Surjective f := by
    intro t
    obtain ⟨e, he⟩ := hQq t.2
    exact ⟨⟨e, by rw [mem_comap, he]; exact t.2⟩, Subtype.ext he⟩
  have h3 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hfs, Subgroup.card_top] at h3
  have hk : Nat.card f.ker = Nat.card q.ker := by
    refine Nat.card_congr
      { toFun := fun p => ⟨p.1.1, by
          have h := p.2
          rw [MonoidHom.mem_ker] at h ⊢
          exact congrArg Subtype.val h⟩
        invFun := fun z => ⟨⟨z.1, by rw [mem_comap, MonoidHom.mem_ker.mp z.2]; exact Q.one_mem⟩,
          by rw [MonoidHom.mem_ker]; exact Subtype.ext (MonoidHom.mem_ker.mp z.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hk] at h3
  rw [← h3, mul_comm]

theorem card_fixed_eq [Finite E] (q : E →* X) (hcen : q.ker ≤ center E) (β : E ≃* E) (r : X)
    (hβq : ∀ e, q (β e) = r * q e * r⁻¹) (hinv : ∀ z ∈ q.ker, β z = z⁻¹) (Q : Subgroup X)
    (hQ : ∀ t ∈ Q, r * t = t * r) (hQq : Q ≤ q.range)
    (hsurj : ∀ z ∈ q.ker, ∃ p : E, q p ∈ Q ∧ ∃ w ∈ q.ker, z = p⁻¹ * β p * w * w) :
    Nat.card {e : E // q e ∈ Q ∧ β e = e} = Nat.card Q := by
  set ε := epsHom q hcen β r hβq Q hQ with hεd
  have hεz : ∀ w : q.ker, ∃ p : Q.comap q, ε p = w⁻¹ * w⁻¹ := by
    intro w
    refine ⟨⟨w, by rw [mem_comap, MonoidHom.mem_ker.mp w.2]; exact Q.one_mem⟩, ?_⟩
    apply Subtype.ext
    rw [hεd, epsHom_apply, hinv _ w.2]
    simp
  have hεs : Function.Surjective ε := by
    intro z
    obtain ⟨p, hp, w, hw, hz⟩ := hsurj z z.2
    obtain ⟨p', hp'⟩ := hεz ⟨w, hw⟩
    refine ⟨⟨p, hp⟩ * p'⁻¹, Subtype.ext ?_⟩
    rw [map_mul, map_inv, hp', Subgroup.coe_mul, Subgroup.coe_inv, hεd, epsHom_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hz, mul_inv_rev, inv_inv]
    simp only [mul_assoc]
  have hker : ∀ p : Q.comap q, p ∈ ε.ker ↔ β p = p := by
    intro p
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [hεd, epsHom_apply, OneMemClass.coe_one] at h'
      exact (inv_mul_eq_one.mp h').symm
    · intro h
      apply Subtype.ext
      rw [hεd, epsHom_apply, h, inv_mul_cancel, OneMemClass.coe_one]
  have e1 : {e : E // q e ∈ Q ∧ β e = e} ≃ ε.ker :=
    { toFun := fun e => ⟨⟨e.1, e.2.1⟩, (hker _).2 e.2.2⟩
      invFun := fun p => ⟨p.1.1, p.1.2, (hker _).1 p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e1]
  have h1 := Subgroup.card_ker_mul_card_range ε
  rw [MonoidHom.range_eq_top.mpr hεs, Subgroup.card_top, card_comap_eq q Q hQq] at h1
  have hpos : 0 < Nat.card q.ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

end CFSG.ComponentClassification.GrSLit.L34Facts
