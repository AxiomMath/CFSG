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

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup

variable {V : Type} [Group V]

structure ModData (A : Subgroup V) (Θ : Subgroup (MulAut V)) (ζ : MulAut V) : Prop where
  inv : ∀ θ ∈ Θ, ∀ a ∈ A, θ a ∈ A
  irr : ∀ B : Subgroup V, B ≤ A → (∀ θ ∈ Θ, ∀ b ∈ B, θ b ∈ B) → B = ⊥ ∨ B = A
  comm : ∀ θ ∈ Θ, ζ * θ = θ * ζ
  mem : ∀ v, ζ v * v⁻¹ ∈ A
  onto : ∀ a ∈ A, ∃ v, ζ v * v⁻¹ = a
  ker : ∀ v, ζ v * v⁻¹ = 1 → v ∈ A
  fix : ∀ x ∈ A, x ≠ 1 →
    Nat.card {a : V // a ∈ A ∧ ∀ θ ∈ Θ, θ x = x → θ a = a} ≤ 4
  nontriv : A ≠ ⊥

@[expose] def pimap (hc : ∀ a b : V, a * b = b * a) (ζ : MulAut V) : V →* V where
  toFun v := ζ v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    rw [show b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ from hc _ _]
    calc ζ a * ζ b * (a⁻¹ * b⁻¹) = ζ a * (ζ b * a⁻¹) * b⁻¹ := by group
      _ = ζ a * (a⁻¹ * ζ b) * b⁻¹ := by rw [hc (ζ b) a⁻¹]
      _ = ζ a * a⁻¹ * (ζ b * b⁻¹) := by group

theorem card_le_of_centralizes [Finite V] (hc : ∀ a b : V, a * b = b * a)
    {A : Subgroup V} {Θ : Subgroup (MulAut V)} {ζ : MulAut V} (D : ModData A Θ ζ)
    (H : Subgroup (MulAut V)) (hH : ∀ h ∈ H, ∀ θ ∈ Θ, h * θ = θ * h) : Nat.card H ≤ 256 := by
  classical
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨⟨x, hxA⟩, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 D.nontriv
  have hx1 : x ≠ 1 := fun h => hx (Subtype.ext h)
  obtain ⟨c₀, hc₀⟩ := D.onto x hxA
  set π := pimap hc ζ with hπdef
  have hπ : ∀ v, π v = ζ v * v⁻¹ := fun v => rfl
  have hπθ : ∀ θ ∈ Θ, ∀ v, π (θ v) = θ (π v) := by
    intro θ hθ v
    have h1 : ζ (θ v) = θ (ζ v) := by
      have := congrArg (fun f : MulAut V => f v) (D.comm θ hθ)
      simpa using this
    rw [hπ, hπ, h1, map_mul, map_inv]
  have hπker : ∀ v, π v = 1 → v ∈ A := fun v hv => D.ker v hv
  have F2 : ∀ φ : MulAut V, (∀ θ ∈ Θ, φ * θ = θ * φ) → φ x = x → ∀ a ∈ A, φ a = a := by
    intro φ hφ hφx
    let B : Subgroup V :=
      { carrier := {a | a ∈ A ∧ φ a = a}
        mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
        one_mem' := ⟨A.one_mem, map_one φ⟩
        inv_mem' := fun {a} ha => ⟨A.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
    have hB : B = ⊥ ∨ B = A := D.irr B (fun a ha => ha.1) (by
      intro θ hθ b hb
      refine ⟨D.inv θ hθ b hb.1, ?_⟩
      have := congrArg (fun f : MulAut V => f b) (hφ θ hθ)
      simp only [MulAut.mul_apply] at this
      rw [this, hb.2])
    rcases hB with hB | hB
    · exfalso
      apply hx1
      have : x ∈ B := ⟨hxA, hφx⟩
      rw [hB] at this
      exact Subgroup.mem_bot.1 this
    · intro a ha
      have : a ∈ B := by rw [hB]; exact ha
      exact this.2
  have F3 : ∀ φ : MulAut V, (∀ θ ∈ Θ, φ * θ = θ * φ) → (∀ a ∈ A, φ a = a) → φ c₀ = c₀ →
      φ = 1 := by
    intro φ hφ hφA hφc
    let B' : Subgroup V :=
      { carrier := {v | φ v = v}
        mul_mem' := fun {a b} ha hb => by
          show φ (a * b) = a * b
          rw [map_mul, show φ a = a from ha, show φ b = b from hb]
        one_mem' := map_one φ
        inv_mem' := fun {a} ha => by
          show φ a⁻¹ = a⁻¹
          rw [map_inv, show φ a = a from ha] }
    have hB'inv : ∀ θ ∈ Θ, ∀ b ∈ B', θ b ∈ B' := by
      intro θ hθ b hb
      have := congrArg (fun f : MulAut V => f b) (hφ θ hθ)
      simp only [MulAut.mul_apply] at this
      show φ (θ b) = θ b
      rw [this, show φ b = b from hb]
    let P : Subgroup V := B'.map π
    have hPA : P ≤ A := by
      rintro _ ⟨b, _, rfl⟩
      exact D.mem b
    have hPinv : ∀ θ ∈ Θ, ∀ p ∈ P, θ p ∈ P := by
      rintro θ hθ _ ⟨b, hb, rfl⟩
      exact ⟨θ b, hB'inv θ hθ b hb, hπθ θ hθ b⟩
    have hPtop : P = A := by
      rcases D.irr P hPA hPinv with h | h
      · exfalso
        have : x ∈ P := ⟨c₀, hφc, by rw [hπ]; exact hc₀⟩
        rw [h] at this
        exact hx1 (Subgroup.mem_bot.1 this)
      · exact h
    refine MulEquiv.ext fun v => ?_
    have hv : π v ∈ P := by rw [hPtop]; exact D.mem v
    obtain ⟨b, hb, hbv⟩ := hv
    have hvb : v * b⁻¹ ∈ A := hπker _ (by rw [map_mul, map_inv, hbv, mul_inv_cancel])
    have h2 : φ (v * b⁻¹ * b) = v * b⁻¹ * b := by
      rw [map_mul, hφA _ hvb, show φ b = b from hb]
    simpa using h2
  let F : Subgroup V :=
    { carrier := {v | ∀ θ ∈ Θ, θ x = x → θ v = v}
      mul_mem' := fun {a b} ha hb θ hθ hθx => by rw [map_mul, ha θ hθ hθx, hb θ hθ hθx]
      one_mem' := fun θ _ _ => map_one θ
      inv_mem' := fun {a} ha θ hθ hθx => by rw [map_inv, ha θ hθ hθx] }
  have hF : Nat.card F ≤ 16 := by
    let πF : F →* V := π.comp F.subtype
    have h1 := Subgroup.card_ker_mul_card_range πF
    have hker : Nat.card πF.ker ≤ 4 := by
      refine le_trans (Nat.card_le_card_of_injective
        (fun k : πF.ker => (⟨((k : F) : V), hπker _ (MonoidHom.mem_ker.1 k.2), k.1.2⟩ :
          {a : V // a ∈ A ∧ ∀ θ ∈ Θ, θ x = x → θ a = a})) ?_) (D.fix x hxA hx1)
      intro k k' hkk'
      simp only [Subtype.mk.injEq] at hkk'
      exact Subtype.ext (Subtype.ext hkk')
    have hmem : ∀ r ∈ πF.range, r ∈ A ∧ ∀ θ ∈ Θ, θ x = x → θ r = r := by
      rintro _ ⟨f, rfl⟩
      refine ⟨D.mem _, fun θ hθ hθx => ?_⟩
      show θ (π (f : V)) = π (f : V)
      rw [← hπθ θ hθ, f.2 θ hθ hθx]
    have hrange : Nat.card πF.range ≤ 4 :=
      le_trans (Nat.card_le_card_of_injective
        (fun r : πF.range => (⟨(r : V), (hmem r r.2).1, (hmem r r.2).2⟩ :
          {a : V // a ∈ A ∧ ∀ θ ∈ Θ, θ x = x → θ a = a}))
        (fun r r' hrr' => by
          simp only [Subtype.mk.injEq] at hrr'
          exact Subtype.ext hrr')) (D.fix x hxA hx1)
    calc Nat.card F = Nat.card πF.ker * Nat.card πF.range := h1.symm
      _ ≤ 4 * 4 := Nat.mul_le_mul hker hrange
      _ = 16 := rfl
  have hos : Nat.card (MulAction.stabilizer H x) * (MulAction.orbit H x).ncard = Nat.card H := by
    rw [← MulAction.index_stabilizer, Subgroup.card_mul_index]
  have horb : (MulAction.orbit H x).ncard ≤ 16 := by
    calc (MulAction.orbit H x).ncard ≤ (F : Set V).ncard := by
          refine Set.ncard_le_ncard ?_ (Set.toFinite _)
          rintro _ ⟨φ, rfl⟩ θ hθ hθx
          have h1 := congrArg (fun f : MulAut V => f x) (hH φ φ.2 θ hθ)
          simp only [MulAut.mul_apply, hθx] at h1
          show θ ((φ : MulAut V) x) = (φ : MulAut V) x
          exact h1.symm
      _ = Nat.card F := (Nat.card_coe_set_eq (F : Set V)).symm
      _ ≤ 16 := hF
  have hθc : ∀ θ ∈ Θ, θ x = x → θ c₀ * c₀⁻¹ ∈ A := by
    intro θ hθ hθx
    apply hπker
    rw [map_mul, map_inv, hπθ θ hθ, hπ, hc₀, hθx, mul_inv_cancel]
  have hstab : Nat.card (MulAction.stabilizer H x) ≤ 16 := by
    have hχA : ∀ χ : H, χ ∈ MulAction.stabilizer H x → ∀ a ∈ A, (χ : MulAut V) a = a := by
      intro χ hχ
      apply F2 χ (fun θ hθ => hH χ χ.2 θ hθ)
      exact hχ
    have hmem : ∀ χ : H, χ ∈ MulAction.stabilizer H x →
        (χ : MulAut V) c₀ * c₀⁻¹ ∈ F := by
      intro χ hχ θ hθ hθx
      have hcomm := congrArg (fun f : MulAut V => f c₀) (hH χ χ.2 θ hθ)
      simp only [MulAut.mul_apply] at hcomm
      have ha := hχA χ hχ _ (hθc θ hθ hθx)
      have e1 : (χ : MulAut V) (θ c₀) = θ c₀ * c₀⁻¹ * (χ : MulAut V) c₀ := by
        have : θ c₀ = (θ c₀ * c₀⁻¹) * c₀ := by group
        conv_lhs => rw [this]
        rw [map_mul, ha]
      rw [map_mul, map_inv, ← hcomm, e1]
      calc θ c₀ * c₀⁻¹ * (χ : MulAut V) c₀ * (θ c₀)⁻¹
          = θ c₀ * (c₀⁻¹ * (χ : MulAut V) c₀) * (θ c₀)⁻¹ := by rw [mul_assoc (θ c₀)]
        _ = θ c₀ * (θ c₀)⁻¹ * (c₀⁻¹ * (χ : MulAut V) c₀) := mul_right_comm _ _ _
        _ = (χ : MulAut V) c₀ * c₀⁻¹ := by rw [mul_inv_cancel, one_mul, mul_comm]
    refine le_trans (Nat.card_le_card_of_injective
      (fun χ : MulAction.stabilizer H x => (⟨(χ.1 : MulAut V) c₀ * c₀⁻¹, hmem χ.1 χ.2⟩ : F))
      ?_) hF
    intro χ χ' hχχ'
    have h1 : (χ.1 : MulAut V) c₀ = (χ'.1 : MulAut V) c₀ := by
      have := congrArg Subtype.val hχχ'
      exact mul_right_cancel this
    have hχ1 := hχA χ.1 χ.2
    have hχ2 := hχA χ'.1 χ'.2
    have hinvA : ∀ a ∈ A, (χ.1 : MulAut V)⁻¹ a = a := by
      intro a ha
      have := congrArg ((χ.1 : MulAut V)⁻¹ : MulAut V) (hχ1 a ha)
      simpa using this.symm
    have hφ : ((χ.1 : MulAut V)⁻¹ * (χ'.1 : MulAut V)) = 1 := by
      apply F3
      · intro θ hθ
        have e1 := hH (χ.1⁻¹ * χ'.1) (H.mul_mem (H.inv_mem χ.1.2) χ'.1.2) θ hθ
        simpa using e1
      · intro a ha
        simp only [MulAut.mul_apply]
        rw [hχ2 a ha, hinvA a ha]
      · simp only [MulAut.mul_apply]
        rw [← h1]
        simp
    have : (χ.1 : MulAut V) = (χ'.1 : MulAut V) := by
      have := congrArg ((χ.1 : MulAut V) * ·) hφ
      simpa using this.symm
    exact Subtype.ext (Subtype.ext this)
  calc Nat.card H = Nat.card (MulAction.stabilizer H x) * (MulAction.orbit H x).ncard := hos.symm
    _ ≤ 16 * 16 := Nat.mul_le_mul hstab horb
    _ = 256 := rfl

end CFSG.EvenSporadicStandard.M24Std
