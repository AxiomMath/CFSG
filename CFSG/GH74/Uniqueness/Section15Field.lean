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
public import Mathlib.RingTheory.LittleWedderburn
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

namespace CFSG.GH74.Uniqueness.Section15Field

open Subgroup

variable {A : Type} [Group A] [Finite A]

theorem exists_field_of_regular (hcomm : ∀ a b : A, a * b = b * a) (𝒦 : Subgroup (MulAut A))
    (hK : ∀ a ∈ 𝒦, ∀ b ∈ 𝒦, a * b = b * a)
    (htrans : ∀ x y : A, x ≠ 1 → y ≠ 1 → ∃ k ∈ 𝒦, k x = y) (hnt : ∃ x : A, x ≠ 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : A ≃ F), Nat.card F = Nat.card A ∧ e 1 = 0 ∧
      (∀ a : Fˣ, ∃ k ∈ 𝒦, ∀ x, e (k x) = a * e x) ∧
      (∀ δ : MulAut A, (∀ k ∈ 𝒦, δ * k * δ⁻¹ ∈ 𝒦) → (∀ k ∈ 𝒦, δ⁻¹ * k * δ ∈ 𝒦) →
        ∃ (a : Fˣ) (σ : F ≃+* F), ∀ x, e (δ x) = a * σ (e x)) := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  let toEnd : MulAut A → AddMonoid.End (Additive A) := fun k =>
    AddMonoidHom.mk' (fun x => Additive.ofMul (k (Additive.toMul x))) (fun x y => by
      simp [map_mul])
  have toEnd_apply : ∀ k x, toEnd k x = Additive.ofMul (k (Additive.toMul x)) := fun k x => rfl
  have toEnd_mul : ∀ k l, toEnd (k * l) = toEnd k * toEnd l := fun k l =>
    DFunLike.ext _ _ fun x => rfl
  have toEnd_one : toEnd 1 = 1 := DFunLike.ext _ _ fun x => rfl
  let gens : Set (AddMonoid.End (Additive A)) := {f | ∃ k ∈ 𝒦, toEnd k = f}
  let C : Subring (AddMonoid.End (Additive A)) := Subring.centralizer gens
  have hgenC : ∀ k ∈ 𝒦, toEnd k ∈ C := by
    intro k hk
    rw [Subring.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    rw [← toEnd_mul, ← toEnd_mul, hK l hl k hk]
  have hcommC : ∀ φ ∈ C, ∀ k ∈ 𝒦, toEnd k * φ = φ * toEnd k := fun φ hφ k hk =>
    (Subring.mem_centralizer_iff.mp hφ) (toEnd k) ⟨k, hk, rfl⟩
  obtain ⟨x₀, hx₀⟩ := hnt
  let a₀ : Additive A := Additive.ofMul x₀
  have hne : ∀ x : Additive A, x ≠ 0 ↔ Additive.toMul x ≠ 1 := fun x => by
    constructor
    · intro hx h
      exact hx (by rw [← ofMul_toMul x, h]; rfl)
    · intro hx h
      exact hx (by rw [h]; rfl)
  have ha₀ : a₀ ≠ 0 := (hne a₀).mpr hx₀
  have htrans' : ∀ x y : Additive A, x ≠ 0 → y ≠ 0 → ∃ k ∈ 𝒦, toEnd k x = y := by
    intro x y hx hy
    obtain ⟨k, hk, hkxy⟩ := htrans (Additive.toMul x) (Additive.toMul y) ((hne x).mp hx)
      ((hne y).mp hy)
    exact ⟨k, hk, by rw [toEnd_apply, hkxy]; rfl⟩
  have hinj : ∀ φ ∈ C, φ ≠ 0 → ∀ x, φ x = 0 → x = 0 := by
    intro φ hφ hφ0 x hx
    by_contra hx0
    apply hφ0
    refine DFunLike.ext _ _ fun y => ?_
    by_cases hy : y = 0
    · rw [hy, map_zero]
      rfl
    · obtain ⟨k, hk, hky⟩ := htrans' x y hx0 hy
      have h1 : toEnd k (φ x) = φ (toEnd k x) := by
        have := congrArg (fun f : AddMonoid.End (Additive A) => f x) (hcommC φ hφ k hk)
        exact this
      rw [hky, hx, map_zero] at h1
      rw [← h1]
      rfl
  let ev : C → Additive A := fun φ => (φ : AddMonoid.End (Additive A)) a₀
  have ev_inj : Function.Injective ev := by
    intro φ ψ h
    by_contra hne'
    have hχ : (φ - ψ : C) ≠ 0 := sub_ne_zero.mpr hne'
    have h1 : ((φ - ψ : C) : AddMonoid.End (Additive A)) a₀ = 0 := by
      have h2 : ((φ - ψ : C) : AddMonoid.End (Additive A)) a₀ =
          (φ : AddMonoid.End (Additive A)) a₀ - (ψ : AddMonoid.End (Additive A)) a₀ := rfl
      rw [h2]
      have h3 : (φ : AddMonoid.End (Additive A)) a₀ = (ψ : AddMonoid.End (Additive A)) a₀ := h
      rw [h3]
      exact sub_self _
    exact ha₀ (hinj (φ - ψ : C) (φ - ψ).2 (fun h0 => hχ (Subtype.ext h0)) a₀ h1)
  have ev_surj : Function.Surjective ev := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by rw [hy]; rfl⟩
    · obtain ⟨k, hk, hka⟩ := htrans' a₀ y ha₀ hy
      exact ⟨⟨toEnd k, hgenC k hk⟩, hka⟩
  let eC : C ≃ Additive A := Equiv.ofBijective ev ⟨ev_inj, ev_surj⟩
  have hNT : Nontrivial C := ⟨⟨0, 1, fun h => by
    have h1 := congrArg ev h
    exact ha₀ h1.symm⟩⟩
  have hNZD : NoZeroDivisors C := ⟨fun {a b} hab => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      refine Subtype.ext (DFunLike.ext _ _ fun y => ?_)
      have h1 : (a : AddMonoid.End (Additive A)) ((b : AddMonoid.End (Additive A)) y) = 0 := by
        have := congrArg (fun c : C => (c : AddMonoid.End (Additive A)) y) hab
        exact this
      have h2 := hinj a a.2 (fun h0 => ha (Subtype.ext h0)) _ h1
      exact h2⟩
  have hFin : Finite C := Finite.of_equiv _ eC.symm
  have hDom : IsDomain C := NoZeroDivisors.to_isDomain C
  let fieldC : Field C := (Finite.isDomain_to_isField C).toField
  let e : A ≃ C := (Additive.ofMul : A ≃ Additive A).trans eC.symm
  have he_ev : ∀ x, ev (e x) = Additive.ofMul x := fun x => eC.apply_symm_apply _
  refine ⟨C, fieldC, hFin, e, ?_, ?_, ?_, ?_⟩
  · exact Nat.card_congr (eC.trans Additive.toMul)
  · apply eC.injective
    rw [show eC (e 1) = Additive.ofMul 1 from eC.apply_symm_apply _]
    rfl
  ·
    intro a
    have ha0 : (a : C) ≠ 0 := a.ne_zero
    have hy : ev (a : C) ≠ 0 := fun h =>
      ha₀ (hinj (a : C) (a : C).2 (fun h0 => ha0 (Subtype.ext h0)) a₀ h)
    obtain ⟨k, hk, hka⟩ := htrans' a₀ (ev (a : C)) ha₀ hy
    have hak : (a : C) = ⟨toEnd k, hgenC k hk⟩ := ev_inj hka.symm
    refine ⟨k, hk, fun x => ?_⟩
    apply eC.injective
    have h1 : eC (e (k x)) = Additive.ofMul (k x) := eC.apply_symm_apply _
    rw [h1]
    show Additive.ofMul (k x) = ev ((a : C) * e x)
    have h2 : ev ((a : C) * e x) =
        ((a : C) : AddMonoid.End (Additive A)) (ev (e x)) := rfl
    rw [h2, he_ev, hak]
    rfl
  ·
    intro δ hδ hδ'
    have hδδ : toEnd δ * toEnd δ⁻¹ = 1 := by rw [← toEnd_mul, mul_inv_cancel, toEnd_one]
    have hδδ' : toEnd δ⁻¹ * toEnd δ = 1 := by rw [← toEnd_mul, inv_mul_cancel, toEnd_one]
    have hconj : ∀ δ : MulAut A, (∀ k ∈ 𝒦, δ⁻¹ * k * δ ∈ 𝒦) → ∀ φ ∈ C,
        toEnd δ * φ * toEnd δ⁻¹ ∈ C := by
      intro δ hδ' φ hφ
      rw [Subring.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      have hk' := hδ' k hk
      have e1 : toEnd k * toEnd δ = toEnd δ * toEnd (δ⁻¹ * k * δ) := by
        rw [← toEnd_mul, ← toEnd_mul]
        congr 1
        group
      have e2 : toEnd (δ⁻¹ * k * δ) * toEnd δ⁻¹ = toEnd δ⁻¹ * toEnd k := by
        rw [← toEnd_mul, ← toEnd_mul]
        congr 1
        group
      have h3 := hcommC φ hφ _ hk'
      calc toEnd k * (toEnd δ * φ * toEnd δ⁻¹)
          = (toEnd k * toEnd δ) * φ * toEnd δ⁻¹ := by simp only [mul_assoc]
        _ = toEnd δ * (toEnd (δ⁻¹ * k * δ) * φ) * toEnd δ⁻¹ := by
            rw [e1]; simp only [mul_assoc]
        _ = toEnd δ * (φ * toEnd (δ⁻¹ * k * δ)) * toEnd δ⁻¹ := by rw [h3]
        _ = toEnd δ * φ * (toEnd (δ⁻¹ * k * δ) * toEnd δ⁻¹) := by simp only [mul_assoc]
        _ = toEnd δ * φ * toEnd δ⁻¹ * toEnd k := by rw [e2]; simp only [mul_assoc]
    have hσmem : ∀ φ : C, toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹ ∈ C :=
      fun φ => hconj δ hδ' φ φ.2
    have hσmem' : ∀ φ : C, toEnd δ⁻¹ * (φ : AddMonoid.End (Additive A)) * toEnd δ ∈ C := by
      intro φ
      have h1 := hconj δ⁻¹ (by simpa using hδ) φ φ.2
      rwa [inv_inv] at h1
    let σ : C ≃+* C :=
      { toFun := fun φ => ⟨toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹, hσmem φ⟩
        invFun := fun φ => ⟨toEnd δ⁻¹ * (φ : AddMonoid.End (Additive A)) * toEnd δ, hσmem' φ⟩
        left_inv := fun φ => Subtype.ext (by
          show toEnd δ⁻¹ * (toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹) * toEnd δ = φ
          calc toEnd δ⁻¹ * (toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹) * toEnd δ
              = (toEnd δ⁻¹ * toEnd δ) * (φ : AddMonoid.End (Additive A)) *
                  (toEnd δ⁻¹ * toEnd δ) := by simp only [mul_assoc]
            _ = φ := by rw [hδδ', one_mul, mul_one])
        right_inv := fun φ => Subtype.ext (by
          show toEnd δ * (toEnd δ⁻¹ * (φ : AddMonoid.End (Additive A)) * toEnd δ) * toEnd δ⁻¹ = φ
          calc toEnd δ * (toEnd δ⁻¹ * (φ : AddMonoid.End (Additive A)) * toEnd δ) * toEnd δ⁻¹
              = (toEnd δ * toEnd δ⁻¹) * (φ : AddMonoid.End (Additive A)) *
                  (toEnd δ * toEnd δ⁻¹) := by simp only [mul_assoc]
            _ = φ := by rw [hδδ, one_mul, mul_one])
        map_mul' := fun φ ψ => Subtype.ext (by
          show toEnd δ * ((φ : AddMonoid.End (Additive A)) * (ψ : AddMonoid.End (Additive A))) *
              toEnd δ⁻¹ = (toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹) *
              (toEnd δ * (ψ : AddMonoid.End (Additive A)) * toEnd δ⁻¹)
          calc toEnd δ * ((φ : AddMonoid.End (Additive A)) * (ψ : AddMonoid.End (Additive A))) *
              toEnd δ⁻¹
              = toEnd δ * (φ : AddMonoid.End (Additive A)) * 1 *
                  (ψ : AddMonoid.End (Additive A)) * toEnd δ⁻¹ := by
                rw [mul_one]; simp only [mul_assoc]
            _ = toEnd δ * (φ : AddMonoid.End (Additive A)) * (toEnd δ⁻¹ * toEnd δ) *
                  (ψ : AddMonoid.End (Additive A)) * toEnd δ⁻¹ := by rw [hδδ']
            _ = (toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹) *
                (toEnd δ * (ψ : AddMonoid.End (Additive A)) * toEnd δ⁻¹) := by
                simp only [mul_assoc])
        map_add' := fun φ ψ => Subtype.ext (by
          show toEnd δ * ((φ : AddMonoid.End (Additive A)) + (ψ : AddMonoid.End (Additive A))) *
              toEnd δ⁻¹ = toEnd δ * (φ : AddMonoid.End (Additive A)) * toEnd δ⁻¹ +
              toEnd δ * (ψ : AddMonoid.End (Additive A)) * toEnd δ⁻¹
          rw [mul_add, add_mul]) }
    have h3 : toEnd δ⁻¹ (toEnd δ a₀) = a₀ := by
      have := congrArg (fun f : AddMonoid.End (Additive A) => f a₀) hδδ'
      exact this
    let b : C := eC.symm (toEnd δ a₀)
    have hbev : ev b = toEnd δ a₀ := eC.apply_symm_apply _
    have hb : b ≠ 0 := by
      intro h0
      have h2 : ev b = 0 := by rw [h0]; rfl
      rw [h2] at hbev
      rw [← hbev, map_zero] at h3
      exact ha₀ h3.symm
    refine ⟨Units.mk0 b hb, σ, fun x => ?_⟩
    apply eC.injective
    have h1 : eC (e (δ x)) = Additive.ofMul (δ x) := eC.apply_symm_apply _
    rw [h1]
    show Additive.ofMul (δ x) = ev (b * σ (e x))
    rw [mul_comm b (σ (e x))]
    have h2 : ev (σ (e x) * b) =
        ((σ (e x) : C) : AddMonoid.End (Additive A)) (ev b) := rfl
    rw [h2, hbev]
    show _ = (toEnd δ * (e x : AddMonoid.End (Additive A)) * toEnd δ⁻¹) (toEnd δ a₀)
    show _ = toEnd δ ((e x : AddMonoid.End (Additive A)) (toEnd δ⁻¹ (toEnd δ a₀)))
    rw [h3]
    have hφ : (e x : AddMonoid.End (Additive A)) a₀ = Additive.ofMul x := he_ev x
    rw [hφ]
    rfl

end CFSG.GH74.Uniqueness.Section15Field
