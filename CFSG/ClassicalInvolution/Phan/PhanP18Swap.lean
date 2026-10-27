module

public import CFSG.ClassicalInvolution.Phan.PhanP16Witt

public section

namespace CFSG.ClassicalInvolution.PhanP

open QuadraticMap CliffordAlgebra CFSG.LieType.Universal.Spin

section Embed

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polar_isometry {E : Type} [AddCommGroup E] [Module F E] {QE : QuadraticForm F E}
    (α : QE →qᵢ Q) (x y : E) : polar Q (α x) (α y) = polar QE x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, α.map_app, α.map_app, α.map_app]

theorem isometry_injective_of_nondegenerate [Invertible (2 : F)]
    {E : Type} [AddCommGroup E] [Module F E] {QE : QuadraticForm F E}
    (hQE : QE.Nondegenerate) (α : QE →qᵢ Q) : Function.Injective α := by
  show Function.Injective α.toLinearMap
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hx0 : α x = 0 := hx
  refine (QuadraticMap.nondegenerate_polar_iff.mpr hQE).1 x fun y => ?_
  rw [QuadraticMap.polarBilin_apply_apply, ← polar_isometry α, hx0, QuadraticMap.polar_zero_left]

@[expose] noncomputable def sumEmb (A : Submodule F V) (f : A →ₗ[F] V) (hf : ∀ a, Q (f a) = Q a)
    (hperp : ∀ a a' : A, polar Q (f a) a' = 0) :
    ((Q.restrict A).prod (Q.restrict A)) →qᵢ Q where
  toLinearMap := A.subtype.coprod f
  map_app' x := by
    change Q ((x.1 : V) + f x.2) = Q x.1 + Q x.2
    rw [QuadraticMap.map_add Q, hf, QuadraticMap.polar_comm, hperp]
    simp

end Embed

section Swap

variable {F : Type} [Field F] [Finite F] [Invertible (2 : F)] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Nontrivial V] {Q : QuadraticForm F V}

theorem exists_spin_fix_map (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate)
    {A : Submodule F V} (hA : (Q.restrict A).Nondegenerate)
    (hV : 2 * Module.finrank F A + 2 ≤ Module.finrank F V) (ρ h : spinGroup Q)
    (hρ : ∀ a ∈ A, ∀ a' ∈ A, polar Q (spinAction Q ρ a) a' = 0)
    (hh : ∀ a ∈ A, ∀ a' ∈ A, polar Q (spinAction Q h a) a' = 0) :
    ∃ y : spinGroup Q, (∀ a ∈ A, spinAction Q y a = a) ∧
      ∀ a ∈ A, spinAction Q y (spinAction Q ρ a) = spinAction Q h a := by
  let fρ : A →ₗ[F] V := (spinAction Q ρ).toLinearMap ∘ₗ A.subtype
  let fh : A →ₗ[F] V := (spinAction Q h).toLinearMap ∘ₗ A.subtype
  have hfρ : ∀ a : A, Q (fρ a) = Q a := fun a => map_spinAction Q ρ a
  have hfh : ∀ a : A, Q (fh a) = Q a := fun a => map_spinAction Q h a
  obtain ⟨α, hαdef⟩ : ∃ α : ((Q.restrict A).prod (Q.restrict A)) →qᵢ Q,
      ∀ a a' : A, α (a, a') = (a : V) + fρ a' :=
    ⟨sumEmb A fρ hfρ (fun a a' => hρ a a.2 a' a'.2), fun a a' => rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ((Q.restrict A).prod (Q.restrict A)) →qᵢ Q,
      ∀ a a' : A, β (a, a') = (a : V) + fh a' :=
    ⟨sumEmb A fh hfh (fun a a' => hh a a.2 a' a'.2), fun a a' => rfl⟩
  have hQE : ((Q.restrict A).prod (Q.restrict A)).Nondegenerate := hA.prod hA
  have hα := isometry_injective_of_nondegenerate hQE α
  have hβ := isometry_injective_of_nondegenerate hQE β
  have hreg := nondegenerate_range α hα hQE
  have hdim : 2 ≤ Module.finrank F (LinearMap.BilinForm.orthogonal Q.polarBilin
      (LinearMap.range α.toLinearMap)) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hreg.isCompl_orthogonal
    have h4 : Module.finrank F (LinearMap.range α.toLinearMap) = 2 * Module.finrank F A := by
      rw [LinearMap.finrank_range_of_inj hα, Module.finrank_prod]
      ring
    omega
  obtain ⟨y, hy⟩ := exists_spin_extend hodd hQ α β hα hβ hreg hdim
  refine ⟨y, fun a ha => ?_, fun a ha => ?_⟩
  · have := hy (⟨a, ha⟩, 0)
    rw [hαdef, hβdef] at this
    simpa using this
  · have := hy (0, ⟨a, ha⟩)
    rw [hαdef, hβdef] at this
    simpa [fρ, fh] using this

end Swap

end CFSG.ClassicalInvolution.PhanP
