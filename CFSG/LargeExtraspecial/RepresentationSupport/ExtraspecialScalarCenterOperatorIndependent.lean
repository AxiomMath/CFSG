module

public import CFSG.Foundations.Basic
public import CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialScalarCenterOperatorIndependent

open Subgroup

open scoped commutatorElement

theorem linearIndependent {F : Type*} [Field F]
    {W : Type*} [AddCommGroup W] [Module F W] [Nontrivial W]
    {q : ℕ} (hq : q.Prime)
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup q E)
    (σ : Representation F E W) (χ : Subgroup.center E →* Fˣ)
    (hχ : Function.Injective χ)
    (hscalar : ∀ z : Subgroup.center E, σ (z : E) = (χ z : F) • (LinearMap.id : W →ₗ[F] W))
    (r : E ⧸ Subgroup.center E → E)
    (hr : ∀ a, (QuotientGroup.mk (r a) : E ⧸ Subgroup.center E) = a) :
    LinearIndependent F (fun a : E ⧸ Subgroup.center E => σ (r a)) := by
  have comm_mul_of_central {g h a : E} (hc : ⁅h, a⁆ ∈ Subgroup.center E) :
      ⁅g * h, a⁆ = ⁅g, a⁆ * ⁅h, a⁆ := by
    have h1 := Subgroup.mem_center_iff.1 hc g
    simp only [commutatorElement_def] at h1 ⊢
    calc g * h * a * (g * h)⁻¹ * a⁻¹
        = g * (h * a * h⁻¹ * a⁻¹) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) := by group
      _ = (g * (h * a * h⁻¹ * a⁻¹)) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) := rfl
      _ = ((h * a * h⁻¹ * a⁻¹) * g) * g⁻¹ * (g * a * g⁻¹ * a⁻¹) := by rw [← h1]
      _ = (g * a * g⁻¹ * a⁻¹) * (h * a * h⁻¹ * a⁻¹) := by
          have h2 : ((h * a * h⁻¹ * a⁻¹) * g) * g⁻¹ * (g * a * g⁻¹ * a⁻¹)
              = (h * a * h⁻¹ * a⁻¹) * (g * a * g⁻¹ * a⁻¹) := by group
          rw [h2]
          have h3 := Subgroup.mem_center_iff.1 hc (g * a * g⁻¹ * a⁻¹)
          exact h3.symm
  have comm_conj {g a : E} : g * a * g⁻¹ = ⁅g, a⁆ * a := by
    simp [commutatorElement_def, mul_assoc]
  classical
  obtain ⟨-, hcomm, -, -⟩ := hE
  have hcm : ∀ g a : E, ⁅g, a⁆ ∈ Subgroup.center E := by
    intro g a
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top a)
  let c : E → E → Subgroup.center E := fun g a => ⟨⁅g, a⁆, hcm g a⟩
  let τ : Representation F E (Module.End F W) :=
    { toFun := fun g => (LinearMap.mulLeft F (σ g)).comp (LinearMap.mulRight F (σ g⁻¹))
      map_one' := by ext; simp
      map_mul' := by intro g h; ext T; simp [mul_assoc] }
  let χ' : (E ⧸ Subgroup.center E) → (E →* Fˣ) := fun a =>
    { toFun := fun g => χ (c g (r a))
      map_one' := by
        have : c 1 (r a) = 1 := Subtype.ext (by simp [c])
        simp [this]
      map_mul' := by
        intro g h
        rw [← map_mul]
        congr 1
        exact Subtype.ext (comm_mul_of_central (hcm h (r a))) }
  refine CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent.linearIndependent τ χ' _ ?_ ?_ ?_
  · intro a h0
    have h1 : σ (r a) * σ (r a)⁻¹ = 1 := by rw [← map_mul]; simp
    change σ (r a) = 0 at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro a g
    show σ g * σ (r a) * σ g⁻¹ = (χ (c g (r a)) : F) • σ (r a)
    rw [← map_mul, ← map_mul, comm_conj, map_mul]
    have := hscalar (c g (r a))
    simp only [c] at this
    rw [this]
    ext w
    simp [c]
  · intro a a' h
    have key : ∀ g, ⁅(g : E), r a⁆ = ⁅g, r a'⁆ := by
      intro g
      have h1 : χ (c g (r a)) = χ (c g (r a')) := congrArg (fun f : E →* Fˣ => f g) h
      exact congrArg Subtype.val (hχ h1)
    have hcen : (r a)⁻¹ * r a' ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro g
      have e1 := comm_conj (g := g) (a := r a)
      have e2 := comm_conj (g := g) (a := r a')
      rw [key g] at e1
      have : g * ((r a)⁻¹ * r a') * g⁻¹ = (r a)⁻¹ * r a' := by
        have e3 : g * (r a)⁻¹ * g⁻¹ = (g * r a * g⁻¹)⁻¹ := by group
        calc g * ((r a)⁻¹ * r a') * g⁻¹ = (g * (r a)⁻¹ * g⁻¹) * (g * r a' * g⁻¹) := by group
          _ = (⁅g, r a'⁆ * r a)⁻¹ * (⁅g, r a'⁆ * r a') := by rw [e3, e1, e2]
          _ = _ := by rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      calc g * ((r a)⁻¹ * r a') = (g * ((r a)⁻¹ * r a') * g⁻¹) * g := by group
        _ = _ := by rw [this]
    have := (QuotientGroup.eq (a := r a) (b := r a')).2 hcen
    rw [hr, hr] at this
    exact this

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialScalarCenterOperatorIndependent
