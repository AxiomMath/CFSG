module

public import CFSG.Foundations.Basic
public import CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent

public section

namespace CFSG.LargeExtraspecial

namespace RepresentationSupport

namespace ExtraspecialTwoOperatorIndependent

open Subgroup

open scoped commutatorElement

section aux

variable {E : Type*} [Group E]

private theorem comm_mul_of_central {g h a : E} (hc : ⁅h, a⁆ ∈ Subgroup.center E) :
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

private theorem comm_conj {g a : E} : g * a * g⁻¹ = ⁅g, a⁆ * a := by
  simp [commutatorElement_def, mul_assoc]

end aux

section main

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]
  {E : Type*} [Group E]

private noncomputable def sgn (F : Type*) [Field F] (c : E) : Fˣ := by
  classical exact if c = 1 then 1 else -1

private theorem sgn_mul {z : E} (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hZ : ∀ c ∈ Subgroup.center E, c = 1 ∨ c = z) {c d : E}
    (hc : c ∈ Subgroup.center E) (hd : d ∈ Subgroup.center E) :
    sgn F (c * d) = sgn F c * sgn F d := by
  rcases hZ c hc with rfl | rfl <;> rcases hZ d hd with rfl | rfl <;>
    simp [sgn, hz1, hzz]

theorem linearIndependent {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module F W] [Nontrivial W]
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup 2 E)
    (σ : Representation F E W) (z : E) (hz : z ∈ Subgroup.center E) (hz1 : z ≠ 1)
    (hzScalar : σ z = -LinearMap.id)
    (r : E ⧸ Subgroup.center E → E)
    (hr : ∀ q, (QuotientGroup.mk (r q) : E ⧸ Subgroup.center E) = q) :
    LinearIndependent F (fun q : E ⧸ Subgroup.center E => σ (r q)) := by
  classical
  obtain ⟨-, hcomm, -, hcard⟩ := hE
  have hcm : ∀ g a : E, ⁅g, a⁆ ∈ Subgroup.center E := by
    intro g a
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top a)
  have hZ : ∀ c ∈ Subgroup.center E, c = 1 ∨ c = z := by
    intro c hc
    by_contra hcon
    push Not at hcon
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (⟨z, hz⟩ : Subgroup.center E)).1 hcard
    have h1 : (⟨c, hc⟩ : Subgroup.center E) = y :=
      hy _ (fun h => hcon.2 (congrArg Subtype.val h))
    have h2 : (1 : Subgroup.center E) = y := hy _ (fun h => hz1 (congrArg Subtype.val h).symm)
    exact hcon.1 (congrArg Subtype.val (h1.trans h2.symm))
  have hzz : z * z = 1 := by
    have hm : z * z ∈ Subgroup.center E := Subgroup.mul_mem _ hz hz
    rcases hZ _ hm with h | h
    · exact h
    · exfalso; apply hz1; simpa using h
  have hneg : (-1 : Fˣ) ≠ 1 := by
    intro h
    apply hF
    have := congrArg (fun u : Fˣ => (u : F)) h
    simp at this
    linear_combination -this
  have hσc : ∀ c ∈ Subgroup.center E, σ c = (sgn F c : F) • (LinearMap.id : W →ₗ[F] W) := by
    intro c hc
    rcases hZ c hc with rfl | rfl
    · simp [sgn, Module.End.one_eq_id]
    · simp [sgn, hz1, hzScalar]
  let τ : Representation F E (Module.End F W) :=
    { toFun := fun g => (LinearMap.mulLeft F (σ g)).comp (LinearMap.mulRight F (σ g⁻¹))
      map_one' := by ext; simp
      map_mul' := by intro g h; ext T; simp [mul_assoc] }
  let χ : (E ⧸ Subgroup.center E) → (E →* Fˣ) := fun q =>
    { toFun := fun g => sgn F ⁅g, r q⁆
      map_one' := by simp [sgn]
      map_mul' := by
        intro g h
        rw [comm_mul_of_central (hcm h (r q))]
        exact sgn_mul hz1 hzz hZ (hcm g _) (hcm h _) }
  refine CFSG.LinearAlgebra.CoprimeActions.DistinctCharacterEigenvectorIndependent.linearIndependent τ χ _ ?_ ?_ ?_
  · intro q h0
    have h1 : σ (r q) * σ (r q)⁻¹ = 1 := by rw [← map_mul]; simp
    change σ (r q) = 0 at h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro q g
    show σ g * σ (r q) * σ g⁻¹ = (sgn F ⁅g, r q⁆ : F) • σ (r q)
    rw [← map_mul, ← map_mul, comm_conj, map_mul, hσc _ (hcm g _)]
    ext w
    simp
  · intro q q' h
    have key : ∀ g, ⁅(g : E), r q⁆ = ⁅g, r q'⁆ := by
      intro g
      have h1 : sgn F ⁅g, r q⁆ = sgn F ⁅g, r q'⁆ := congrArg (fun f : E →* Fˣ => f g) h
      rcases hZ _ (hcm g (r q)) with h2 | h2 <;> rcases hZ _ (hcm g (r q')) with h3 | h3 <;>
        rw [h2, h3] at h1 ⊢ <;> simp [sgn, hz1, hneg, hneg.symm] at h1 ⊢
    have hcen : (r q)⁻¹ * r q' ∈ Subgroup.center E := by
      rw [Subgroup.mem_center_iff]
      intro g
      have e1 := comm_conj (g := g) (a := r q)
      have e2 := comm_conj (g := g) (a := r q')
      rw [key g] at e1
      have : g * ((r q)⁻¹ * r q') * g⁻¹ = (r q)⁻¹ * r q' := by
        have e3 : g * (r q)⁻¹ * g⁻¹ = (g * r q * g⁻¹)⁻¹ := by group
        calc g * ((r q)⁻¹ * r q') * g⁻¹ = (g * (r q)⁻¹ * g⁻¹) * (g * r q' * g⁻¹) := by group
          _ = (⁅g, r q'⁆ * r q)⁻¹ * (⁅g, r q'⁆ * r q') := by rw [e3, e1, e2]
          _ = _ := by rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
      calc g * ((r q)⁻¹ * r q') = (g * ((r q)⁻¹ * r q') * g⁻¹) * g := by group
        _ = _ := by rw [this]
    have := (QuotientGroup.eq (a := r q) (b := r q')).2 hcen
    rw [hr, hr] at this
    exact this

end main

end ExtraspecialTwoOperatorIndependent

end RepresentationSupport

end CFSG.LargeExtraspecial
