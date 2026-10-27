module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryBSemilinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherConjDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentForm

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBUnitaryB

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open LinearMap (BilinForm)

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem isometryGroup_eq_orthogonalGroup {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    (B : BilinForm K W) (hsym : B.IsSymm) (h2 : (2 : K) ≠ 0) :
    TauCeti.BilinForm.isometryGroup B =
      TauCeti.QuadraticMap.orthogonalGroup (CatalogueBOrthogonalDescent.originalQuadratic B) := by
  ext g
  rw [CatalogueBOrthogonalDescent.originalQuadratic_isometry_iff B hsym h2 g,
    TauCeti.BilinForm.mem_isometryGroup_iff]

section Fixed

variable (h : UnitaryFieldData p f E) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (τ₀ : V →ₛₗ[h.bar] V)
  (hτ₀ : Function.Bijective τ₀) (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w))

@[expose] def fixedCommutingEquiv :
    FixedCommutingProduct.fixedSubgroup (antiConj h τ₀ hτ₀ hτ₀B) ≃* commutingUnitary B τ₀ where
  toFun g := ⟨(g : sesqUnitaryGroup B),
    ⟨(g : sesqUnitaryGroup B).2, (mem_fixed_unitaryConj h _ _ hτ₀B _).mp g.2⟩⟩
  invFun g := ⟨⟨g, g.2.1⟩, (mem_fixed_unitaryConj h _ _ hτ₀B _).mpr g.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

include hτ₀ hτ₀B in
theorem commutingUnitary_pComponent_quasisimple (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 3 ≤ finrank E V) (hB : B.IsSymm) (hBl : B.SeparatingLeft) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) (ℓ : ℕ) [Fact ℓ.Prime]
    (L : Subgroup (commutingUnitary B τ₀)) (hL : CFSG.IsPComponent ℓ L) :
    CFSG.IsQuasisimple L := by
  have hodd : Odd p := h.prime.odd_of_ne_two hp
  have : Finite E := h.finite
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hK : Odd (Nat.card h.fixedField) := by
    rw [h.card_fixedField]
    exact hodd.pow
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact two_ne_zero_of_odd h hp h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
      (Φ.trans (MulEquiv.subgroupCongr (isometryGroup_eq_orthogonalGroup B' hsym h2)))
      (CatalogueBOrthogonalAssembly.odd_orthogonal_p_components_assembly hK _ hQ
        (by rw [hfinW]; exact hn) ℓ Fact.out) L hL
  · obtain ⟨B', -, halt, hnd, heven, Φ, -⟩ := hB2 hμ1
    have h4 : 4 ≤ finrank h.fixedField (conjFixed h ((b : E) • τ₀)) := by
      rw [hfinW]
      obtain ⟨k, hk⟩ := heven
      omega
    exact CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ Φ
      (fun M hM => ((CatalogueBAlternatingIsometry.odd_symplectic_isometry_p_components B' halt
        hnd h4 hK).2 ℓ Fact.out M hM).2) L hL

end Fixed

theorem odd_unitary_conjugate_semilinear_fixed_p_components (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hn : 3 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (τ₀ : V →ₛₗ[h.bar] V)
    (hτ₀ : Function.Bijective τ₀) (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) :
    (∀ ℓ : ℕ, ℓ.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B)),
        CFSG.IsPComponent ℓ L → CFSG.IsQuasisimple L) ∧
    (∀ ℓ : ℕ, ℓ.Prime →
      ∀ L : Subgroup (projSpecial h B ⊓
        FixedCommutingProduct.fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B) :
          Subgroup (sesqProjUnitary h B)),
        CFSG.IsPComponent ℓ L → CFSG.IsQuasisimple L) := by
  have : Finite E := h.finite
  obtain ⟨-, -, -, -, -, hMnormal, hMab, hsurj, -, -, -, hker, -⟩ :=
    odd_unitary_semilinear_projective_fixed_structure h hp (by omega) τ₀ hτ₀ hτ₀B μ hμ
  have hD : ∀ ℓ : ℕ, ℓ.Prime →
      ∀ L : Subgroup (FixedCommutingProduct.fixedSubgroup (antiProjConj h τ₀ hτ₀ hτ₀B)),
        CFSG.IsPComponent ℓ L → CFSG.IsQuasisimple L := by
    intro ℓ hℓ L hL
    have : Fact ℓ.Prime := ⟨hℓ⟩
    have := hMnormal
    have := hMab
    exact CatalogueBFixedCentralQuotient.pComponent_quasisimple_of_normal_solvable_quotient ℓ
      (antiFixedImage h τ₀ hτ₀ hτ₀B)
      (CatalogueBProjectiveInvolution.pComponent_quasisimple_of_central_surjection ℓ
        (antiFixedProjection h τ₀ hτ₀ hτ₀B) hsurj hker
        (fun J hJ => CatalogueBProjectiveInvolution.pComponent_quasisimple_of_equiv ℓ
          (fixedCommutingEquiv h τ₀ hτ₀ hτ₀B)
          (commutingUnitary_pComponent_quasisimple h τ₀ hτ₀ hτ₀B hp hn hB hBl μ hμ ℓ) J hJ))
      L hL
  refine ⟨hD, fun ℓ hℓ L hL => ?_⟩
  have : Fact ℓ.Prime := ⟨hℓ⟩
  exact inf_pComponent_quasisimple (projSpecial h B) _ ℓ (hD ℓ hℓ) L hL

end CFSG.ComponentClassification.CatalogueBUnitaryB
