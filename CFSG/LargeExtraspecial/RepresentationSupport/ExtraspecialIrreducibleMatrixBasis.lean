module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleRepresentationMatrixSpan
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialScalarCenterOperatorIndependent

public section

namespace CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialIrreducibleMatrixBasis

theorem exists_basis {F : Type*} [Field F] [IsAlgClosed F]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    {q : ℕ} (hq : q.Prime)
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup q E)
    (σ : Representation F E W) (hσ : σ.IsIrreducible)
    (χ : Subgroup.center E →* Fˣ) (hχ : Function.Injective χ)
    (hscalar : ∀ z : Subgroup.center E, σ (z : E) = (χ z : F) • (LinearMap.id : W →ₗ[F] W))
    (r : E ⧸ Subgroup.center E → E)
    (hr : ∀ a, (QuotientGroup.mk (r a) : E ⧸ Subgroup.center E) = a) :
    ∃ b : Module.Basis (E ⧸ Subgroup.center E) F (Module.End F W), ∀ a, b a = σ (r a) := by
  have hli := ExtraspecialScalarCenterOperatorIndependent.linearIndependent hq hE σ χ hχ
    hscalar r hr
  have hspan := CFSG.LinearAlgebra.CoprimeActions.IrreducibleRepresentationMatrixSpan.span_eq_top σ hσ
  refine ⟨Module.Basis.mk hli ?_, fun a => by rw [Module.Basis.coe_mk]⟩
  rw [← hspan]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  have hz : (r (QuotientGroup.mk g))⁻¹ * g ∈ Subgroup.center E := by
    rw [← QuotientGroup.eq, hr]
  have hg : g = r (QuotientGroup.mk g) * ((r (QuotientGroup.mk g))⁻¹ * g) := by group
  have h2 := hscalar ⟨_, hz⟩
  have : σ g = (χ ⟨_, hz⟩ : F) • σ (r (QuotientGroup.mk g)) := by
    conv_lhs => rw [hg]
    rw [map_mul]
    simp only at h2
    rw [h2]
    ext w
    simp
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem dimension_eq {F : Type*} [Field F] [IsAlgClosed F]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] [Nontrivial W]
    {q : ℕ} (hq : q.Prime)
    {E : Type*} [Group E] [Finite E] (hE : CFSG.IsExtraspecialPGroup q E)
    (σ : Representation F E W) (hσ : σ.IsIrreducible)
    (χ : Subgroup.center E →* Fˣ) (hχ : Function.Injective χ)
    (hscalar : ∀ z : Subgroup.center E, σ (z : E) = (χ z : F) • (LinearMap.id : W →ₗ[F] W))
    (r : E ⧸ Subgroup.center E → E)
    (hr : ∀ a, (QuotientGroup.mk (r a) : E ⧸ Subgroup.center E) = a)
    {d : ℕ} (hcard : Nat.card E = q ^ (1 + 2 * d)) :
    Module.finrank F W = q ^ d := by
  obtain ⟨b, -⟩ := exists_basis hq hE σ hσ χ hχ hscalar r hr
  have h1 : Module.finrank F (Module.End F W) = Nat.card (E ⧸ Subgroup.center E) := by
    rw [Module.finrank_eq_nat_card_basis b]
  have h2 : Nat.card E = Nat.card (E ⧸ Subgroup.center E) * Nat.card (Subgroup.center E) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card (Subgroup.center E) = q := hE.2.2.2
  have hqpos : 0 < q := hq.pos
  have h4 : Nat.card (E ⧸ Subgroup.center E) = q ^ (2 * d) := by
    rw [hcard, h3, pow_add, pow_one] at h2
    have : q ^ (2 * d) * q = Nat.card (E ⧸ Subgroup.center E) * q := by
      rw [mul_comm, mul_comm (Nat.card _)] at h2
      linarith
    exact (Nat.eq_of_mul_eq_mul_right hqpos this).symm
  have h5 : Module.finrank F (Module.End F W) = Module.finrank F W * Module.finrank F W := by
    exact Module.finrank_linearMap F F W W
  rw [h1, h4] at h5
  have h6 : (Module.finrank F W) ^ 2 = (q ^ d) ^ 2 := by
    rw [sq, ← pow_mul, mul_comm d 2, ← h5]
  exact Nat.pow_left_injective (by norm_num) h6

end CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialIrreducibleMatrixBasis
