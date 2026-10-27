module

public import CFSG.LieType.AlgebraicGroups.ClosedOrbitCone
public import CFSG.LieType.AlgebraicGroups.ConeIncidence

public noncomputable section

open WithConv TauCeti.Comodule

namespace CFSG.LieType.AlgebraicGroups.ClosedCone

universe u v w

variable {k : Type u} [Field k] {H : Type v} [CommRing H] [HopfAlgebra k H]
variable {W : Type w} [AddCommGroup W] [Module k W] [TauCeti.Comodule k H W]

theorem exists_ideal_forall_iff_exists_inv_mul_mem [IsAlgClosed k] [FiniteDimensional k W]
    {w₀ : W} (hw₀ : w₀ ≠ 0) (hX : IsZariskiClosed k (orbitCone k H w₀))
    (B : Set (WithConv (H →ₐ[k] k)))
    (hB : ∀ g, g ∈ B ↔ basePointsRepresentation (H := H) W g w₀ ∈ k ∙ w₀)
    (τ : WithConv (H →ₐ[k] k) → WithConv (H →ₐ[k] k)) (F : W →ₗ[k] W)
    (hF : ∀ x v, F (basePointsRepresentation (H := H) W x v) =
      basePointsRepresentation (H := H) W (τ x) (F v))
    (hFw₀ : F w₀ ≠ 0) (hFw₀' : F w₀ ∈ k ∙ w₀) :
    ∃ J : Ideal H, ∀ z : WithConv (H →ₐ[k] k), (∀ a ∈ J, z.ofConv a = 0) ↔
      ∃ x, x⁻¹ * z * τ x ∈ B := by
  have hXc : IsCone k (orbitCone k H w₀) := by
    rintro c _ ⟨g, d, rfl⟩
    exact ⟨g, c * d, by rw [smul_smul]⟩
  obtain ⟨J, hJ⟩ := exists_ideal_forall_iff_exists_apply_mem_span (H := H) hX hXc F
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hFw₀'
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hFw₀ (by rw [← hc, zero_smul])
  have hinv : ∀ (x : WithConv (H →ₐ[k] k)) (v : W),
      basePointsRepresentation (H := H) W x⁻¹ (basePointsRepresentation (H := H) W x v) = v :=
    fun x v => by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hkey : ∀ z x, x⁻¹ * z * τ x ∈ B ↔
      basePointsRepresentation (H := H) W z (F (basePointsRepresentation (H := H) W x w₀)) ∈
        k ∙ basePointsRepresentation (H := H) W x w₀ := by
    intro z x
    have hτ : basePointsRepresentation (H := H) W (τ x) w₀ =
        c⁻¹ • F (basePointsRepresentation (H := H) W x w₀) := by
      rw [hF x w₀, ← hc, map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [hB, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hτ, map_smul,
      map_smul, Submodule.smul_mem_iff _ (inv_ne_zero hc0)]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
      refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
      have := congrArg (basePointsRepresentation (H := H) W x) ha
      rwa [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] at this
    · intro h
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
      exact Submodule.mem_span_singleton.mpr ⟨a, by rw [← ha, map_smul, hinv]⟩
  refine ⟨J, fun z => (hJ z).trans ⟨?_, ?_⟩⟩
  · rintro ⟨v, ⟨x, d, rfl⟩, hv0, hzv⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hv0 (zero_smul _ _)
    refine ⟨x, (hkey z x).mpr ?_⟩
    rw [map_smul, map_smul, Submodule.span_singleton_smul_eq (IsUnit.mk0 d hd0)] at hzv
    exact (Submodule.smul_mem_iff _ hd0).mp hzv
  · rintro ⟨x, hx⟩
    refine ⟨basePointsRepresentation (H := H) W x w₀, ⟨x, 1, (one_smul _ _).symm⟩,
      fun h0 => hw₀ ?_, (hkey z x).mp hx⟩
    rw [← hinv x w₀, h0, map_zero]

end CFSG.LieType.AlgebraicGroups.ClosedCone
