module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

variable {F : Type} [Field F] [Finite F]

instance faithfulSMul_zpowers (σ : F ≃+* F) : FaithfulSMul (Subgroup.zpowers σ) F :=
  ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩

theorem algebraMap_norm_fixed (σ : F ≃+* F) (y : F) :
    algebraMap (FixedPoints.subfield (Subgroup.zpowers σ) F) F
        (Algebra.norm (FixedPoints.subfield (Subgroup.zpowers σ) F) y) =
      ∏ j ∈ Finset.range (orderOf σ), (σ ^ j) y := by
  classical
  have : Finite (F ≃+* F) := Finite.of_injective (fun τ : F ≃+* F => (τ : F → F))
    fun a b h => RingEquiv.ext (congrFun h)
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have : Fintype (Subgroup.zpowers σ) := Fintype.ofFinite _
  rw [Algebra.norm_eq_prod_automorphisms]
  rw [← Fintype.prod_equiv (FixedPoints.toAlgAutMulEquiv (Subgroup.zpowers σ) F).toEquiv
      (fun g => g • y) (fun τ => τ y) fun g => rfl,
    ← Fintype.prod_equiv (finEquivZPowers hfin) (fun i : Fin (orderOf σ) => (σ ^ (i : ℕ)) y) _
      fun i => by rw [finEquivZPowers_apply]; rfl,
    Fin.prod_univ_eq_prod_range (fun j => (σ ^ j) y)]

theorem exists_norm_ratio (σ : F ≃+* F) {ι : Type*} (t : ι → Fˣ) (c₀ : F)
    (ht : ∀ i, ∏ j ∈ Finset.range (orderOf σ), (σ ^ j) (t i : F) = c₀) :
    ∃ (a : Fˣ) (u : ι → Fˣ), ∀ i, (a : F) * t i = u i / σ (u i) := by
  classical
  set G := Subgroup.zpowers σ
  set F₀ := FixedPoints.subfield G F
  have : Finite (F ≃+* F) := Finite.of_injective (fun τ : F ≃+* F => (τ : F → F))
    fun a b h => RingEquiv.ext (congrFun h)
  have : Finite F₀ := Subtype.finite
  have : IsCyclic (F ≃ₐ[F₀] F) :=
    isCyclic_of_surjective (FixedPoints.toAlgAutMulEquiv G F).toMonoidHom
      (FixedPoints.toAlgAutMulEquiv G F).surjective
  set g := FixedPoints.toAlgAutMulEquiv G F ⟨σ, Subgroup.mem_zpowers σ⟩
  have hg : ∀ x, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨⟨τ, hτ⟩, rfl⟩ := (FixedPoints.toAlgAutMulEquiv G F).surjective x
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
    refine ⟨k, ?_⟩
    change g ^ k = _
    rw [show (⟨σ ^ k, hτ⟩ : G) = ⟨σ, Subgroup.mem_zpowers σ⟩ ^ k from
      Subtype.ext (by rw [Subgroup.coe_zpow]), map_zpow]
  have hgapply : ∀ y : F, g y = σ y := fun y => rfl
  rcases isEmpty_or_nonempty ι with hempty | ⟨⟨i₀⟩⟩
  · exact ⟨1, fun i => (hempty.false i).elim, fun i => (hempty.false i).elim⟩
  ·
    have hc : c₀ = algebraMap F₀ F (Algebra.norm F₀ (t i₀ : F)) := by
      rw [algebraMap_norm_fixed, ht]
    have hc0 : Algebra.norm F₀ (t i₀ : F) ≠ 0 := Algebra.norm_ne_zero_iff.2 (t i₀).ne_zero
    obtain ⟨a, ha⟩ := FiniteField.unitsMap_norm_surjective F₀ F
      (Units.mk0 (Algebra.norm F₀ (t i₀ : F)) hc0)⁻¹
    have hna : Algebra.norm F₀ (a : F) * Algebra.norm F₀ (t i₀ : F) = 1 := by
      have h := congrArg Units.val ha
      rw [Units.coe_map, Units.val_inv_eq_inv_val, Units.val_mk0] at h
      change Algebra.norm F₀ (a : F) = _ at h
      rw [h, inv_mul_cancel₀ hc0]
    have hnorm : ∀ i, Algebra.norm F₀ ((a : F) * t i) = 1 := by
      intro i
      rw [map_mul]
      have hti : Algebra.norm F₀ (t i : F) = Algebra.norm F₀ (t i₀ : F) := by
        apply (algebraMap F₀ F).injective
        rw [algebraMap_norm_fixed, algebraMap_norm_fixed, ht, ht]
      rw [hti, hna]
    choose u hu using fun i => groupCohomology.exists_div_of_norm_eq_one hg (hnorm i)
    exact ⟨a, u, fun i => by rw [← hu i, hgapply]⟩

end CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane
