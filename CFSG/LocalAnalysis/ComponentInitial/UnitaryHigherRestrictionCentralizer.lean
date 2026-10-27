module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherCentralizerTwo
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem unitary_restriction_symplectic_centralizer_solvable (h : UnitaryFieldData p f E)
    (hp : p ≠ 2) [FiniteDimensional E V] (hm : 2 ≤ finrank E V)
    {Hf : V →ₛₗ[h.bar] V →ₗ[E] E} (hH : Hf.IsSymm) (hnd : Hf.Nondegenerate)
    (B : LinearMap.BilinForm h.fixedField V) (hB : B.Nondegenerate) (hBalt : B.IsAlt)
    (hinv : ∀ g ∈ sesqSpecialUnitaryGroup Hf, ∀ u v,
      B ((g : V →ₗ[E] V) u) ((g : V →ₗ[E] V) v) = B u v) :
    Group.IsSolvable (Subgroup.centralizer
      ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars h.fixedField)).subgroupOf
        (bilinIsometryGroup B)) : Set (bilinIsometryGroup B))) ∧
    (3 ≤ finrank E V →
      (∀ X : LinearMap.GeneralLinearGroup h.fixedField V,
        X ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
          (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)) ↔
          ∃ a : Eˣ, ∀ v, (X : V →ₗ[h.fixedField] V) v = (a : E) • v) ∧
      ∀ X ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
          (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)),
        ∀ Y ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
          (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)),
          X * Y = Y * X) := by
  have hfull : 3 ≤ finrank E V → ∀ X : LinearMap.GeneralLinearGroup h.fixedField V,
      X ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
        (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)) ↔
        ∃ a : Eˣ, ∀ v, (X : V →ₗ[h.fixedField] V) v = (a : E) • v := by
    intro hm3 X
    constructor
    · intro hX
      rw [Subgroup.mem_centralizer_iff] at hX
      obtain ⟨a, ha⟩ := commutant_eq_scalar h hp hm3 hH hnd.1 (X : V →ₗ[h.fixedField] V)
        fun g hg v => by
          have h1 := hX _ ⟨g, hg, rfl⟩
          have h2 := congrArg (fun Y : LinearMap.GeneralLinearGroup h.fixedField V =>
            (Y : V →ₗ[h.fixedField] V) v) h1
          exact h2.symm
      obtain ⟨v₀, hv₀⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := E) (M := V)).mp
        (by omega)
      have ha0 : a ≠ 0 := by
        rintro rfl
        have h1 := ha v₀
        rw [zero_smul] at h1
        have h2 : ((X⁻¹ : LinearMap.GeneralLinearGroup h.fixedField V) :
            V →ₗ[h.fixedField] V) ((X : V →ₗ[h.fixedField] V) v₀) = v₀ := by
          rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Module.End.one_apply]
        rw [h1, map_zero] at h2
        exact hv₀ h2.symm
      exact ⟨Units.mk0 a ha0, ha⟩
    · rintro ⟨a, ha⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, -, rfl⟩
      refine Units.ext (LinearMap.ext fun v => ?_)
      change (g : V →ₗ[E] V) ((X : V →ₗ[h.fixedField] V) v) =
        (X : V →ₗ[h.fixedField] V) ((g : V →ₗ[E] V) v)
      rw [ha, ha, map_smul]
  have hcomm : 3 ≤ finrank E V → ∀ X ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
      (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)),
      ∀ Y ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
        (glRestrictScalars h.fixedField)) : Set (LinearMap.GeneralLinearGroup h.fixedField V)),
        X * Y = Y * X := by
    intro hm3 X hX Y hY
    obtain ⟨a, ha⟩ := (hfull hm3 X).mp hX
    obtain ⟨b, hb⟩ := (hfull hm3 Y).mp hY
    refine Units.ext (LinearMap.ext fun v => ?_)
    change (X : V →ₗ[h.fixedField] V) ((Y : V →ₗ[h.fixedField] V) v) =
      (Y : V →ₗ[h.fixedField] V) ((X : V →ₗ[h.fixedField] V) v)
    rw [ha, hb, ha, hb, smul_smul, smul_smul, mul_comm]
  refine ⟨?_, fun hm3 => ⟨hfull hm3, hcomm hm3⟩⟩
  rcases (by omega : finrank E V = 2 ∨ 3 ≤ finrank E V) with h2 | hm3
  · exact centralizer_solvable_two h hp h2 hH hnd B hB hBalt hinv
  · refine Group.isSolvable_of_comm fun x y => Subtype.ext (Subtype.ext ?_)
    have hmemS : ∀ z : Subgroup.centralizer
        ((((sesqSpecialUnitaryGroup Hf).map (glRestrictScalars h.fixedField)).subgroupOf
          (bilinIsometryGroup B)) : Set (bilinIsometryGroup B)),
        (z : bilinIsometryGroup B).1 ∈ Subgroup.centralizer (((sesqSpecialUnitaryGroup Hf).map
          (glRestrictScalars h.fixedField)) :
            Set (LinearMap.GeneralLinearGroup h.fixedField V)) := by
      intro z
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g, hg, rfl⟩
      have hgB : glRestrictScalars h.fixedField g ∈ bilinIsometryGroup B :=
        mem_bilinIsometryGroup.mpr fun u w => hinv g hg u w
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp z.2) ⟨_, hgB⟩
        (Subgroup.mem_subgroupOf.mpr ⟨g, hg, rfl⟩))
    exact hcomm hm3 _ (hmemS x) _ (hmemS y)

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
