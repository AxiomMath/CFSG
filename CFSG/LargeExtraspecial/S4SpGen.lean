module

public import CFSG.LargeExtraspecial.S4SpTrans
public import CFSG.ClassicalGroups.Alternating.Generation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module Subgroup CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {β : LinearMap.BilinForm (ZMod 2) V}

theorem eq_isometryGroup_of_spTransvection_mem (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {X : Subgroup (V ≃ₗ[ZMod 2] V)} (hX : X ≤ TauCeti.BilinForm.isometryGroup β)
    (hτ : ∀ a : V, spTransvection β hβ a ∈ X) : X = TauCeti.BilinForm.isometryGroup β := by
  refine le_antisymm hX fun g hg => ?_
  set f := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V with hf
  have hg' : f.symm g ∈ CFSG.LocalAnalysis.ComponentInitial.bilinIsometryGroup β := by
    rw [CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup]
    intro x y
    exact TauCeti.BilinForm.mem_isometryGroup_iff.mp hg x y
  rw [CFSG.ClassicalGroups.Alternating.alternating_transvection_generation hβ hnd] at hg'
  have hle : Subgroup.closure {u | ∃ (a : V) (c : ZMod 2),
      u = CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβ a c} ≤
        X.comap f.toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨a, c, rfl⟩
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
    · have : f (CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβ a 0) = 1 := by
        ext x
        change (CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβ a 0 :
          V →ₗ[ZMod 2] V) x = x
        rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, zero_mul, zero_smul,
          add_zero]
      change f _ ∈ X
      rw [this]
      exact one_mem _
    · have : f (CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβ a 1) =
          spTransvection β hβ a := by
        ext x
        change (CFSG.ClassicalGroups.Alternating.symplecticTransvection β hβ a 1 :
          V →ₗ[ZMod 2] V) x = _
        rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul,
          spTransvection_apply]
      change f _ ∈ X
      rw [this]
      exact hτ a
  have := hle hg'
  change f (f.symm g) ∈ X at this
  rwa [MulEquiv.apply_symm_apply] at this

omit [FiniteDimensional (ZMod 2) V] in
theorem spTransvection_mem_of_one (hβ : β.IsAlt) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : X ≤ TauCeti.BilinForm.isometryGroup β) {a : V} (ha : spTransvection β hβ a ∈ X)
    (htr : ∀ v : V, v ≠ 0 → ∃ x ∈ X, x a = v) (v : V) : spTransvection β hβ v ∈ X := by
  by_cases hv : v = 0
  · have : spTransvection β hβ v = 1 := by
      ext x
      rw [hv, spTransvection_apply, smul_zero, add_zero]
      rfl
    rw [this]
    exact one_mem _
  obtain ⟨x, hxX, rfl⟩ := htr v hv
  rw [← conj_spTransvection hβ a (hX hxX)]
  exact mul_mem (mul_mem hxX ha) (inv_mem hxX)

theorem eq_isometryGroup_of_transitive (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : X ≤ TauCeti.BilinForm.isometryGroup β) {a : V} (ha : a ≠ 0)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEX : E ≤ X) (hEU : E ≤ spPointRadical β a)
    (hidx : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E)
    (hnorm : ∀ x ∈ X, x a = a → x ∈ normalizer (E : Set (V ≃ₗ[ZMod 2] V)))
    (htr : ∀ v : V, v ≠ 0 → ∃ x ∈ X, x a = v) : X = TauCeti.BilinForm.isometryGroup β :=
  eq_isometryGroup_of_spTransvection_mem hβ hnd hX (spTransvection_mem_of_one hβ hX
    (hEX (spTransvection_mem_of_transitive hβ hnd h6 hX ha hEX hEU hidx hnorm htr)) htr)

end CFSG.LargeExtraspecial.S4
