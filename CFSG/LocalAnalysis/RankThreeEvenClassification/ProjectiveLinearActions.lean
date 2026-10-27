module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.OneDimensionalPrimeActions

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem linearEquiv_end_injective {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space) :
    Function.Injective (equivalence : Module.End field space) := equivalence.injective

noncomputable def linearProjectiveAction (field : Type u) (space : Type v)
    [Field field] [AddCommGroup space] [Module field space] :
    (space ≃ₗ[field] space) →* Equiv.Perm (Projectivization field space) where
  toFun equivalence :=
    { toFun := Projectivization.map (equivalence : Module.End field space) (linearEquiv_end_injective equivalence)
      invFun := Projectivization.map (equivalence.symm : Module.End field space) (linearEquiv_end_injective equivalence.symm)
      left_inv := by
        intro point
        induction point using Projectivization.ind with
        | h member hmember =>
          rw [Projectivization.map_mk, Projectivization.map_mk]
          apply Projectivization.submodule_injective
          rw [Projectivization.submodule_mk, Projectivization.submodule_mk]
          have heq : (equivalence.symm : Module.End field space)
              ((equivalence : Module.End field space) member) = member :=
            equivalence.symm_apply_apply member
          rw [heq]
      right_inv := by
        intro point
        induction point using Projectivization.ind with
        | h member hmember =>
          rw [Projectivization.map_mk, Projectivization.map_mk]
          apply Projectivization.submodule_injective
          rw [Projectivization.submodule_mk, Projectivization.submodule_mk]
          have heq : (equivalence : Module.End field space)
              ((equivalence.symm : Module.End field space) member) = member :=
            equivalence.apply_symm_apply member
          rw [heq] }
  map_one' := by
    apply Equiv.ext
    intro point
    induction point using Projectivization.ind with
    | h member hmember =>
      change Projectivization.map ((1 : space ≃ₗ[field] space) : Module.End field space) (linearEquiv_end_injective 1)
        (Projectivization.mk field member hmember) = Projectivization.mk field member hmember
      simp only [LinearEquiv.coe_toLinearMap_one, Projectivization.map_id, id_eq]
  map_mul' first second := by
    apply Equiv.ext
    intro point
    exact congrFun (Projectivization.map_comp (second : Module.End field space)
      (linearEquiv_end_injective second) (first : Module.End field space)
      (linearEquiv_end_injective first)) point

theorem linearProjectiveAction_apply_mk {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space) (member : space) (hne : member ≠ 0) :
    linearProjectiveAction field space equivalence (Projectivization.mk field member hne) =
      Projectivization.mk field (equivalence member) (by
        intro heq
        exact hne (equivalence.injective (heq.trans (map_zero equivalence).symm))) := by
  exact Projectivization.map_mk (equivalence : Module.End field space)
    (linearEquiv_end_injective equivalence) member hne

theorem projective_fixed_point_iff_eigenvector {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (equivalence : space ≃ₗ[field] space) (member : space) (hne : member ≠ 0) :
    linearProjectiveAction field space equivalence (Projectivization.mk field member hne) =
      Projectivization.mk field member hne ↔ ∃ scalar : field, equivalence member = scalar • member := by
  rw [linearProjectiveAction_apply_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨fun ⟨scalar, heq⟩ => ⟨scalar, heq.symm⟩, fun ⟨scalar, heq⟩ => ⟨scalar, heq.symm⟩⟩

theorem linear_pElement_fixed_projective_iff_fixed_vector {field : Type u} {space : Type v}
    [Field field] [AddCommGroup space] [Module field space]
    (prime : ℕ) (hprime : prime.Prime) [CharP field prime]
    (equivalence : space ≃ₗ[field] space) (exponent : ℕ)
    (hpower : equivalence ^ (prime ^ exponent) = 1) (member : space) (hne : member ≠ 0) :
    linearProjectiveAction field space equivalence (Projectivization.mk field member hne) =
      Projectivization.mk field member hne ↔ equivalence member = member := by
  constructor
  · intro hfixed
    obtain ⟨scalar, heigenvector⟩ := (projective_fixed_point_iff_eigenvector equivalence member hne).mp hfixed
    have hiterate : ∀ power : ℕ, (equivalence ^ power) member = scalar ^ power • member := by
      intro power
      induction power with
      | zero => simp
      | succ power ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, heigenvector, smul_smul, ← pow_succ]
    have heq := hiterate (prime ^ exponent)
    rw [hpower] at heq
    change member = scalar ^ (prime ^ exponent) • member at heq
    have hscalarPower : scalar ^ (prime ^ exponent) = 1 :=
      smul_left_injective field hne (heq.symm.trans (one_smul field member).symm)
    rw [char_prime_power_eq_one prime hprime scalar exponent hscalarPower, one_smul] at heigenvector
    exact heigenvector
  · intro hfixed
    apply (projective_fixed_point_iff_eigenvector equivalence member hne).mpr
    exact ⟨1, hfixed.trans (one_smul field member).symm⟩

end CFSG.RankThreeEvenClassification.Helpers
