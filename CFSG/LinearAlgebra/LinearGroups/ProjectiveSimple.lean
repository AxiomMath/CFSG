module

public import CFSG.LinearAlgebra.LinearGroups.Elations
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.LinearGroups

open Matrix Module
open scoped Pointwise LinearAlgebra.Projectivization

variable {K : Type*} [Field K] {n : ℕ}

theorem linear_projective_action (hn : 2 ≤ n) :
    Nonempty (ℙ K (Fin n → K)) ∧
      Function.Bijective (fun p : ℙ K (Fin n → K) =>
        (⟨p.submodule, p.finrank_submodule⟩ :
          {L : Submodule K (Fin n → K) // finrank K L = 1})) ∧
      (∀ (g : SpecialLinearGroup (Fin n) K) (p : ℙ K (Fin n → K)),
        (g • p).submodule = g • p.submodule) ∧
      (∀ (g : SpecialLinearGroup (Fin n) K) (p : ℙ K (Fin n → K)),
        QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)) g • p = g • p) ∧
      FaithfulSMul (ProjectiveSpecialLinearGroup (Fin n) K) (ℙ K (Fin n → K)) ∧
      MulAction.IsMultiplyPretransitive (ProjectiveSpecialLinearGroup (Fin n) K)
        (ℙ K (Fin n → K)) 2 ∧
      MulAction.IsPreprimitive (ProjectiveSpecialLinearGroup (Fin n) K) (ℙ K (Fin n → K)) := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  refine ⟨inferInstance,
    ⟨fun p q h => Projectivization.submodule_injective (congrArg Subtype.val h),
      fun L => ⟨Projectivization.mk'' L.1 L.2, Subtype.ext (Projectivization.submodule_mk'' _ _)⟩⟩,
    PSL.smul_submodule, fun _ _ => rfl, inferInstance, ?_, inferInstance⟩
  let f : ℙ K (Fin n → K) →ₑ[QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K))]
      ℙ K (Fin n → K) :=
    { toFun := id
      map_smul' := fun _ _ => rfl }
  exact MulAction.IsPretransitive.of_embedding (f := f) Function.surjective_id

theorem linear_projective_elation_data {L : Submodule K (Fin n → K)} (hL : finrank K L = 1) :
    (∀ a ∈ projectiveElationSubgroup L, ∀ b ∈ projectiveElationSubgroup L, a * b = b * a) ∧
      projectiveElationSubgroup L ≤ MulAction.stabilizer
        (ProjectiveSpecialLinearGroup (Fin n) K) (Projectivization.mk'' L hL) ∧
      (∀ h ∈ MulAction.stabilizer (ProjectiveSpecialLinearGroup (Fin n) K)
          (Projectivization.mk'' L hL),
        ∀ a ∈ projectiveElationSubgroup L, h * a * h⁻¹ ∈ projectiveElationSubgroup L) ∧
      Subgroup.normalClosure
        (projectiveElationSubgroup L : Set (ProjectiveSpecialLinearGroup (Fin n) K)) = ⊤ := by
  have hstab : ∀ g : SpecialLinearGroup (Fin n) K,
      QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)) g ∈
        MulAction.stabilizer (ProjectiveSpecialLinearGroup (Fin n) K)
          (Projectivization.mk'' L hL) ↔ g • L = L := by
    intro g
    rw [MulAction.mem_stabilizer_iff, QuotientGroup.mk'_apply,
      Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
      ← Projectivization.submodule_injective.eq_iff, PSL.smul_submodule,
      Projectivization.submodule_mk'']
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (linear_elation_abelian hL).2 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    exact (hstab a).mpr ((linear_elation_conjugation L a).2.1 ha)
  · rintro h hh _ ⟨a, ha, rfl⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ h
    refine ⟨g * a * g⁻¹, (linear_elation_conjugation L g).2.2 g ((hstab g).mp hh) a ha, ?_⟩
    simp
  · rw [projectiveElationSubgroup, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _
      (QuotientGroup.mk'_surjective _), linear_elation_conjugate_generation hL]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem projectiveElationSubgroup_smul (g : ProjectiveSpecialLinearGroup (Fin n) K)
    (p : ℙ K (Fin n → K)) :
    projectiveElationSubgroup (g • p).submodule =
      MulAut.conj g • projectiveElationSubgroup p.submodule := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, PSL.smul_submodule,
    projectiveElationSubgroup, projectiveElationSubgroup, ← conj_smul_elationSubgroup,
    PSL.iwasawaT_map_conj]

@[expose] noncomputable def projectiveElationIwasawa :
    MulAction.IwasawaStructure (ProjectiveSpecialLinearGroup (Fin n) K) (ℙ K (Fin n → K)) where
  T p := projectiveElationSubgroup p.submodule
  is_comm p := ⟨⟨fun a b => Subtype.ext
    ((linear_projective_elation_data p.finrank_submodule).1 a a.2 b b.2)⟩⟩
  is_conj := projectiveElationSubgroup_smul
  is_generator := by
    have hSL : (⨆ p : ℙ K (Fin n → K), elationSubgroup p.submodule) = ⊤ := by
      rw [eq_top_iff, ← special_linear_elementary_generation, Subgroup.closure_le]
      rintro _ ⟨i, j, hij, c, rfl⟩
      have hei : (Pi.single i (1 : K) : Fin n → K) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
      refine Subgroup.mem_iSup_of_mem (Projectivization.mk K _ hei) ?_
      rw [Projectivization.submodule_mk]
      exact linear_elation_elementary_containment hij c
    change (⨆ p : ℙ K (Fin n → K), (elationSubgroup p.submodule).map _) = ⊤
    rw [← Subgroup.map_iSup, hSL]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem linear_projective_simple (hn : 2 ≤ n) (h : 3 ≤ n ∨ ∃ s : Finset K, s.card = 4) :
    Nontrivial (ProjectiveSpecialLinearGroup (Fin n) K) ∧
      IsSimpleGroup (ProjectiveSpecialLinearGroup (Fin n) K) ∧
      (Finite K → Finite (ProjectiveSpecialLinearGroup (Fin n) K)) := by
  have hnt := linear_projective_nontrivial (K := K) hn
  refine ⟨hnt, ?_, fun _ => inferInstance⟩
  exact MulAction.IwasawaStructure.isSimpleGroup (linear_projective_perfect hn h).commutator_eq_top
    projectiveElationIwasawa inferInstance

end CFSG.LinearGroups
