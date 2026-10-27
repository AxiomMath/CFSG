module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderSp4PerfE0
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoPerOffenderInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain Matrix

private theorem sp4p_stabL_map_conj {L : Type*} [Group L] {F : Type*} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) (g : L) (u : Fin r → F) :
    (stabL Mat u).map (MulAut.conj g).toMonoidHom =
      stabL Mat ((Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u) := by
  have hcoeg : ∀ x : L, (Mat (MulAut.conj g x) : Matrix (Fin r) (Fin r) F) =
      (Mat g : Matrix (Fin r) (Fin r) F) * (Mat x : Matrix (Fin r) (Fin r) F) *
        (Mat g : Matrix (Fin r) (Fin r) F)⁻¹ := by
    intro x
    simp only [MulAut.conj_apply, map_mul, map_inv,
      Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv]
  have hinv : ∀ w : Fin r → F,
      ((Mat g : Matrix (Fin r) (Fin r) F))⁻¹ *ᵥ
          ((Mat g : Matrix (Fin r) (Fin r) F) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_inv,
      ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  ext s
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    change (Mat (MulAut.conj g a) : Matrix (Fin r) (Fin r) F) *ᵥ
      ((Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u) =
        (Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u
    rw [hcoeg a, ← Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec, ha]
  · intro hs
    refine ⟨g⁻¹ * s * g, ?_, ?_⟩
    · have hcs : (Mat (g⁻¹ * s * g) : Matrix (Fin r) (Fin r) F) =
          ((Mat g : Matrix (Fin r) (Fin r) F))⁻¹ * (Mat s : Matrix (Fin r) (Fin r) F) *
            (Mat g : Matrix (Fin r) (Fin r) F) := by
        simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.coe_mul,
          Matrix.GeneralLinearGroup.coe_inv]
      change (Mat (g⁻¹ * s * g) : Matrix (Fin r) (Fin r) F) *ᵥ u = u
      rw [hcs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hs, hinv]
    · show MulAut.conj g (g⁻¹ * s * g) = s
      rw [MulAut.conj_apply]
      group

private theorem sp4p_stabL_eq_map_conj {L : Type*} [Group L] {F : Type*} [Field F] {r : ℕ}
    (Mat : L →* Matrix.GeneralLinearGroup (Fin r) F) {u v : Fin r → F} {g : L}
    (hg : (Mat g : Matrix (Fin r) (Fin r) F) *ᵥ u = v) :
    stabL Mat u = (stabL Mat v).map (MulAut.conj g⁻¹).toMonoidHom := by
  have hinv : (Mat g⁻¹ : Matrix (Fin r) (Fin r) F) *ᵥ v = u := by
    rw [← hg, Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, map_inv,
      inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  have h := sp4p_stabL_map_conj (F := F) (r := r) Mat g⁻¹ v
  rw [hinv] at h
  exact h.symm

private theorem sp4p_antiSp_perfect {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) : Group.IsPerfect (antiSp F) := by
  have : Group.IsPerfect (CFSG.Open.StatedSp 2 F) := by
    refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp 2 F (Or.inl ?_)
    have : Fintype F := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact ⟨s, hs⟩
  exact Group.IsPerfect.ofSurjective (f := (antiSpEquiv F).symm.toMonoidHom)
    (antiSpEquiv F).symm.surjective

private theorem sp4p_e0_ne_zero {F : Type} [Field F] :
    ((Pi.single (0 : Fin 4) (1 : F) : Fin 4 → F)) ≠ 0 := by
  intro h
  exact one_ne_zero (α := F) (by simpa using congrFun h (0 : Fin 4))

private theorem sp4p_antiSp_exists_mulVec_eq {F : Type} [Field F] [CharP F 2]
    {u v : Fin 4 → F} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : antiSp F, (glMat (g : GL (Fin 4) F)) *ᵥ u = v := by
  obtain ⟨g, hg, hgu⟩ := (CFSG.ClassicalGroups.Alternating.alternating_transvection_vector_transitivity
    (minorForm_isAlt (K := F)) minorForm_nondegenerate).2 u v hu hv
  have hmem : (GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm g ∈ antiSp F := by
    rw [antiSp_eq_closure]
    have hmem' := Subgroup.mem_map_of_mem
      (GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm.toMonoidHom hg
    rw [MonoidHom.map_closure] at hmem'
    have hset : {g' : GL (Fin 4) F | ∃ (a : Fin 4 → F) (c : F), g' =
        GeneralLinearGroup.toLin.symm (CFSG.ClassicalGroups.Alternating.symplecticTransvection
          (minorForm F) minorForm_isAlt a c)} =
        ⇑(GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm.toMonoidHom ''
          {g | ∃ (a : Fin 4 → F) (c : F), g =
            CFSG.ClassicalGroups.Alternating.symplecticTransvection (minorForm F)
              minorForm_isAlt a c} := by
      ext y
      constructor
      · rintro ⟨a, c, rfl⟩
        exact ⟨_, ⟨a, c, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, c, rfl⟩, rfl⟩
        exact ⟨a, c, rfl⟩
    rw [hset]
    exact hmem'
  refine ⟨⟨_, hmem⟩, ?_⟩
  have h1 : (GeneralLinearGroup.toLin (n := Fin 4) (R := F))
      ((GeneralLinearGroup.toLin (n := Fin 4) (R := F)).symm g) = g :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun x : LinearMap.GeneralLinearGroup F (Fin 4 → F) =>
    (x : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) u) h1
  simp only [GeneralLinearGroup.coe_toLin, mulVecLin_apply] at h2
  rw [← hgu]
  exact h2

theorem sp4_perfect_stab_zero {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    ⁅stabL (antiSp F).subtype (0 : Fin 4 → F), stabL (antiSp F).subtype (0 : Fin 4 → F)⁆ =
      stabL (antiSp F).subtype (0 : Fin 4 → F) := by
  have htop : stabL (antiSp F).subtype (0 : Fin 4 → F) = ⊤ := by
    ext l
    simp [stabL, Matrix.mulVec_zero]
  rw [htop]
  exact Group.isPerfect_def.mp (sp4p_antiSp_perfect h4)

theorem sp4_perfStab {F : Type} [Field F] [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) :
    PerfStab (antiSp F).subtype := by
  intro u
  by_cases hu : u = 0
  · rw [hu]
    exact sp4_perfect_stab_zero h4
  · obtain ⟨g, hg⟩ := sp4p_antiSp_exists_mulVec_eq hu (sp4p_e0_ne_zero (F := F))
    have hg' : ((antiSp F).subtype g : Matrix (Fin 4) (Fin 4) F) *ᵥ u =
        Pi.single (0 : Fin 4) (1 : F) := hg
    rw [sp4p_stabL_eq_map_conj (F := F) (r := 4) (antiSp F).subtype hg']
    rw [← Subgroup.map_commutator]
    rw [sp4_perfect_stab_e0 h4]

theorem k54PerfStabSp4_proof : K54PerfStabSp4 := fun _ _ _ _ h4 => sp4_perfStab h4

end CFSG.LocalAnalysis.RankThreeUC.S15

end
