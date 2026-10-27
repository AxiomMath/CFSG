module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieTorus

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257.L3
  CFSG.Quasithin.H13.F431.L3.P3

variable {F K : Type} [Field F] [Field K]

@[expose] noncomputable def projIso (ψ : F ≃+* K) : projectiveSL 3 F ≃* projectiveSL 3 K :=
  (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F).symm.trans
    ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv ψ (Fin 3)).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))

theorem coe_map_apply_iso (ψ : F ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 3) F) (i j : Fin 3) :
    ((Matrix.SpecialLinearGroup.map ψ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) i j = ψ ((g : Matrix (Fin 3) (Fin 3) F) i j) :=
  rfl

theorem projIso_proj (ψ : F ≃+* K) (g : Matrix.SpecialLinearGroup (Fin 3) F) :
    projIso ψ (proj 3 F g) = proj 3 K (Matrix.SpecialLinearGroup.map ψ.toRingHom g) :=
  rfl

theorem projIso_xP (ψ : F ≃+* K) (a : F) : projIso ψ (xP a) = xP (ψ a) := by
  unfold xP
  rw [projIso_proj]
  congr 1
  apply Subtype.ext
  ext i j
  rw [coe_map_apply_iso]
  fin_cases i <;> fin_cases j <;> simp [xMat, xM]

theorem projIso_yP (ψ : F ≃+* K) (b : F) : projIso ψ (yP b) = yP (ψ b) := by
  unfold yP
  rw [projIso_proj]
  congr 1
  apply Subtype.ext
  ext i j
  rw [coe_map_apply_iso]
  fin_cases i <;> fin_cases j <;> simp [yMat, yM]

theorem projIso_wP (ψ : F ≃+* K) (c : F) : projIso ψ (wP c) = wP (ψ c) := by
  unfold wP
  rw [projIso_proj]
  congr 1
  apply Subtype.ext
  ext i j
  rw [coe_map_apply_iso]
  fin_cases i <;> fin_cases j <;> simp [wMat, wM]

theorem projIso_dMat (ψ : F ≃+* K) (t₁ t₂ : Fˣ) :
    projIso ψ (proj 3 F (dMat t₁ t₂)) =
      proj 3 K (dMat (Units.map ψ.toMonoidHom t₁) (Units.map ψ.toMonoidHom t₂)) := by
  rw [projIso_proj]
  congr 1
  apply Subtype.ext
  ext i j
  rw [coe_map_apply_iso]
  fin_cases i <;> fin_cases j <;> simp [coe_dMat, Matrix.diagonal]

theorem projIso_mem_V2 [CharP F 2] [CharP K 2] (ψ : F ≃+* K) (g : projectiveSL 3 F) :
    projIso ψ g ∈ (V2 : Subgroup (projectiveSL 3 K)) ↔ g ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
  rw [mem_V2, mem_V2]
  constructor
  · rintro ⟨b, c, hbc⟩
    refine ⟨ψ.symm b, ψ.symm c, ?_⟩
    apply (projIso ψ).injective
    simp only [hbc, map_mul, projIso_yP, projIso_wP, RingEquiv.apply_symm_apply]
  · rintro ⟨b, c, rfl⟩
    exact ⟨ψ b, ψ c, by rw [map_mul, projIso_yP, projIso_wP]⟩

theorem projIso_mem_V1 [CharP F 2] [CharP K 2] (ψ : F ≃+* K) (g : projectiveSL 3 F) :
    projIso ψ g ∈ (V1 : Subgroup (projectiveSL 3 K)) ↔ g ∈ (V1 : Subgroup (projectiveSL 3 F)) := by
  rw [mem_V1, mem_V1]
  constructor
  · rintro ⟨a, c, hac⟩
    refine ⟨ψ.symm a, ψ.symm c, ?_⟩
    apply (projIso ψ).injective
    simp only [hac, map_mul, projIso_xP, projIso_wP, RingEquiv.apply_symm_apply]
  · rintro ⟨a, c, rfl⟩
    exact ⟨ψ a, ψ c, by rw [map_mul, projIso_xP, projIso_wP]⟩

theorem map_V2_projIso [CharP F 2] [CharP K 2] (ψ : F ≃+* K) :
    (V2 : Subgroup (projectiveSL 3 F)).map (projIso ψ).toMonoidHom = V2 := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have h := projIso_mem_V2 ψ ((projIso ψ).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem map_V1_projIso [CharP F 2] [CharP K 2] (ψ : F ≃+* K) :
    (V1 : Subgroup (projectiveSL 3 F)).map (projIso ψ).toMonoidHom = V1 := by
  ext x
  rw [Subgroup.mem_map_equiv]
  have h := projIso_mem_V1 ψ ((projIso ψ).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem map_Ln_projIso [CharP F 2] [CharP K 2] (ψ : F ≃+* K) :
    (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))).map
        (projIso ψ).toMonoidHom =
      Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
  rw [Subgroup.map_equiv_normalizer_eq, map_V2_projIso]

theorem map_Pt_projIso [CharP F 2] [CharP K 2] (ψ : F ≃+* K) :
    (Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))).map
        (projIso ψ).toMonoidHom =
      Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
  rw [Subgroup.map_equiv_normalizer_eq, map_V1_projIso]

theorem map_B0_projIso [CharP F 2] [CharP K 2] (ψ : F ≃+* K) :
    ((Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))) ⊓
        Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 F)) : Set (projectiveSL 3 F))).map
        (projIso ψ).toMonoidHom =
      (Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K))) ⊓
        Subgroup.normalizer ((V1 : Subgroup (projectiveSL 3 K)) : Set (projectiveSL 3 K)) := by
  rw [Subgroup.map_inf_eq _ _ _ (projIso ψ).injective, map_Ln_projIso, map_Pt_projIso]

end CFSG.GH74.QTGen4.DSGen4.L34
