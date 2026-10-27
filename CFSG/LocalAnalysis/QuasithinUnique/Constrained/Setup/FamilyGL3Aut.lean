module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Irred

public section

namespace CFSG.QuasithinUnique.Setup.Family

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification Matrix CFSG.ProperTwoGeneratedCore.BinaryThreeSpace

theorem fieldAut_zmod_two (n : ℕ) (σ : ZMod 2 ≃+* ZMod 2) : fieldAut n (ZMod 2) σ = 1 := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨g, rfl⟩ := proj_surjective n (ZMod 2) x
  rw [fieldAut_proj]
  have hσ : σ.toRingHom = RingHom.id _ := Subsingleton.elim _ _
  have hmap : Matrix.SpecialLinearGroup.map (RingHom.id (ZMod 2)) g = g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  rw [hσ, hmap]
  rfl

theorem descendAut_injective_zmod_two (n : ℕ) : Function.Injective (descendAut n (ZMod 2)) := by
  intro e e' h
  refine MulEquiv.ext fun g => ?_
  have := congrArg (fun φ : MulAut (projectiveSL n (ZMod 2)) => φ (proj n (ZMod 2) g)) h
  simp only [descendAut_proj] at this
  exact proj_injective_zmod_two n this

theorem aut_SL3_cases (α : MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :
    (∃ A : GL (Fin 3) (ZMod 2),
        α = CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A) ∨
      (∃ A : GL (Fin 3) (ZMod 2),
        α = CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A *
          CatalogueBGraphForm.slGraphAut 3 (ZMod 2)) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := ZMod 2) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, h⟩ := hgen (descendAut 3 (ZMod 2) α)
  rw [fieldAut_zmod_two, mul_one] at h
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    rw [pow_zero, mul_one] at h
    exact ⟨A, descendAut_injective_zmod_two 3 (by rw [h]; rfl)⟩
  · right
    rw [pow_one] at h
    exact ⟨A, descendAut_injective_zmod_two 3 (by rw [h, map_mul]; rfl)⟩

theorem congr_slConjugation (A : GL (Fin 3) (ZMod 2)) :
    MulAut.congr (slEquivGL 3) (CatalogueBHigherLinearAction.slConjugation 3 (ZMod 2) A) =
      MulAut.conj A := by
  refine MulEquiv.ext fun h => ?_
  obtain ⟨g, rfl⟩ := (slEquivGL 3).surjective h
  rw [MulAut.congr_apply, MulAut.conj_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact CatalogueBHigherLinearAction.toGL_slConjugation 3 (ZMod 2) A g

theorem congr_slGraphAut :
    MulAut.congr (slEquivGL 3) (CatalogueBGraphForm.slGraphAut 3 (ZMod 2)) =
      CatalogueBGraphForm.glGraphAut 3 (ZMod 2) := by
  refine MulEquiv.ext fun h => ?_
  obtain ⟨g, rfl⟩ := (slEquivGL 3).surjective h
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact CatalogueBGraphForm.toGL_slGraphAut 3 (ZMod 2) g

theorem aut_GL32_cases (α : MulAut GL32) :
    (∃ s : GL32, α = MulAut.conj s) ∨
      (∃ s : GL32, α = MulAut.conj s * CatalogueBGraphForm.glGraphAut 3 (ZMod 2)) := by
  have hα : MulAut.congr (slEquivGL 3) ((MulAut.congr (slEquivGL 3)).symm α) = α :=
    (MulAut.congr (slEquivGL 3)).apply_symm_apply α
  rcases aut_SL3_cases ((MulAut.congr (slEquivGL 3)).symm α) with ⟨A, hA⟩ | ⟨A, hA⟩
  · left
    refine ⟨A, ?_⟩
    rw [← hα, hA, congr_slConjugation]
  · right
    refine ⟨A, ?_⟩
    rw [← hα, hA, map_mul, congr_slConjugation, congr_slGraphAut]

theorem no_graph_conj : ∀ a b c d e f g h i : ZMod 2,
    Matrix.det !![a, b, c; d, e, f; g, h, i] = 1 →
    !![a, b, c; d, e, f; g, h, i] * unitri 1 0 0 =
      (unitri 1 0 0)ᵀ * !![a, b, c; d, e, f; g, h, i] →
    !![a, b, c; d, e, f; g, h, i] * unitri 0 1 0 =
      (unitri 0 1 0)ᵀ * !![a, b, c; d, e, f; g, h, i] → False := by
  decide

theorem glGraphAut_ne_conj (s : GL32) :
    CatalogueBGraphForm.glGraphAut 3 (ZMod 2) ≠ MulAut.conj s := by
  intro h
  have hdet : (s : Mat3).det = 1 := by
    have h1 : Matrix.GeneralLinearGroup.det s = 1 := Subsingleton.elim _ _
    have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
    simpa using h2
  have key : ∀ g : GL32, (s : Mat3) * (g : Mat3) = ((g⁻¹ : GL32) : Mat3)ᵀ * (s : Mat3) := by
    intro g
    have h1 := congrArg (fun φ : MulAut GL32 => ((φ g : GL32) : Mat3)) h
    simp only [MulAut.conj_apply, Units.val_mul, CatalogueBGraphForm.glGraphAut_matrix] at h1
    have h2 : ((s⁻¹ : GL32) : Mat3) * (s : Mat3) = 1 := Units.inv_mul s
    calc (s : Mat3) * (g : Mat3) = ((s : Mat3) * (g : Mat3)) * 1 := (Matrix.mul_one _).symm
      _ = ((s : Mat3) * (g : Mat3)) * (((s⁻¹ : GL32) : Mat3) * (s : Mat3)) := by rw [h2]
      _ = ((s : Mat3) * (g : Mat3) * ((s⁻¹ : GL32) : Mat3)) * (s : Mat3) :=
          (Matrix.mul_assoc _ _ _).symm
      _ = ((g⁻¹ : GL32) : Mat3)ᵀ * (s : Mat3) := by rw [← h1]
  have k1 : (s : Mat3) * unitri 1 0 0 = (unitri 1 0 0)ᵀ * (s : Mat3) := key (unitriGL 1 0 0)
  have k2 : (s : Mat3) * unitri 0 1 0 = (unitri 0 1 0)ᵀ * (s : Mat3) := key (unitriGL 0 1 0)
  have e := Matrix.eta_fin_three (s : Mat3)
  refine no_graph_conj ((s : Mat3) 0 0) ((s : Mat3) 0 1) ((s : Mat3) 0 2) ((s : Mat3) 1 0)
    ((s : Mat3) 1 1) ((s : Mat3) 1 2) ((s : Mat3) 2 0) ((s : Mat3) 2 1) ((s : Mat3) 2 2) ?_ ?_ ?_
  · rw [← e]; exact hdet
  · rw [← e]; exact k1
  · rw [← e]; exact k2

theorem center_GL32 : Subgroup.center GL32 = ⊥ := by
  have h := Subgroup.map_center_eq (slEquivGL 3)
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
    rw [← scalars_eq_center]
    exact scalars_zmod_two 3
  rw [hc, Subgroup.map_bot] at h
  exact h.symm

end CFSG.QuasithinUnique.Setup.Family
