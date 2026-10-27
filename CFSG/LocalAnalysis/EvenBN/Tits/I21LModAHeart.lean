module

public import CFSG.CharacterTheory.SteinbergBYAlternatingSixModular
public import CFSG.Quasithin.Background.Harris.Alt6.Heart

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Equiv Matrix CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.AlternatingSix CFSG.Quasithin.G11.Harris.Alt6

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def modA_rep (φ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W)) :
    Representation (ZMod 2) (alternatingGroup (Fin 6)) W :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp φ

theorem modA_rep_irreducible [Nontrivial W] (φ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W))
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    (modA_rep φ).IsIrreducible := by
  have hbot : (⊥ : Subrepresentation (modA_rep φ)) ≠ ⊤ := fun h =>
    bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, fun U => ?_⟩
  rcases hirr U.toSubmodule (fun g u hu => U.apply_mem_toSubmodule g hu) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem modA_finrank_irred [Nontrivial W]
    (φ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W))
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    finrank (ZMod 2) W = 1 ∨ finrank (ZMod 2) W = 4 ∨ finrank (ZMod 2) W = 16 := by
  obtain ⟨-, i, ⟨e⟩⟩ := a6BinaryRep_complete W (modA_rep φ) (modA_rep_irreducible φ hirr)
  have h := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fin_fun] at h
  fin_cases i <;> simp at h <;> omega

theorem modA_heart [Nontrivial W]
    (φ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W))
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (h4 : finrank (ZMod 2) W = 4) :
    ∃ T : W ≃ₗ[ZMod 2] (Fin 4 → ZMod 2),
      (∀ g w, T (φ g w) = heartHom (g : Perm (Fin 6)) *ᵥ T w) ∨
        ∀ g w, T (φ g w) = heartHom (totalPermHom (g : Perm (Fin 6))) *ᵥ T w := by
  obtain ⟨-, i, ⟨e⟩⟩ := a6BinaryRep_complete W (modA_rep φ) (modA_rep_irreducible φ hirr)
  have hφ : ∀ g w, e (φ g w) = a6BinaryRep i g (e w) := fun g w =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w
  have hrank := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_fin_fun, h4] at hrank
  fin_cases i
  · simp at hrank
  · refine ⟨e.toLinearEquiv, Or.inl fun g w => ?_⟩
    have h := hφ g w
    show e (φ g w) = _
    rw [h]
    show (rep4a g).map (RingHom.id (ZMod 2)) *ᵥ e w = _
    simp [rep4a]
    rfl
  · refine ⟨e.toLinearEquiv, Or.inr fun g w => ?_⟩
    have h := hφ g w
    show e (φ g w) = _
    rw [h]
    show (rep4b g).map (RingHom.id (ZMod 2)) *ᵥ e w = _
    simp [rep4b]
    rfl
  · simp at hrank

theorem modA_coord_mulVec (T : W ≃ₗ[ZMod 2] (Fin 4 → ZMod 2)) (f : W →ₗ[ZMod 2] W) (w : W) :
    LinearMap.toMatrix' (T.toLinearMap ∘ₗ f ∘ₗ T.symm.toLinearMap) *ᵥ T w = T (f w) := by
  have h := Matrix.toLin'_apply (LinearMap.toMatrix' (T.toLinearMap ∘ₗ f ∘ₗ T.symm.toLinearMap))
    (T w)
  rw [Matrix.toLin'_toMatrix'] at h
  rw [← h]
  simp

theorem modA_end_scalar [Nontrivial W]
    (φ : alternatingGroup (Fin 6) →* (W ≃ₗ[ZMod 2] W))
    (hirr : ∀ U : Submodule (ZMod 2) W, (∀ g, ∀ u ∈ U, φ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (h4 : finrank (ZMod 2) W = 4) (f : W →ₗ[ZMod 2] W)
    (hf : ∀ g w, f (φ g w) = φ g (f w)) : f = 0 ∨ f = 1 := by
  obtain ⟨T, hT⟩ := modA_heart φ hirr h4
  set X : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    LinearMap.toMatrix' (T.toLinearMap ∘ₗ f ∘ₗ T.symm.toLinearMap)
  have hX : ∀ w, X *ᵥ T w = T (f w) := fun w => modA_coord_mulVec T f w
  have hcomm : ∀ (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) (g : alternatingGroup (Fin 6)),
      (∀ w, T (φ g w) = M *ᵥ T w) → X * M = M * X := by
    intro M g hM
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨v, rfl⟩ := T.surjective w
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply]
    rw [← hM v, hX, hf, hX, hM]
  have hXc : X = 0 ∨ X = 1 := by
    rcases hT with hT | hT
    · exact commutant_heart_a X (hcomm _ ⟨cyc5, cyc5_mem⟩ (hT ⟨cyc5, cyc5_mem⟩))
        (hcomm _ ⟨cyc3, cyc3_mem⟩ (hT ⟨cyc3, cyc3_mem⟩))
    · exact commutant_heart_b X (hcomm _ ⟨cyc5, cyc5_mem⟩ (hT ⟨cyc5, cyc5_mem⟩))
        (hcomm _ ⟨cyc3, cyc3_mem⟩ (hT ⟨cyc3, cyc3_mem⟩))
  rcases hXc with h | h
  · left
    refine LinearMap.ext fun w => T.injective ?_
    rw [← hX, h]
    simp
  · right
    refine LinearMap.ext fun w => T.injective ?_
    rw [← hX, h]
    simp

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
