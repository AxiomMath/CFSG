module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4K1
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3D4Ker
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Solv
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Transfer

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3.D4

open CFSG.Blueprint.Chevalley Matrix Subgroup

variable (K : Type) [Field K]

@[expose] def compatSubgroup : Subgroup (ModGL Tag.D4 K × GL (Fin 8) K) where
  carrier := {x | phi K ∘ₗ (x.1 : Module.End K (RootModule Tag.D4 K)) =
      rho K (x.2 : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K ∧
    (x.2 : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (x.2 : Matrix (Fin 8) (Fin 8) K) =
      castM K BZ}
  mul_mem' := by
    rintro ⟨g, s⟩ ⟨g', s'⟩ ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨?_, ?_⟩
    · show phi K ∘ₗ ((g * g' : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) =
        rho K ((s * s' : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K
      have h1' : phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K)) =
        rho K (s : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K := h1
      have h1'' : phi K ∘ₗ (g' : Module.End K (RootModule Tag.D4 K)) =
        rho K (s' : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K := k1
      rw [Units.val_mul, Units.val_mul, rho_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
        ← LinearMap.comp_assoc, h1', LinearMap.comp_assoc, h1'', LinearMap.comp_assoc]
    · show ((s * s' : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
        ((s * s' : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) = castM K BZ
      have h2s : (s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (s : Matrix (Fin 8) (Fin 8) K) =
        castM K BZ := h2
      have h2s' : (s' : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
        (s' : Matrix (Fin 8) (Fin 8) K) = castM K BZ := k2
      calc ((s * s' : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
            ((s * s' : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)
          = (s' : Matrix (Fin 8) (Fin 8) K)ᵀ * ((s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
              (s : Matrix (Fin 8) (Fin 8) K)) * (s' : Matrix (Fin 8) (Fin 8) K) := by
            simp only [Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = castM K BZ := by rw [h2s]; exact h2s'
  one_mem' := by
    refine ⟨?_, ?_⟩
    · show phi K ∘ₗ ((1 : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) =
        rho K ((1 : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K
      rw [Units.val_one, Units.val_one, rho_one]
      ext v
      simp
    · show ((1 : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
        ((1 : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) = castM K BZ
      simp
  inv_mem' := by
    rintro ⟨g, s⟩ ⟨h1, h2⟩
    have h1' : phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K)) =
        rho K (s : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K := h1
    have h2s : (s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (s : Matrix (Fin 8) (Fin 8) K) =
        castM K BZ := h2
    refine ⟨?_, ?_⟩
    · show phi K ∘ₗ ((g⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) =
        rho K ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K
      have e1 : rho K ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *
          rho K (s : Matrix (Fin 8) (Fin 8) K) = 1 := by
        rw [← rho_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, rho_one]
      have e2 : ((g : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) *
          ((g⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc phi K ∘ₗ ((g⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))
          = (rho K ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) *
              rho K (s : Matrix (Fin 8) (Fin 8) K)) ∘ₗ
              (phi K ∘ₗ ((g⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))) := by
            rw [e1, Module.End.one_eq_id, LinearMap.id_comp]
        _ = rho K ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ∘ₗ
              ((phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K))) ∘ₗ
                ((g⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K))) := by
            simp only [h1', Module.End.mul_eq_comp, LinearMap.comp_assoc]
        _ = rho K ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K := by
            rw [LinearMap.comp_assoc, ← Module.End.mul_eq_comp, e2, Module.End.one_eq_id,
              LinearMap.comp_id]
    · show ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
        ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) = castM K BZ
      have hs : (s : Matrix (Fin 8) (Fin 8) K) * ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) =
          1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ *
            ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)
          = ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)ᵀ *
              ((s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (s : Matrix (Fin 8) (Fin 8) K)) *
              ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) := by rw [h2s]
        _ = ((s : Matrix (Fin 8) (Fin 8) K) * ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K))ᵀ *
              castM K BZ * ((s : Matrix (Fin 8) (Fin 8) K) *
                ((s⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K)) := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = castM K BZ := by rw [hs]; simp

theorem exists_transfer_D4 (Y : Subgroup (ModGL Tag.D4 K)) (hYle : Y ≤ adjointGroup Tag.D4 K)
    (hY : CFSG.IsQuasisimple Y) :
    ∃ Y₂ : Subgroup (GL (Fin 8) K),
      (∀ s ∈ Y₂, (s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (s : Matrix (Fin 8) (Fin 8) K) =
        castM K BZ) ∧ CFSG.IsQuasisimple Y₂ ∧
      Nonempty (↥Y₂ ⧸ center ↥Y₂ ≃* ↥Y ⧸ center ↥Y) := by
  classical
  let gens : Set (ModGL Tag.D4 K × GL (Fin 8) K) :=
    {x | ∃ (i : Fin 4) (c : K),
      ((x.1 : Module.End K (RootModule Tag.D4 K)) = xOp Tag.D4 K i c ∧ x.2 = gX K i c) ∨
      ((x.1 : Module.End K (RootModule Tag.D4 K)) = yOp Tag.D4 K i c ∧ x.2 = gY K i c)}
  set R : Subgroup (ModGL Tag.D4 K × GL (Fin 8) K) := Subgroup.closure gens with hR
  have hgenP : gens ⊆ compatSubgroup K := by
    rintro ⟨g, s⟩ ⟨i, c, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · refine ⟨?_, ?_⟩
      · have h1' : (g : Module.End K (RootModule Tag.D4 K)) = xOp Tag.D4 K i c := h1
        have h2' : s = gX K i c := h2
        show phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K)) =
          rho K (s : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K
        rw [h1', h2']
        exact phi_compat_xOp K i c
      · have h2' : s = gX K i c := h2
        show (s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (s : Matrix (Fin 8) (Fin 8) K) = _
        rw [h2']
        exact gX_orth K i c
    · refine ⟨?_, ?_⟩
      · have h1' : (g : Module.End K (RootModule Tag.D4 K)) = yOp Tag.D4 K i c := h1
        have h2' : s = gY K i c := h2
        show phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K)) =
          rho K (s : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K
        rw [h1', h2']
        exact phi_compat_yOp K i c
      · have h2' : s = gY K i c := h2
        show (s : Matrix (Fin 8) (Fin 8) K)ᵀ * castM K BZ * (s : Matrix (Fin 8) (Fin 8) K) = _
        rw [h2']
        exact gY_orth K i c
  have hRP : R ≤ compatSubgroup K := (Subgroup.closure_le _).mpr hgenP
  have hAdj : adjointGroup Tag.D4 K ≤ R.map (MonoidHom.fst _ _) := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, c, hg | hg⟩
    · exact ⟨(g, gX K i c), Subgroup.subset_closure ⟨i, c, Or.inl ⟨hg, rfl⟩⟩, rfl⟩
    · exact ⟨(g, gY K i c), Subgroup.subset_closure ⟨i, c, Or.inr ⟨hg, rfl⟩⟩, rfl⟩
  have hYR : ∀ y ∈ Y, ∃ s, (y, s) ∈ R := by
    intro y hy
    obtain ⟨⟨y', s⟩, hys, hy'⟩ := hAdj (hYle hy)
    have : y' = y := hy'
    subst this
    exact ⟨s, hys⟩
  have hK1 : ∀ h : GL (Fin 8) K, (1, h) ∈ R → h ∈ center (GL (Fin 8) K) := by
    intro h hh
    obtain ⟨h1, _⟩ := hRP hh
    apply phi_fix_scalar K h
    have h1' : phi K ∘ₗ ((1 : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) =
        rho K (h : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K := h1
    rw [Units.val_one, Module.End.one_eq_id, LinearMap.comp_id] at h1'
    exact h1'.symm
  have hK2 : Group.IsSolvable ↥(R.comap (MonoidHom.inl (ModGL Tag.D4 K) (GL (Fin 8) K))) := by
    have hle : R.comap (MonoidHom.inl (ModGL Tag.D4 K) (GL (Fin 8) K)) ≤ stabilizerOf (phi K) := by
      intro g hg
      obtain ⟨h1, _⟩ := hRP hg
      have h1' : phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K)) =
          rho K ((1 : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K) ∘ₗ phi K := h1
      show phi K ∘ₗ (g : Module.End K (RootModule Tag.D4 K)) = phi K
      rw [h1', Units.val_one, rho_one, Module.End.one_eq_id, LinearMap.id_comp]
    haveI := isSolvable_stabilizerOf (phi K)
      (hVec Tag.D4 K (1 : Fin 4) + hVec Tag.D4 K (3 : Fin 4)) (fun v hv => phi_ker_le_span K hv)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  obtain ⟨Y₂, hY₂, hq, he⟩ := exists_quasisimple_of_relation R hK1 hK2 Y hY hYR
  exact ⟨Y₂, fun s hs => by obtain ⟨g, hg⟩ := hY₂ s hs; exact (hRP hg).2, hq, he⟩

end CFSG.ComponentClassification.CatFC.KGHS3.D4
