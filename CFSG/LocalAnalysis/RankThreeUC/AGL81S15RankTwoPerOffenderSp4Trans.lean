module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.Quasithin.Background.SmithB42Sp4Nat

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.ComponentClassification.UnbalancedCatalog.SpChain Matrix

private theorem sp4t_funCongrLeft_symm_apply {K : Type} [Field K]
    (w : Fin 2 ⊕ Fin 2 → K) (i : Fin 4) :
    ((LinearEquiv.funCongrLeft K K antiIdx).symm w) i = w (antiIdx.symm i) := by
  simp [LinearEquiv.funCongrLeft_symm, LinearMap.funLeft_apply]

private theorem sp4t_coord_submatrix_mulVec {K : Type} [Field K]
    (M : Matrix (Fin 4) (Fin 4) K) (w : Fin 2 ⊕ Fin 2 → K) :
    (LinearEquiv.funCongrLeft K K antiIdx).symm
        ((M.submatrix antiIdx antiIdx) *ᵥ w) =
      M *ᵥ ((LinearEquiv.funCongrLeft K K antiIdx).symm w) := by
  have hP : (LinearEquiv.funCongrLeft K K antiIdx).symm w = w ∘ antiIdx.symm := by
    funext j
    rw [sp4t_funCongrLeft_symm_apply]
    rfl
  rw [Matrix.submatrix_mulVec_equiv]
  ext i
  rw [sp4t_funCongrLeft_symm_apply, hP]
  simp

theorem exists_mat_antiSp_of_natural {G : Type*} [Group G] {L : Subgroup G} {F : Type}
    [Field F] [CharP F 2] (e : ↥L ≃* StatedSp 2 F) (α : MulAut (StatedSp 2 F)) :
    ∃ (Mat : ↥L →* Matrix.GeneralLinearGroup (Fin 4) F) (P : (Fin 2 ⊕ Fin 2 → F) ≃+ (Fin 4 → F)),
      Function.Injective Mat ∧ Mat.range = antiSp F ∧
      ∀ (l : ↥L) (w : Fin 2 ⊕ Fin 2 → F),
        P ((CFSG.Quasithin.B42Sp4.spM (α (e l))).mulVec w) =
          (Mat l : Matrix (Fin 4) (Fin 4) F) *ᵥ P w := by
  let θ : StatedSp 2 F ≃* antiSp F := (antiSpEquiv F).symm
  let Mat : ↥L →* Matrix.GeneralLinearGroup (Fin 4) F :=
    (antiSp F).subtype.comp (θ.toMonoidHom.comp (α.toMonoidHom.comp e.toMonoidHom))
  let P : (Fin 2 ⊕ Fin 2 → F) ≃+ (Fin 4 → F) :=
    (LinearEquiv.funCongrLeft F F antiIdx).symm.toAddEquiv
  refine ⟨Mat, P, ?_, ?_, ?_⟩
  · intro l₁ l₂ h
    have h' : θ (α (e l₁)) = θ (α (e l₂)) := Subtype.ext h
    exact e.injective (α.injective (θ.injective h'))
  · ext g
    constructor
    · intro hg
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hg
      exact (θ (α (e l))).2
    · intro hg
      refine MonoidHom.mem_range.mpr ⟨e.symm (α.symm (antiSpEquiv F ⟨g, hg⟩)), ?_⟩
      change ((antiSpEquiv F).symm
        (α (e (e.symm (α.symm (antiSpEquiv F ⟨g, hg⟩))))) : GL (Fin 4) F) = g
      simp
  · intro l w
    let g : antiSp F := (antiSpEquiv F).symm (α (e l))
    have hg : antiSpEquiv F g = α (e l) := by
      dsimp [g]
      rw [MulEquiv.apply_symm_apply]
    have hsp : CFSG.Quasithin.B42Sp4.spM (α (e l)) =
        (glMat g).submatrix antiIdx antiIdx := by
      rw [← hg]
      exact spMat_antiSpEquiv g
    calc
      P ((CFSG.Quasithin.B42Sp4.spM (α (e l))).mulVec w)
          = (LinearEquiv.funCongrLeft F F antiIdx).symm
              (((glMat g).submatrix antiIdx antiIdx) *ᵥ w) := by
            rw [hsp]
            rfl
      _ = (glMat g) *ᵥ ((LinearEquiv.funCongrLeft F F antiIdx).symm w) :=
            sp4t_coord_submatrix_mulVec (K := F) (M := glMat g) (w := w)
      _ = (Mat l : Matrix (Fin 4) (Fin 4) F) *ᵥ P w := by
            rfl

end CFSG.LocalAnalysis.RankThreeUC.S15

end
