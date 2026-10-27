module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Perp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

open CFSG.LocalAnalysis.GLTheoremA.CatB Module Matrix CFSG.Open

@[expose] noncomputable def glK : GL (Fin 6) K4 →* Module.End K4 (Fin 6 → K4) where
  toFun g := Matrix.mulVecLin (g : Matrix (Fin 6) (Fin 6) K4)
  map_one' := by
    ext x i
    simp
  map_mul' g h := by
    rw [Units.val_mul, Matrix.mulVecLin_mul]
    rfl

theorem glK_apply (g : GL (Fin 6) K4) (x : Fin 6 → K4) :
    glK g x = (g : Matrix (Fin 6) (Fin 6) K4) *ᵥ x := rfl

theorem glK_injective : Function.Injective glK := by
  intro g h hgh
  apply Units.ext
  ext i j
  have := congrFun (congrArg (fun f : Module.End K4 (Fin 6 → K4) => f (Pi.single j 1)) hgh) i
  simpa [glK_apply, Matrix.mulVec_single_one] using this

theorem glK_det (g : GL (Fin 6) K4) :
    LinearMap.det (glK g) = (g : Matrix (Fin 6) (Fin 6) K4).det := by
  have : glK g = Matrix.toLin' (g : Matrix (Fin 6) (Fin 6) K4) := rfl
  rw [this, LinearMap.det_toLin']

theorem hermF_glK {g : GL (Fin 6) K4}
    (hg : ((g : Matrix (Fin 6) (Fin 6) K4).map (· ^ 2))ᵀ * (g : Matrix (Fin 6) (Fin 6) K4) = 1)
    (x y : Fin 6 → K4) :
    hermF (glK g x) (glK g y) = hermF x y := by
  unfold hermF
  rw [glK_apply, glK_apply]
  exact herm_mulVec hg x y

@[expose] noncomputable def rhoG : ↥(StatedSU 6 (2 ^ 1) K4) →* Module.End K4 (Fin 6 → K4) :=
  glK.comp (StatedSU 6 (2 ^ 1) K4).subtype

theorem rhoG_apply (g : ↥(StatedSU 6 (2 ^ 1) K4)) (x : Fin 6 → K4) :
    rhoG g x = ((g : GL (Fin 6) K4) : Matrix (Fin 6) (Fin 6) K4) *ᵥ x := rfl

theorem rhoG_injective : Function.Injective rhoG := by
  intro g h hgh
  exact Subtype.ext (glK_injective hgh)

theorem su_unitary (g : ↥(StatedSU 6 (2 ^ 1) K4)) :
    ((((g : GL (Fin 6) K4) : Matrix (Fin 6) (Fin 6) K4)).map (· ^ 2))ᵀ *
      ((g : GL (Fin 6) K4) : Matrix (Fin 6) (Fin 6) K4) = 1 := by
  have h := (mem_statedSU_K4 (m := 6) (by norm_num) g.2).2
  exact h

theorem su_det (g : ↥(StatedSU 6 (2 ^ 1) K4)) :
    ((g : GL (Fin 6) K4) : Matrix (Fin 6) (Fin 6) K4).det = 1 :=
  (mem_statedSU_K4 (m := 6) (by norm_num) g.2).1

theorem rhoG_herm (g : ↥(StatedSU 6 (2 ^ 1) K4)) (x y : Fin 6 → K4) :
    hermF (rhoG g x) (rhoG g y) = hermF x y :=
  hermF_glK (su_unitary g) x y

theorem rhoG_det (g : ↥(StatedSU 6 (2 ^ 1) K4)) : LinearMap.det (rhoG g) = 1 := by
  show LinearMap.det (glK g.1) = 1
  rw [glK_det, su_det]

@[expose] def fixSub (H : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)) : Submodule K4 (Fin 6 → K4) where
  carrier := {v | ∀ h ∈ H, rhoG h v = v}
  add_mem' := by
    intro v w hv hw h hh
    rw [map_add, hv h hh, hw h hh]
  zero_mem' := by
    intro h _
    simp
  smul_mem' := by
    intro c v hv h hh
    rw [map_smul, hv h hh]

theorem mem_fixSub {H : Subgroup ↥(StatedSU 6 (2 ^ 1) K4)} {v : Fin 6 → K4} :
    v ∈ fixSub H ↔ ∀ h ∈ H, rhoG h v = v := Iff.rfl

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

end
