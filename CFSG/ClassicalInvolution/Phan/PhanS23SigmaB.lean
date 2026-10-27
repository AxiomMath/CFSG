module

public import CFSG.ClassicalInvolution.Phan.PhanS23Sigma

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Descent

theorem re_sum {α : Type*} (s : Finset α) (g : α → GF49) :
    (∑ x ∈ s, g x).re = ∑ x ∈ s, (g x).re :=
  map_sum (QuadraticAlgebra.reₗ (-1 : ZMod 7) 0) g s

theorem im_sum {α : Type*} (s : Finset α) (g : α → GF49) :
    (∑ x ∈ s, g x).im = ∑ x ∈ s, (g x).im :=
  map_sum (QuadraticAlgebra.imₗ (-1 : ZMod 7) 0) g s

noncomputable def extLin (f : (Fin 7 → ZMod 7) →ₗ[ZMod 7] (Fin 7 → ZMod 7)) :
    (Fin 7 → GF49) →ₗ[GF49] (Fin 7 → GF49) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap (ZMod 7) GF49))

theorem reV_extLin (f : (Fin 7 → ZMod 7) →ₗ[ZMod 7] (Fin 7 → ZMod 7)) (u : Fin 7 → GF49) :
    reV (extLin f u) = f (reV u) := by
  funext j
  rw [← LinearMap.toMatrix'_mulVec f (reV u)]
  simp [extLin, Matrix.mulVec, dotProduct, reV, re_sum]

theorem imV_extLin (f : (Fin 7 → ZMod 7) →ₗ[ZMod 7] (Fin 7 → ZMod 7)) (u : Fin 7 → GF49) :
    imV (extLin f u) = f (imV u) := by
  funext j
  rw [← LinearMap.toMatrix'_mulVec f (imV u)]
  simp [extLin, Matrix.mulVec, dotProduct, imV, im_sum]

noncomputable def extEquiv (e : qF.IsometryEquiv qF) :
    (Fin 7 → GF49) ≃ₗ[GF49] (Fin 7 → GF49) :=
  LinearEquiv.ofLinearMap
    (extLin (e.toLinearEquiv : (Fin 7 → ZMod 7) →ₗ[ZMod 7] (Fin 7 → ZMod 7)))
    (extLin (e.symm.toLinearEquiv : (Fin 7 → ZMod 7) →ₗ[ZMod 7] (Fin 7 → ZMod 7)))
    (LinearMap.ext fun u => ext_reV_imV (by simp [reV_extLin]) (by simp [imV_extLin]))
    (LinearMap.ext fun u => ext_reV_imV (by simp [reV_extLin]) (by simp [imV_extLin]))

theorem reV_extEquiv (e : qF.IsometryEquiv qF) (u : Fin 7 → GF49) :
    reV (extEquiv e u) = e (reV u) := reV_extLin _ u

theorem imV_extEquiv (e : qF.IsometryEquiv qF) (u : Fin 7 → GF49) :
    imV (extEquiv e u) = e (imV u) := imV_extLin _ u

theorem polarK_extEquiv (e : qF.IsometryEquiv qF) (u v : Fin 7 → GF49) :
    polarK (extEquiv e u) (extEquiv e v) = polarK u v := by
  refine QuadraticAlgebra.ext ?_ ?_
  · simp only [polarK_re, reV_extEquiv, imV_extEquiv, polar_isometry]
  · simp only [polarK_im, reV_extEquiv, imV_extEquiv, polar_isometry]

theorem starV_extEquiv (e : qF.IsometryEquiv qF) (u : Fin 7 → GF49) :
    extEquiv e (starV u) = starV (extEquiv e u) := by
  refine ext_reV_imV ?_ ?_
  · simp only [reV_extEquiv, reV_starV]
  · simp only [imV_extEquiv, imV_starV, map_neg]

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Descent
