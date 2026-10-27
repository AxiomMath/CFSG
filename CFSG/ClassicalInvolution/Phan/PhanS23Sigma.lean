module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.ClassicalInvolution.Phan.PhanS19Gf
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

@[expose] noncomputable def qF : QuadraticForm (ZMod 7) (Fin 7 → ZMod 7) :=
  QuadraticMap.weightedSumSquares (ZMod 7) (![1, 1, 1, 1, 1, 1, -1] : Fin 7 → ZMod 7)

@[expose] def FamilyWitt7 : Prop :=
  ∀ (ι : Type) [Fintype ι] (v w : ι → Fin 7 → ZMod 7),
    (∀ i j, QuadraticMap.polar qF (v i) (v j) = QuadraticMap.polar qF (w i) (w j)) →
    (∀ c : ι → ZMod 7, ∑ i, c i • v i = 0 ↔ ∑ i, c i • w i = 0) →
    ∃ e : qF.IsometryEquiv qF, ∀ i, e (v i) = w i

namespace Descent

theorem polar_qF (x y : Fin 7 → ZMod 7) :
    QuadraticMap.polar qF x y =
      2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 + x 4 * y 4 + x 5 * y 5 - x 6 * y 6) := by
  simp only [QuadraticMap.polar, qF, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_seven,
    Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem polar_isometry (e : qF.IsometryEquiv qF) (x y : Fin 7 → ZMod 7) :
    QuadraticMap.polar qF (e x) (e y) = QuadraticMap.polar qF x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add e x y,
    QuadraticMap.IsometryEquiv.map_app, QuadraticMap.IsometryEquiv.map_app,
    QuadraticMap.IsometryEquiv.map_app]

@[expose] def polarK (u v : Fin 7 → GF49) : GF49 :=
  2 * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2 + u 3 * v 3 + u 4 * v 4 + u 5 * v 5 - u 6 * v 6)

@[expose] def starV (u : Fin 7 → GF49) : Fin 7 → GF49 := fun j => star (u j)

@[expose] def reV (u : Fin 7 → GF49) : Fin 7 → ZMod 7 := fun j => (u j).re

@[expose] def imV (u : Fin 7 → GF49) : Fin 7 → ZMod 7 := fun j => (u j).im

theorem ext_reV_imV {u v : Fin 7 → GF49} (h1 : reV u = reV v) (h2 : imV u = imV v) : u = v := by
  funext j
  exact QuadraticAlgebra.ext (congrFun h1 j) (congrFun h2 j)

theorem reV_starV (u : Fin 7 → GF49) : reV (starV u) = reV u := by
  funext j
  simp [reV, starV]

theorem imV_starV (u : Fin 7 → GF49) : imV (starV u) = -imV u := by
  funext j
  simp [imV, starV]

theorem polarK_re (u v : Fin 7 → GF49) :
    (polarK u v).re =
      QuadraticMap.polar qF (reV u) (reV v) - QuadraticMap.polar qF (imV u) (imV v) := by
  simp only [polarK, polar_qF, reV, imV, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_ofNat]
  ring

theorem polarK_im (u v : Fin 7 → GF49) :
    (polarK u v).im =
      QuadraticMap.polar qF (reV u) (imV v) + QuadraticMap.polar qF (imV u) (reV v) := by
  simp only [polarK, polar_qF, reV, imV, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_ofNat]
  ring

theorem polarK_starV_re (u v : Fin 7 → GF49) :
    (polarK u (starV v)).re =
      QuadraticMap.polar qF (reV u) (reV v) + QuadraticMap.polar qF (imV u) (imV v) := by
  simp only [polarK, polar_qF, starV, reV, imV, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_ofNat,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring

theorem polarK_starV_im (u v : Fin 7 → GF49) :
    (polarK u (starV v)).im =
      QuadraticMap.polar qF (imV u) (reV v) - QuadraticMap.polar qF (reV u) (imV v) := by
  simp only [polarK, polar_qF, starV, reV, imV, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_add,
    QuadraticAlgebra.re_sub, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.im_add, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_ofNat,
    QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring

end Descent

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
