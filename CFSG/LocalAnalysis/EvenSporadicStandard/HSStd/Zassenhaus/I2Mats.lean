module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.I2Facts

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2

@[expose] def rho : Fin 2 → Mat :=
  ![!![1, 0, 1, 1; 0, 0, 1, 0; 1, 1, 0, 0; 1, 1, 1, 1],
    !![0, 1, 1, 1; 1, 1, 1, 1; 1, 0, 1, 0; 1, 1, 0, 0]]

@[expose] def kx : Mat := !![1, 0, 0, 0; 1, 1, 0, 0; 1, 0, 0, 1; 1, 0, 1, 0]

@[expose] def ky : Mat := !![1, 0, 0, 0; 1, 1, 1, 1; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def lift (A : Mat) : Matrix (Fin 4) (Fin 4) (ZMod 4) :=
  A.map fun b => ((b.val : ℕ) : ZMod 4)

theorem exists_lift {x : Mat} {X : Matrix (Fin 4) (Fin 4) (ZMod 4)} (h : red X = x) :
    ∃ A : Mat, X = lift x + (2 : ZMod 4) • lift A := by
  have key : ∀ a : ZMod 4, ∃ c : ZMod 2,
      a = (((ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) a).val : ℕ) : ZMod 4) +
        2 * ((c.val : ℕ) : ZMod 4) := by decide
  choose c hc using fun i j => key (X i j)
  refine ⟨Matrix.of c, ?_⟩
  ext i j
  have h1 : ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) (X i j) = x i j := by
    simpa [red] using congrFun (congrFun h i) j
  have := hc i j
  rw [h1] at this
  simpa [lift, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using this

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.I2
