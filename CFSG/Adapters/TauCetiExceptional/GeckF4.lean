module

public import CFSG.Adapters.TauCetiExceptional.GeckAssembly

public noncomputable section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.Blueprint.Chevalley Matrix

namespace GeckF4

@[expose] def cartanInv : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, 3, 4, 2; 3, 6, 8, 4; 2, 4, 6, 3; 1, 2, 3, 2]

theorem cartanInv_mul : cartanInv * CartanMatrix.F₄ = 1 := by
  decide

@[expose] def coord (j : Fin 48) : Fin 4 → ℤ :=
  DynkinType.f4Root j ᵥ* cartanInv

@[expose] def certIndex : List ℕ :=
  [0, 1, 2, 3, 10, 8, 17, 7, 25, 15, 5, 16, 24, 13, 31, 22, 21, 36, 30, 40, 44, 35, 39, 43, 4, 6,
    9, 11, 19, 18, 27, 14, 33, 23, 12, 26, 32, 20, 37, 29, 28, 41, 34, 45, 47, 38, 42, 46]

theorem coordCheck_eq_true : GeckRoots.coordCheck f4Certificate certIndex coord = true := by
  decide +kernel

theorem root_eq (j : Fin 48) (l : Fin 4) :
    (DynkinType.F4.simplyConnectedRootDatum DynkinType.valid_F4).root j l =
      ∑ k, coord j k * DynkinType.F4.cartanMatrix k l := by
  rw [DynkinType.simplyConnectedRootDatum_F4, DynkinType.f4SimplyConnectedRootDatum_root,
    DynkinType.cartanMatrix_F4]
  have h : DynkinType.f4Root j l = (coord j ᵥ* CartanMatrix.F₄) l := by
    rw [coord, Matrix.vecMul_vecMul, cartanInv_mul, Matrix.vecMul_one]
  exact h

theorem cartan_eq (i j : Fin 4) : Tag.F4.cartan j i = DynkinType.F4.cartanMatrix i j := by
  rw [DynkinType.cartanMatrix_F4]
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def rootData :
    GeckRoots.RootData .F4 .F4 DynkinType.valid_F4 where
  node := Equiv.refl _
  coord := coord
  root_eq := root_eq
  isRoot := GeckRoots.isRoot_of_coordCheck f4Certificate_check coordCheck_eq_true
  card := rfl
  cartan := cartan_eq

end GeckF4

def geckMatchF4
    : GeckMatch .F4 .F4 DynkinType.valid_F4 :=
  GeckF4.rootData.toGeckMatch

end CFSG.TauCetiBridge
