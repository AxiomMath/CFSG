module

public import CFSG.Adapters.TauCetiExceptional.GeckAssembly

public noncomputable section

namespace CFSG.TauCetiBridge

open TauCeti CFSG.Blueprint.Chevalley Matrix

namespace GeckG2

@[expose] def coord : Fin 12 → Fin 2 → ℤ :=
  ![![0, 1], ![1, 0], ![1, 1], ![1, 2], ![1, 3], ![2, 3], ![0, -1], ![-1, 0], ![-1, -1],
    ![-1, -2], ![-1, -3], ![-2, -3]]

@[expose] def node : Fin 2 ≃ Fin 2 :=
  Equiv.swap 0 1

@[expose] def certIndex : List ℕ :=
  [1, 0, 4, 8, 3, 7, 5, 2, 9, 11, 6, 10]

theorem coordCheck_eq_true : GeckRoots.coordCheck g2Certificate certIndex coord = true := by
  decide +kernel

theorem root_eq (j : Fin 12) (l : Fin 2) :
    (DynkinType.G2.simplyConnectedRootDatum DynkinType.valid_G2).root j l =
      ∑ k, coord j (node k) * DynkinType.G2.cartanMatrix k l := by
  rw [DynkinType.simplyConnectedRootDatum_G2, DynkinType.g2SimplyConnectedRootDatum_root,
    DynkinType.cartanMatrix_G2]
  have h : DynkinType.g2Root j l =
      ∑ k, coord j (node k) * CartanMatrix.G₂ᵀ k l := by
    rw [DynkinType.g2Root_apply, Fin.sum_univ_two]
    fin_cases j <;> fin_cases l <;> rfl
  exact h

theorem cartan_eq (i j : Fin 2) :
    Tag.G2.cartan (node j) (node i) = DynkinType.G2.cartanMatrix i j := by
  rw [DynkinType.cartanMatrix_G2]
  fin_cases i <;> fin_cases j <;> rfl

@[expose] def rootData :
    GeckRoots.RootData .G2 .G2 DynkinType.valid_G2 where
  node := node
  coord := coord
  root_eq := root_eq
  isRoot := GeckRoots.isRoot_of_coordCheck g2Certificate_check coordCheck_eq_true
  card := rfl
  cartan := cartan_eq

end GeckG2

def geckMatchG2
    : GeckMatch .G2 .G2 DynkinType.valid_G2 :=
  GeckG2.rootData.toGeckMatch

end CFSG.TauCetiBridge
