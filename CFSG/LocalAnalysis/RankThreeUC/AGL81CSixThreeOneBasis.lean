module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneDefs
import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenListCongr

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631

theorem linearListAt_of_matrixListAt {p : ℕ} [Fact p.Prime]
    (h : ∀ n ≤ 3, MatrixListAt p n) : LinearListAt p := by
  intro W _ _ _ hn H hH
  let n := Module.finrank (ZMod p) W
  have hn' : n ≤ 3 := hn
  let b : Module.Basis (Fin n) (ZMod p) W := Module.finBasisOfFinrankEq (ZMod p) W rfl
  let e : LinearMap.GeneralLinearGroup (ZMod p) W ≃* GL (Fin n) (ZMod p) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm
  haveI : Finite ((Module.End (ZMod p) W)ˣ) :=
    Finite.of_equiv (GL (Fin n) (ZMod p)) e.toEquiv.symm
  let H' : Subgroup (GL (Fin n) (ZMod p)) := H.map e.toMonoidHom
  have hH' : oPPrimeHull p H' = H' := oPPrimeHull_map_eq e.toMonoidHom hH
  have hlist : SixThreeOneList p (↥H' ⧸ CFSG.pCore p ↥H') := h n hn' H' hH'
  obtain ⟨ee⟩ := nonempty_quot_pCore_map_of_injective (p := p) e.toMonoidHom e.injective H
  exact SixThreeOneList.of_mulEquiv ee.symm hlist

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
