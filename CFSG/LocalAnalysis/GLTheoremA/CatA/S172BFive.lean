module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BCentSolv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.S172B

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.Open CFSG.Yardstones.Md0ec50421ce4
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S172X
  CFSG.LocalAnalysis.GLTheoremA.S172B.Cent

theorem modelSolvable_orthDerived_five {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 2) V = 2 * 5) (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q)
    (hbound : ∀ E : Subgroup ↥(orthDerived Q), CFSG.Open.IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ (5 - 1))
    (hb : CatDistinct.OrderBridge) :
    ModelSolvable 3 ↥(orthDerived Q) 4 (isUnA 4 2) := by
  intro Bb hBb hcard d hd hLd hcd e he hed
  obtain ⟨l, hF⟩ := exists_frame_of_card hQ hbound hBb hcard
  have hfull := fullSupport_of_layerIs hQ hdim hplus (le_refl 5) hb hF hd hLd hcd
  exact isSolvable_centralizer_pair_of_fullSupport hQ (by omega) hF hd he hfull hed

end CFSG.LocalAnalysis.GLTheoremA.S172B

end
