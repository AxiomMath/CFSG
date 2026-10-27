module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFRRankOrth
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFCField
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoBasic
public import CFSG.RankThree.PartOne.KFR4.Row4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFRRank

open CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem innerThree_catD (k : ℕ) (hk : 5 ≤ k) (hv : (TauCeti.LieTypeIndex.D k gfTwoPP).Valid) :
    InnerThree (TauCeti.ValidLieTypeIndex.Group ⟨.D k gfTwoPP, hv⟩) := by
  have h : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group ⟨.D k gfTwoPP, hv⟩)
      .POmegaPlus k 2 1 :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD k gfTwoPP hv (MulEquiv.refl _)
  intro β hβ
  obtain ⟨s, hs⟩ := CFSG.HardMathSupport.Dickson.Bal207.OrthFC.orthTwoInner_holds _ .POmegaPlus k
    (Or.inl rfl) hk h β hβ
  exact ⟨s, hs.symm⟩

theorem innerThree_catTwistedD (k : ℕ) (hk : 5 ≤ k)
    (hv : (TauCeti.LieTypeIndex.twistedD k gfTwoPP).Valid) :
    InnerThree (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD k gfTwoPP, hv⟩) := by
  have h : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD k gfTwoPP, hv⟩)
      .POmegaMinus k 2 1 :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD k gfTwoPP hv (MulEquiv.refl _)
  intro β hβ
  obtain ⟨s, hs⟩ := CFSG.HardMathSupport.Dickson.Bal207.OrthFC.orthTwoInner_holds _ .POmegaMinus k
    (Or.inr rfl) hk h β hβ
  exact ⟨s, hs.symm⟩

theorem coreThree_catD (k : ℕ) (hk : 5 ≤ k) (hv : (TauCeti.LieTypeIndex.D k gfTwoPP).Valid) :
    CoreThree (TauCeti.ValidLieTypeIndex.Group ⟨.D k gfTwoPP, hv⟩) := by
  have h : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group ⟨.D k gfTwoPP, hv⟩)
      .POmegaPlus k 2 1 :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD k gfTwoPP hv (MulEquiv.refl _)
  have h0 := h
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h0
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  haveI := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.charP_two hK2
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_plus h K hK e
  haveI : Nonempty (Fin (2 * k)) := ⟨⟨0, by omega⟩⟩
  exact coreThree_of_mulEquiv (((coordinatePlusWitnessEquiv K e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge _ (by omega))).trans
      (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hnd).symm)
    (coreThree_orth hK2 hnd (by rw [Module.finrank_fin_fun]; omega))

theorem coreThree_catTwistedD (k : ℕ) (hk : 5 ≤ k)
    (hv : (TauCeti.LieTypeIndex.twistedD k gfTwoPP).Valid) :
    CoreThree (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD k gfTwoPP, hv⟩) := by
  have h : StatedClassicalModel (TauCeti.ValidLieTypeIndex.Group ⟨.twistedD k gfTwoPP, hv⟩)
      .POmegaMinus k 2 1 :=
    CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD k gfTwoPP hv (MulEquiv.refl _)
  have h0 := h
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h0
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  haveI := CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two.charP_two hK2
  have hn1 : 1 ≤ k := by omega
  obtain ⟨-, hnd, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  haveI : Nonempty (Fin (2 * k)) := ⟨⟨0, by omega⟩⟩
  exact coreThree_of_mulEquiv (((coordinateMinusWitnessEquiv K hn1 b c e).trans
    (CFSG.RankThree.PartOne.KCOrthogonalAut.coordBridge _ (by omega))).trans
      (CFSG.RankThree.PartOne.KFR4.orthDerivedEquivProj hnd).symm)
    (coreThree_orth hK2 hnd (by rw [Module.finrank_fin_fun]; omega))

end CFSG.LocalAnalysis.GLTheoremA.SFRRank

end
