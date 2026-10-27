module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

@[expose] def SemilinD4EightAut (S : Type) [Group S] (φ : MulAut S) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (e : S ≃* StatedProj (StatedOmega (StatedQuadPlus 4 F))),
    Nat.card F = 8 ∧
      MulAut.congr (coordinatePlusWitnessEquiv F e) φ ∈
        matrixProjectiveImage (coordinateQuadPlus 4 F)

@[expose] def NonSemilinD4Eight (S : Type) [Group S] (φ : MulAut S) : Prop :=
  ¬ SemilinD4EightAut S φ

theorem mulAut_congr_symm_trans {S S' M : Type} [Group S] [Group S'] [Group M] (g : S ≃* S')
    (E : S ≃* M) (φ : MulAut S) :
    MulAut.congr (g.symm.trans E) (MulAut.congr g φ) = MulAut.congr E φ := by
  ext x
  simp [MulAut.congr_apply]

theorem SemilinD4EightAut.of_mulEquiv {S S' : Type} [Group S] [Group S'] {φ : MulAut S}
    (h : SemilinD4EightAut S φ) (g : S ≃* S') : SemilinD4EightAut S' (MulAut.congr g φ) := by
  obtain ⟨F, _, _, e, hF, hφ⟩ := h
  refine ⟨F, inferInstance, inferInstance, g.symm.trans e, hF, ?_⟩
  have hc : coordinatePlusWitnessEquiv F (g.symm.trans e) =
      g.symm.trans (coordinatePlusWitnessEquiv F e) := rfl
  rw [hc, mulAut_congr_symm_trans]
  exact hφ

theorem nonSemilinD4Eight_congr {S S' : Type} [Group S] [Group S'] (g : S ≃* S') {φ : MulAut S}
    (h : NonSemilinD4Eight S φ) : NonSemilinD4Eight S' (MulAut.congr g φ) := by
  intro h'
  apply h
  have h2 := h'.of_mulEquiv g.symm
  have h3 : MulAut.congr g.symm (MulAut.congr g φ) = φ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [h3] at h2

end CFSG.HardMathSupport.Dickson.Bal207
