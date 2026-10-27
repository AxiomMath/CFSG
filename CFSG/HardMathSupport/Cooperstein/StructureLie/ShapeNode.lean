module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ChevNoAlt
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeOfTransvection
public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeData
import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalIdentification
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthogonalCentre
import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeBlocksAux

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.AGLEmbedding (Asc81bHyp IsWeakSBlock barM IsClassicalTwoOrG2 IsOrthogonalTwo blockV)

theorem finite_glt (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] : Finite (LinearMap.GeneralLinearGroup (ZMod 2) W) := by
  have : Finite W := Module.finite_of_finite (ZMod 2)
  have : Finite (W →ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : W →ₗ[ZMod 2] W => (f : W → W)) DFunLike.coe_injective
  exact Finite.of_injective (Units.val : (W →ₗ[ZMod 2] W)ˣ → _) Units.val_injective

theorem ShapeOut.finite {Y : Type} [Group Y] (h : ShapeOut Y) : Finite Y := by
  rcases h with ⟨W, i1, i2, i3, Q, -, ⟨e⟩⟩ | ⟨W, i1, i2, i3, f, -, -, -, ⟨e⟩⟩ | ⟨m, -, ⟨e⟩⟩
  · have := finite_glt W
    exact Finite.of_injective e (e.injective)
  · have := finite_glt W
    exact Finite.of_injective e (e.injective)
  · exact Finite.of_injective e e.injective

theorem eightEightShapeNoAlt
    : EightEightShapeNoAlt := by
  intro G _ _ X S L hX hA hL _ hAlt ht
  obtain ⟨Y, _, hY, ⟨e1⟩⟩ := shapeOut_of_transvectionData hX hA hL ht
  have hSL := CFSG.HardMathSupport.Cooperstein.Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨e2⟩ := CFSG.HardMathSupport.Cooperstein.Coordinator.nonempty_autOnCenterQuotientEquiv
    hA hL hSL
  have e3 : (Y ⧸ Subgroup.center Y) ≃* (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)) :=
    e1.symm.trans e2
  have hq := CFSG.HardMathSupport.Cooperstein.Coordinator.isQuasisimple_of_open' hL.component.2.2
  have hsimp : IsSimpleGroup (Y ⧸ Subgroup.center Y) := by
    have := hq.2.1
    exact e3.isSimpleGroup
  have hnonab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    simpa using congrArg e3 h
  have hAltY : ∀ m : ℕ, (m = 7 ∨ 9 ≤ m) →
      IsEmpty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin m)) := fun m hm =>
    ⟨fun e => (hAlt m hm).false (e3.symm.trans e)⟩
  have := hY.finite
  obtain ⟨hc, hO⟩ := isOrthogonalTwo_of_shapeOut hY hsimp hnonab hAltY
  have eY : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans (QuotientGroup.quotientBot)
  exact orthOrTripleA6_of_isTwoPrimeComponent hL.toIsTwoPrimeComponent
    (IsOrthogonalTwo.of_mulEquiv e3.symm (IsOrthogonalTwo.of_mulEquiv eY hO))

end CFSG.HardMathSupport.Cooperstein.StructureLie
