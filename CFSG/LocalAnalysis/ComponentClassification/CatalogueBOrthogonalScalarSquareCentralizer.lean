module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionCommutant
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

open CatalogueBProjectiveInvolution

@[expose] def orthogonalOperatorCentralizer (Q : QuadraticForm K V)
    (T : Module.End K V) : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  (operatorCentralizer T).comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

@[expose] def orthogonalCentralizerToOperator (Q : QuadraticForm K V)
    (T : Module.End K V) : orthogonalOperatorCentralizer Q T →* operatorCentralizer T where
  toFun g := ⟨g.val.val, g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem orthogonalCentralizerToOperator_apply (Q : QuadraticForm K V)
    (T : Module.End K V) (g : orthogonalOperatorCentralizer Q T) (x : V) :
    (orthogonalCentralizerToOperator Q T g).val x = g.val.val x := rfl

@[expose] def orthogonalCentralizerRestriction (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) : orthogonalOperatorCentralizer Q T →*
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) where
  toFun g := ⟨operatorCentralizerRestriction T b (orthogonalCentralizerToOperator Q T g),
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (fun x => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.val.property x.val)⟩
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

theorem orthogonalCentralizerRestriction_apply (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) (g : orthogonalOperatorCentralizer Q T)
    (x : T.eigenspace b) :
    ((orthogonalCentralizerRestriction Q T b g).val x).val = g.val.val x.val := rfl

@[expose] def splitOrthogonalRestriction (Q : QuadraticForm K V)
    (T : Module.End K V) (b : K) : orthogonalOperatorCentralizer Q T →*
      (TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace b).subtype) ×
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (T.eigenspace (-b)).subtype)) :=
  (orthogonalCentralizerRestriction Q T b).prod (orthogonalCentralizerRestriction Q T (-b))

end CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
