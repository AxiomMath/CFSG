module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3GapG1Defs
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneMain
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBISp6ActionParameters
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneLambdaZeroMain
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneNormalizerPoint

public section

namespace CFSG.EvenSmallLie.Child3

open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64

theorem inputLamZero : InputLamZero :=
  fun hG _ hL hLn hZ hmodel T hT _ hzT hz hH _ _ _ _ _ hb hnd hV φ e he hfull =>
    false_of_lambda_zero hG hL hLn hZ hmodel T hT hzT hz hH hb hnd hV φ e he hfull

theorem gapEpsilonOne_of_inputs
    (hLZ : InputLamZero) (hQ : EpsOneLagrangianNormalizerStmt) :
    GapEpsilonOne := by
  intro G _ _ L T z hS V _ _ _ b hb hnd hV φ e he hfull
  by_contra hnel
  obtain ⟨κ₂, lam, h₂, h₁⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SteinbergBI.exists_action_parameters hS.oddCore_eq
      hS.standard hS.not_normal hS.center_eq hS.model T hS.cyclic hS.mem hS.order hS.core_z hb hnd
      hV φ e he hfull
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) lam with hl | hl
  · exact hLZ hS.oddCore_eq hS.standard hS.not_normal hS.center_eq hS.model T hS.cyclic hS.mem
      hS.order hS.core_z hb hnd hV φ e he hfull κ₂ lam h₂ h₁ hl hnel
  · exact false_of_lambda_one hQ hS.oddCore_eq hS.simple hS.nonab hS.standard hS.not_normal
      hS.center_eq hS.model T hS.cyclic hS.mem hS.order hS.core_z hb hnd hV φ e he hfull κ₂ lam
      h₂ h₁ hl hnel

theorem gapEpsilonOne_of_lagNormalizer
    (hQ : EpsOneLagrangianNormalizerStmt) : GapEpsilonOne :=
  gapEpsilonOne_of_inputs inputLamZero hQ

theorem gapEpsilonOne :
    GapEpsilonOne :=
  gapEpsilonOne_of_lagNormalizer
    standard_binary_symplectic_six_epsilon_one_lagrangian_radical_normalizer

end CFSG.EvenSmallLie.Child3
