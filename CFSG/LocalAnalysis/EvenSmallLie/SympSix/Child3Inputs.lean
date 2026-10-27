module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Assembly
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6SmallReeAmbient
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorLagrangian
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6TwoFactorAltNode

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

theorem inputAltEightTwoFactor
    (hD : CFSG.LocalAnalysis.SteinbergBV.DirectSimpleInvolutionCentralizerLayerStmt) :
    InputAltEightTwoFactor := by
  intro G _ _ L T z hS V _ _ _ b hb hnd hV φ e he halt
  exact
    (AlternatingEight.standard_binary_symplectic_six_alternating_eight_two_factor_ambient_exclusion
    hD hS.simple hS.nonab hS.kProper hS.oddCore_eq hS.standard hS.not_normal hS.center_eq hS.model
    T hS.cyclic hS.mem hS.order hS.core_z hb hnd hV φ e he
    halt).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem inputSmallRee (hF : Sp6LagrangianFullOddCoreStmt) : InputSmallRee := by
  intro G _ _ L T z hS V _ _ _ b hb hnd hV φ e he hfull hel hDs hDn ℓ f
  have hQ := lieModel_quot_of_center_eq_bot hS.center_eq hS.model
  exact ((standard_binary_symplectic_six_elementary_lagrangian_small_Ree_ambient_exclusion φ he z
    hF hS.simple hS.nonab hS.kProper hS.standard hS.core ⟨T, hS.cyclic⟩ (evenStandardType_of hQ)
    (not_evenStandardException_of hQ) (evenStandardResidual_of hS.center_eq hQ) hS.center_eq hQ
    T hS.cyclic hS.mem hS.order hb hnd hV hfull).2.2.2.2.2.2.2.2 hel hDs hDn ℓ f).2

theorem inputTwoFactor (hF : Sp6LagrangianFullOddCoreStmt) : InputTwoFactor := by
  intro G _ _ L T z hS V _ _ _ b hb hnd hV φ e he hfull hel
  have hQ := lieModel_quot_of_center_eq_bot hS.center_eq hS.model
  exact ((standard_binary_symplectic_six_elementary_lagrangian_two_factor_ambient_exclusion φ he z
    hF hS.simple hS.nonab hS.kProper hS.standard hS.core ⟨T, hS.cyclic⟩ (evenStandardType_of hQ)
    (not_evenStandardException_of hQ) (evenStandardResidual_of hS.center_eq hQ) hS.center_eq hQ
    T hS.cyclic hS.mem hS.order hb hnd hV hfull).2.2.2.2.2.2.2.2 hel).2.1

theorem childSp6Centerless_of_gaps_of_twoFactor (hSch : SchreierFor CFSG.Blueprint.Catalog)
    (hTF : InputTwoFactor) (hAE : InputAltEightTwoFactor) (hG1 : GapEpsilonOne)
    (hG2 : GapLagrangianSelector) (hG3 : GapAltEight) : ChildSp6Centerless :=
  childSp6Centerless_of_inputs hSch hTF (inputSmallRee (fullOddCore_of_schreier hSch)) hAE hG1 hG2
    hG3

theorem childSp6Centerless_of_altEight_of_gaps (hSch : SchreierFor CFSG.Blueprint.Catalog)
    (hAE : InputAltEightTwoFactor) (hG1 : GapEpsilonOne) (hG2 : GapLagrangianSelector)
    (hG3 : GapAltEight) : ChildSp6Centerless :=
  childSp6Centerless_of_gaps_of_twoFactor hSch (inputTwoFactor (fullOddCore_of_schreier hSch)) hAE
    hG1 hG2 hG3

theorem childSp6Centerless_of_schreier_of_gaps (hSch : SchreierFor CFSG.Blueprint.Catalog)
    (hG1 : GapEpsilonOne) (hG2 : GapLagrangianSelector) (hG3 : GapAltEight) :
    ChildSp6Centerless :=
  childSp6Centerless_of_altEight_of_gaps hSch (inputAltEightTwoFactor
    (CFSG.LocalAnalysis.SteinbergBV.direct_simple_involution_centralizer_layer_of_schreier hSch))
    hG1 hG2 hG3

end CFSG.EvenSmallLie.Child3
