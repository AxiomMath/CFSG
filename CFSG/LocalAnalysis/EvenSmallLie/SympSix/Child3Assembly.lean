module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3Lagrangian
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3OrbitCases

public section

namespace CFSG.EvenSmallLie.Child3

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.Degree64
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.FusionOrbits
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)


theorem childSp6Centerless_of_inputs (hSch : SchreierFor CFSG.Blueprint.Catalog)
    (hTF : InputTwoFactor) (hSR : InputSmallRee) (hAE : InputAltEightTwoFactor)
    (hG1 : GapEpsilonOne) (hG2 : GapLagrangianSelector) (hG3 : GapAltEight) :
    ChildSp6Centerless := by
  intro G _ _ L hset hZ hQ
  obtain ⟨T, z, hS⟩ := setting_of_standardSetting hset hZ hQ
  obtain ⟨V, _, _, _, b, hb, hnd, hV, φ, e, he⟩ := exists_symplectic_model hS.model
  rcases orbit_cases hS hb hnd hV φ he with hfull | halt
  · exact false_of_lagrangian (fullOddCore_of_schreier hSch) hG1 hG2 hTF hSR hS hb hnd hV φ he
      hfull
  · exact hG3 G L T z hS V b hb hnd hV φ e he halt (hAE G L T z hS V b hb hnd hV φ e he halt)

end CFSG.EvenSmallLie.Child3
