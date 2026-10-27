module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Induct
public import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorConfiguration
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B2G4

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial

theorem b_B2_g4_of_inclusion
    (hProp : ∀ (X : Type) [Group X] [Finite X], Gen4 X → IsKGroupNative X →
      CentralTwoBInclusion.Property X) : B_B2_g4 := by
  intro X _ _ hg hX hcore y hy K hK
  have hcore' : CFSG.Assembly.oddCore X = ⊥ := by
    rw [assembly_oddCore_eq_pPrimeCore]
    exact hcore
  have hlocal := AssemblyBLocalB.of_corefree_and_inclusion hcore' (hProp X hg hX)
  have hJ : CFSG.Assembly.ComponentType.IsTwoPComponent
      (K.subgroupOf (centralizer ({y} : Set X))) :=
    (isTwoPComponent_iff_isPComponent _).2 hK.2
  have h := AssemblyBLocalB.ordinary_at_involution hlocal y hy _ hJ
  exact ⟨hK.1, (AssemblyBPredicates.isComponentOf_top_iff_native _).1 h⟩

theorem b_B2_g4_of_inputs
    (hS : SchreierG4) (hU : UnbalancedG4) (hE : ExceptionalG4) : B_B2_g4 :=
  b_B2_g4_of_inclusion fun X _ _ hg hX => kGroup_B_inclusion_g4 hS hU hE X hg hX

end CFSG.GH74.GLS.C3.Layer1.Bk.B2G4
