module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallModelConj
public import CFSG.GH74.KGroups.NativeChecks2
public import CFSG.GH74.Exceptional.UnitaryFourTwo
public import CFSG.GH74.Generic.Context
public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.Fischer.Classification.PartIII.Beta.Data
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import Mathlib

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.GH74.Exceptional CFSG.Fischer.Classification.Beta CFSG.Assembly.LowTwoRank

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] noncomputable def psi : PSp43 →* Equiv.Perm (Fin 45) :=
  rho43.comp psp43EquivU2.toMonoidHom

theorem psi_apply (g : PSp43) (j : Fin 45) : psi g j = s43Idx (g * s43 j * g⁻¹) := by
  have : psi g =
      sigma43 (((MulEquiv.subgroupCongr Y43_eq_top).trans Subgroup.topEquiv).symm g) := by
    show rho43 (psp43EquivU2 g) = _
    rw [psp43EquivU2, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm]
    rfl
  rw [this, sigma43_apply]
  rfl

theorem psi_s43 (i j : Fin 45) : psi (s43 i) j = tauFun i j := by
  rw [psi_apply, s43_inv, s43_tau, s43Idx_s43]
  rfl

end CFSG.ComponentClassification.CatFactsSmall.PSp43
