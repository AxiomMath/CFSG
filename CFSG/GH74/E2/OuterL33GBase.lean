
module

public import CFSG.GH74.E2.OuterL33
public import CFSG.GH74.E2.OuterCore
public import CFSG.GH74.E2.L33AutTable
public import CFSG.GH74.E2.LocalLeaves
public import CFSG.GH74.E2.Alpha1Core
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Alpha1CoreInputs
public import CFSG.GH74.E2.SD16CertInputs
public import Mathlib
public import CFSG.GH74.KGroups.Generic
public import CFSG.GH74.KGroups.PermCheck
public import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.KGroups.PSLN
public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.McL
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyChain11
public import Certificates.Certificate3085Base

@[expose] public section

namespace CFSG.GH74.E2

open Subgroup CFSG.GH74.GLS

theorem l33_card_aut {K : Type} [Group K] (hK : ShapeL33 K) :
    Nat.card (MulAut K) = 2 * Nat.card K := by
  obtain ⟨e⟩ := KGroups.L33.equiv_of_lieModel hK
  rw [KGroups.L33.card_mulAut e, Nat.card_congr e.toEquiv,
    KGroups.card_group KGroups.L33.QP KGroups.L33.QP_ok, KGroups.L33.QP_valid.2]

local instance instDecEqSD16 : DecidableEq SD16M := inferInstance

end CFSG.GH74.E2
