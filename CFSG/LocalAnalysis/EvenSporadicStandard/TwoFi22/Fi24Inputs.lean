module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.Main
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.Open.StatedDefs
public import CFSG.Fischer.NoF25.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJSylInputs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.EvenSporadicStandard

open Subgroup CFSG.Blueprint.NativeSporadic

namespace TwoFi22

variable {G : Type} [Group G]

@[expose] def O2In (H : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 ↥H).map H.subtype

@[expose] def O23In (H : Subgroup G) : Subgroup G :=
  ((CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map
    H.subtype

@[expose] def ParrottShape (H : Subgroup G) : Prop :=
  CFSG.IsExtraspecial 2 ↥(O2In H) ∧ Nat.card (O2In H) = 2 ^ 13 ∧
  H ⊓ centralizer (O2In H : Set G) ≤ O2In H ∧
  ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).Normal ∧ O23In H ≤ K ∧
    Nat.card (O23In H) = 3 * Nat.card (O2In H) ∧
    (∃ (X : Type) (_ : Group X) (π : ↥K →* X), Function.Surjective π ∧
      π.ker = (O23In H).subgroupOf K ∧ CFSG.Open.StatedClassicalModel X .PSU 4 3 1) ∧
    K.relIndex H = 2

end TwoFi22

end CFSG.EvenSporadicStandard
