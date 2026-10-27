module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Frame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.Leaves
public import CFSG.Models
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4CoverCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherCore
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Setup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma49Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CL4
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1FourGroup
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1RowAlt
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Count
public import CFSG.LocalAnalysis.ComponentClassification.HeldBalStatements
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCoreBasics
public import CFSG.LocalAnalysis.ComponentClassification.TBLitStepFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTenSkel
public import CFSG.LocalAnalysis.OddStandard.OddLieHarris82Simple
public import CFSG.Open.GeneralizedFittingSelfCentralizing
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.Sporadic.HeldB.AllFixed
public import Certificates.Certificate7233Base

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank
open scoped commutatorElement

@[expose] def rels26 (n : ℕ) (e : Bool) : Set (FreeGroup (Fin 5)) :=
  let u : FreeGroup (Fin 5) := FreeGroup.of 0
  let v : FreeGroup (Fin 5) := FreeGroup.of 1
  let w : FreeGroup (Fin 5) := FreeGroup.of 2
  let r : FreeGroup (Fin 5) := FreeGroup.of 3
  let s : FreeGroup (Fin 5) := FreeGroup.of 4
  {x | x ∈ [⁅u, v⁆, ⁅u, w⁆, ⁅v, w⁆, u ^ 2 ^ n, v ^ 2 ^ n, w ^ 2 ^ n, r ^ 2,
    r⁻¹ * s * r * s, r⁻¹ * u * r * w, r⁻¹ * v * r * v, r⁻¹ * w * r * u,
    s⁻¹ * u * s * v⁻¹, s⁻¹ * v * s * w⁻¹, s⁻¹ * w * s * (u * v⁻¹ * w)⁻¹,
    s ^ 4 * (if e then (u * w)⁻¹ else 1)]}

@[expose] def IsPres26 (n : ℕ) (e : Bool) (P : Type) [Group P] (u v w r s : P) : Prop :=
  ∃ h : ∀ x ∈ rels26 n e, FreeGroup.lift (![u, v, w, r, s] : Fin 5 → P) x = 1,
    Function.Bijective (PresentedGroup.toGroup h)

@[expose] def IsExt26 (n : ℕ) (X : Type) [Group X] [Finite X] : Prop :=
  Nonempty (↥(pCoreOf 2 (⊤ : Subgroup X)) ≃* (Fin 3 → Multiplicative (ZMod (2 ^ n)))) ∧
  SecProp (⊤ : Subgroup X) (pCoreOf 2 (⊤ : Subgroup X))
    (fun Y _ _ _ => Nonempty (Y ≃* GL (Fin 3) (ZMod 2))) ∧
  centralizer ((pCoreOf 2 (⊤ : Subgroup X) : Subgroup X) : Set X) = pCoreOf 2 (⊤ : Subgroup X)

@[expose] def IsG23Type (Y : Type) [Group Y] : Prop :=
  ∀ (Q : Type) [Group Q], HRG23 Q → ∀ S : Sylow 2 Q, Nonempty (Y ≃* S)

@[expose] def IsHSType (Y : Type) [Group Y] : Prop :=
  ∀ S : Sylow 2 (TauCeti.SporadicName.Group TauCeti.SporadicName.HS), Nonempty (Y ≃* S)

end CFSG.OddStandard.HigherRank.G2Three.Sec2
