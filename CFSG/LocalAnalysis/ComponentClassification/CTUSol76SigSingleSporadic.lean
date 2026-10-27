module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporA
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporB
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporC
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleSporD
public import CFSG.LocalAnalysis.ComponentClassification.BMCaseOddCoreB
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreLoc
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesB
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCasesD
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Sporadic.SmallOddCore.Co3Catalogue
public import CFSG.Sporadic.HNOddCore.HN
public import CFSG.Sporadic.ThSchreier.NodeGFExclusion
public import CFSG.Sporadic.ONOddCore.ONan
public import CFSG.Sporadic.Schreier.J4SCatalogU
public import CFSG.Sporadic.Schreier.LyOddCoreFree
public import CFSG.Sporadic.Co2Schreier.ModelSimple
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit

theorem twoComponentsQuasisimpleAt_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s) (T : Type) [Group T] [Finite T]
    (hT : IsSimpleGroup T) (hna : ∃ a b : T, a * b ≠ b * a)
    (hP : Blueprint.NativeSporadic.IsSporadic T s) : TwoComponentsQuasisimpleAt T := by
  have := hT
  obtain ⟨e⟩ := hP
  let f : ↥(CFSG.generalizedFitting T) ≃* T :=
    (MulEquiv.subgroupCongr sig_generalizedFitting_eq_top).trans Subgroup.topEquiv
  obtain ⟨a, b, hab⟩ := hna
  refine twoComponentsQuasisimpleAt_of_oddCore
    (hs T f.isSimpleGroup ⟨f.symm a, f.symm b, fun h => hab ?_⟩ ⟨f.trans e⟩)
  simpa using congrArg f h

theorem twoComponentsQuasisimpleAt_He
    (T : Type)
    [Group T] [Finite T] (_hT : IsSimpleGroup T) (_hna : ∃ a b : T, a * b ≠ b * a)
    (hP : Blueprint.NativeSporadic.IsSporadic T .He) : TwoComponentsQuasisimpleAt T := by
  obtain ⟨e⟩ := hP
  have e' : T ≃* Blueprint.NativeSporadic.He := e
  let f : T ≃* Sporadic.HeldB.heP := e'.trans Sporadic.HeldB.heEquivP
  refine twoComponentsQuasisimpleAt_of_oddCore fun t ht => ?_
  have h := Sporadic.HeldB.ctbhi_held_inner_involution_centralizers_odd_core.2 (f t)
    (by rw [MulEquiv.orderOf_eq]; exact ht)
  have h' : CFSG.oddCore ↥(centralizer ({f t} : Set Sporadic.HeldB.heP)) = ⊥ := by
    rw [← h]
    simp only [pPrimeCore, CFSG.oddCore, Nat.coprime_two_left]
  exact LieType.Ree.ReeTag.oddCore_eq_bot_of_mulEquiv (RestrictedStd.Spor.centralizerEquiv f t) h'

theorem singleComponentQuasisimpleAt_exists {ι : Type} {P : ι → (S : Type) → [Group S] → Prop}
    (h : ∀ i, SingleComponentQuasisimpleAt (P i)) :
    SingleComponentQuasisimpleAt (fun S _ => ∃ i, P i S) := by
  intro R _ _ hR hO hP
  obtain ⟨i, hi⟩ := hP
  exact h i R hR hO hi

theorem singleComponentQuasisimpleAt_of_sporadicOddCoreFree {s : TauCeti.SporadicName}
    (hs : CatalogueU.SporadicOddCoreFree s)
    (h : SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T s)) :
    SingleComponentQuasisimpleAt (fun S _ => Blueprint.NativeSporadic.IsSporadic S s) :=
  singleComponentQuasisimpleAt_of_clean (twoComponentsQuasisimpleAt_of_sporadicOddCoreFree hs) h

section Certified


theorem singleComponentQuasisimpleAt_isSporadic_of_Ru
    (hRu : SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Ru))
    (s : TauCeti.SporadicName) :
    SingleComponentQuasisimpleAt (fun S _ => Blueprint.NativeSporadic.IsSporadic S s) := by
  cases s
  case M11 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M11
      singleComponentCleanAt_M11
  case M12 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M12
      singleComponentCleanAt_M12
  case M22 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M22
      singleComponentCleanAt_M22
  case M23 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M23
      singleComponentCleanAt_M23
  case M24 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M24
      singleComponentCleanAt_M24
  case J1 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree Foote5.sporadicOddCoreFree_J1
      singleComponentCleanAt_J1
  case J2 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_J2
      singleComponentCleanAt_J2
  case J3 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_J3
      singleComponentCleanAt_J3
  case J4 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      CatalogueU.sporadicOddCoreFree_J4 singleComponentCleanAt_J4
  case HS =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_HS
      singleComponentCleanAt_HS
  case McL =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_McL
      singleComponentCleanAt_McL
  case He =>
    exact singleComponentQuasisimpleAt_of_clean twoComponentsQuasisimpleAt_He
      singleComponentCleanAt_He
  case Ru =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Ru
      hRu
  case Suz =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Suz
      singleComponentCleanAt_Suz
  case ONan =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      Sporadic.ONOddCore.sporadicOddCoreFree_ONan singleComponentCleanAt_ON
  case Co1 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Co1
      singleComponentCleanAt_Co1
  case Co2 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      Sporadic.Co2Schreier.sporadicOddCoreFree_Co2 singleComponentCleanAt_Co2
  case Co3 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      Sporadic.SmallOddCore.sporadicOddCoreFree_Co3 singleComponentCleanAt_Co3
  case Fi22 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Fi22
      singleComponentCleanAt_Fi22
  case Fi23 =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_Fi23
      singleComponentCleanAt_Fi23
  case Fi24Prime =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      CatalogueU.sporadicOddCoreFree_Fi24Prime singleComponentCleanAt_Fi24
  case HN =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      Sporadic.HNOddCore.sporadicOddCoreFree_HN singleComponentCleanAt_HN
  case Ly =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      Sporadic.LySchreier.sporadicOddCoreFree_Ly singleComponentCleanAt_Ly
  case Th =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree
      Sporadic.ThSchreier.sporadicOddCoreFree_Th singleComponentCleanAt_Th
  case B =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree BMCase.sporadicOddCoreFree_B
      singleComponentCleanAt_B
  case M =>
    exact singleComponentQuasisimpleAt_of_sporadicOddCoreFree CatalogueU.sporadicOddCoreFree_M
      singleComponentCleanAt_M

theorem singleComponentQuasisimpleAt_sporadic_of_Ru
    (hRu : SingleComponentCleanAt (fun T _ => Blueprint.NativeSporadic.IsSporadic T .Ru)) :
    SingleComponentQuasisimpleAt (fun S _ => Blueprint.NativeSporadic.SporadicRep S) :=
  singleComponentQuasisimpleAt_exists (singleComponentQuasisimpleAt_isSporadic_of_Ru hRu)

end Certified

end CFSG.ComponentClassification.Sol76.Sig
