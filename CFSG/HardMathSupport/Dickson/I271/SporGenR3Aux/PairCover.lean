module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Cover
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Pair
public import CFSG.HardMathSupport.Dickson.I271.SporGen
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.NoComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.StepGen

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Tables.Census
  CFSG.Yardstones.Md0ec50421ce4

section CoverStep

variable {X : Type} [Group X] [Finite X]

theorem strong_of_centShape_cover {p : ℕ} {K B : Subgroup X} {name : TauCeti.SporadicName}
    {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hOut : SporadicOuterLeTwo) (hH : CompHyp p K B) (hN : I271Norm p K B)
    (hS : I271SporType K name)
    (hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K))
    (hOall : OPrimeCoreTrivialAt p (↥K ⧸ Subgroup.center ↥K))
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → IsStronglyBalancedIn p B' J)
    (hshape : CentShape p Good (↥K ⧸ Subgroup.center ↥K)) : IsStronglyBalancedIn p B K := by
  have hZp : IsPGroup p (Subgroup.center ↥K) := i271h_center_isPGroup hH.prime hH.primeCore
  refine strong_of_dichotomy hGood hOut hH hN hS hloc hIH ?_
  intro a k hk haB hc haC
  obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hH.elem.2 a haB) haC hk hc
  exact comp_dichotomy_cover hH.prime hGood hZp hOall hshape hk hc hkZ hkp

end CoverStep

theorem sporPair_of_centShape_cover {name : TauCeti.SporadicName} {p : ℕ}
    {Good : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → IsStronglyBalancedIn p B' J)
    (hD : CentShape p Good (NativeSporadic.Carrier name)) : SporPair name p := by
  intro X _ _ hX K B hH hN hS hF hO
  right
  have hC : CompHyp p K B := CompHyp.of_i271Hyp hH hN.1
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hH.prime hH.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eS : (↥K ⧸ Subgroup.center ↥K) ≃* NativeSporadic.Carrier name := e.trans (hBr name).some.symm
  haveI : Finite (NativeSporadic.Carrier name) := Finite.of_equiv _ eS.toEquiv
  have hOall : OPrimeCoreTrivialAt p (↥K ⧸ Subgroup.center ↥K) := hP.1 _ ⟨eS⟩
  have hshape : CentShape p Good (↥K ⧸ Subgroup.center ↥K) :=
    CentShape.of_equiv hH.prime hGood eS.symm hD
  exact strong_of_centShape_cover hGood hOut hC hN ⟨e⟩ hloc hOall hIH hshape

theorem sporPair_of_leafShape_cover {name : TauCeti.SporadicName}
    {p : ℕ} (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hChev : ChevStrong p) (hD : LeafShape name p) :
    SporPair name p :=
  sporPair_of_centShape_cover (fun _ _ _ _ e h => LeafType.of_equiv e h) hOut hBr hP
    (fun _ _ _ _ _ h hG => strong_leaf hChev h hG) hD

@[expose] def ConstrainedShape (name : TauCeti.SporadicName) (p : ℕ) : Prop :=
  ∀ k : NativeSporadic.Carrier name, k ≠ 1 → k ^ p = 1 →
    PConstrainedShape p (Subgroup.centralizer ({k} : Set (NativeSporadic.Carrier name)))

end CFSG.HardMathSupport.Dickson.I271
