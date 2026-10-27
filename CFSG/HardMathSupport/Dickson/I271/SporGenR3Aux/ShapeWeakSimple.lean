module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ShapeWeak
public import CFSG.RankThree.PartOne.SPOR.OuterM

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.Monster.Generated (Gmat)

@[expose] def SimpleCentShapeRk' (p : ℕ) (Good Rk : ∀ (T : Type) [Group T], Prop)
    (name : TauCeti.SporadicName) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (T ≃* NativeSporadic.Carrier name) →
    CentShapeRk' p Good Rk T

section Templates

theorem strong_of_simpleCentShapeRk' {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges) (hP : SporadicOnePairHolds name p)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : SimpleCentShapeRk' p Good Rk name) {X : Type} [Group X] [Finite X]
    {K B : Subgroup X} (hC : CompHyp p K B) (hN : I271Norm p K B) (hS : I271SporType K name)
    (hZ : Subgroup.center ↥K = ⊥) : IsStronglyBalancedIn p B K := by
  have hq : CFSG.Open.IsQuasisimple ↥K := hC.quasi
  obtain ⟨e⟩ := hS
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hq.2
  have hloc : IsLocallyOneBalancedAbs p (↥K ⧸ Subgroup.center ↥K) :=
    isLocallyOneBalancedAbs_of_pair hOut hBr hC.prime hC.odd hP _ hq.2
      (exists_noncomm_of_isQuasisimple hq) ⟨e⟩
  let eZ : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eK : ↥K ≃* NativeSporadic.Carrier name := eZ.symm.trans (e.trans (hBr name).some.symm)
  haveI : IsSimpleGroup ↥K := MulEquiv.isSimpleGroup eZ.symm
  have hshape : CentShapeRk' p Good Rk ↥K := hD ↥K eK
  refine strong_of_dichotomy_rk hGood hRk hOut hC hN ⟨e⟩ hloc hIH ?_
  intro a k hk haB hc haC
  obtain ⟨hkZ, hkp⟩ := lift_data_of_inner (hC.elem.2 a haB) haC hk hc
  have hk1 : (⟨k, hk⟩ : ↥K) ≠ 1 := fun h => hkZ (h ▸ Subgroup.one_mem _)
  have hkp1 : (⟨k, hk⟩ : ↥K) ^ p = 1 := by
    rw [hZ] at hkp
    exact Subgroup.mem_bot.1 hkp
  exact comp_dichotomy_rk' hC.prime hk hc (hshape _ hk1 hkp1)

theorem sporStrong_of_simpleCentShapeRk' {name : TauCeti.SporadicName} {p : ℕ}
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hIH : ∀ (Y : Type) [Group Y] [Finite Y] (J B' : Subgroup Y), CompHyp p J B' →
      Good (↥J ⧸ Subgroup.center ↥J) → Rk ↥J → IsStronglyBalancedIn p B' J)
    (hD : SimpleCentShapeRk' p Good Rk name) : SporStrong name p := by
  intro X _ _ K B hC hN hS
  exact strong_of_simpleCentShapeRk' hGood hRk hOut hBr hP hIH hD hC hN hS
    (center_eq_bot_of_mult hSpM hC hS hm)

theorem sporStrong_of_goodSporSimpleShape'
    {name : TauCeti.SporadicName} {p : ℕ} {names : List TauCeti.SporadicName}
    (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers) (hBr : SporadicBridges)
    (hP : SporadicOnePairHolds name p) (hm : ¬ p ∣ sporadicMultiplierOrder name)
    (hChev : ChevStrong p) (hSp : ∀ S ∈ names, SporStrong S p)
    (hD : SimpleCentShapeRk' p (GoodSpor p names) (RkSpor p names) name) :
    SporStrong name p :=
  sporStrong_of_simpleCentShapeRk' (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
    (fun _ _ _ _ e h => RkSpor.of_equiv e h) hOut hSpM hBr hP hm
    (fun _ _ _ _ _ h hG hR => strong_goodSpor hChev hSp h hG hR) hD

end Templates

section Monster

theorem simpleCentShapeRk'_M_of_gmat {p : ℕ} (hp : p.Prime)
    {Good Rk : ∀ (T : Type) [Group T], Prop}
    (hGood : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Good T → Good T')
    (hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → Rk T → Rk T')
    (h : CentShapeRk' p Good Rk Gmat) : SimpleCentShapeRk' p Good Rk .M := by
  intro T _ _ _ e
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  haveI : Finite Gmat := Finite.of_equiv T ε.toEquiv
  exact CentShapeRk'.of_equiv hp hGood hRk ε.symm h

theorem sporStrong_M_of_gmatShape {p : ℕ}
    {names : List TauCeti.SporadicName} (hp : p.Prime) (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers) (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M p)
    (hChev : ChevStrong p) (hSp : ∀ S ∈ names, SporStrong S p)
    (hD : CentShapeRk' p (GoodSpor p names) (RkSpor p names) Gmat) : SporStrong .M p :=
  sporStrong_of_goodSporSimpleShape' hOut hSpM hBr hP (show ¬ p ∣ 1 from hp.not_dvd_one) hChev hSp
    (simpleCentShapeRk'_M_of_gmat hp (fun _ _ _ _ e h => GoodSpor.of_equiv e h)
      (fun _ _ _ _ e h => RkSpor.of_equiv e h) hD)

theorem sporPair_M_of_gmatShape {p : ℕ}
    {names : List TauCeti.SporadicName} (hp : p.Prime) (hOut : SporadicOuterLeTwo)
    (hSpM : SporadicMultipliers) (hBr : SporadicBridges) (hP : SporadicOnePairHolds .M p)
    (hChev : ChevStrong p) (hSp : ∀ S ∈ names, SporStrong S p)
    (hD : CentShapeRk' p (GoodSpor p names) (RkSpor p names) Gmat) : SporPair .M p :=
  sporPair_of_sporStrong (sporStrong_M_of_gmatShape hp hOut hSpM hBr hP hChev hSp hD)

end Monster

end CFSG.HardMathSupport.Dickson.I271
