module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165ExcEngineSections
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExc
public import CFSG.GroupTheory.PLayer.PIndex
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
public import CFSG.HardMathSupport.Solomon.Coordinator.L5Conj
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8ExcAction
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.GL83PartI.I_22_6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreArith
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACorePerm
public import CFSG.Quasithin.Background.F918D5
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.Sporadic.Co2Schreier.ThirdChain
public import CFSG.Timmesfeld.Bridge.RootSetsBasic

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6

open CFSG.ClassicalGroups.UnitaryFlag

section Certificate


theorem exists_section_lift_SU3 {H G k : Type} [Group H] [Finite H] [Group G]
    [Field k] [Finite k] [CharP k 2] {n : ℕ} (hk : Nat.card k = (2 ^ n) ^ 2) (hn : 2 ≤ n)
    {π : H →* G} (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center H)
    {L : Subgroup G} (hLperf : ⁅L, L⁆ = L) {x : H}
    (hLx : L ≤ Subgroup.centralizer ({π x} : Set G))
    (e : ↥L ≃* ↥(unitarySU 2 n k 3)) :
    ∃ (S : Subgroup H) (eS : ↥S ≃* ↥L),
      S ≤ Subgroup.centralizer ({x} : Set H) ∧ S.map π = L ∧ S ⊓ π.ker = ⊥ ∧
      (∀ s : ↥S, π s = eS s) ∧ Group.IsPerfect ↥S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ^ n ≠ 2 := by
    have h4 : 4 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    omega
  have hq : (3, 2 ^ n) ≠ (3, 2) := fun hh => h2 (Prod.mk.inj hh).2
  have hQtriv : ∀ {m n : ℕ}, m ∣ n → True → True := fun _ _ => trivial
  refine CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcEngine.exists_section_lift_of_splits
    hπ hker hLperf hLx e (Q := fun _ => True) (hQ := hQtriv) (hQker := trivial) ?_
  intro E _ _ ρ hρ hcen _
  exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
    (p := 2) (f := n) (F := k) hk (by omega) (n := 3) le_rfl (by norm_num) hq hρ hcen

end Certificate

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcTwE6
