module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerived
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCore
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.SUSixCenter
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer innAutDerived)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

section SLevel

variable (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group]

theorem layer_ne_bot_of_component {p : ℕ} (hp : p.Prime) {β : MulAut (TauCeti.CFSGIndex.lie d).Group}
    {J : Subgroup (TauCeti.CFSGIndex.lie d).Group} (hJ : GLAPComponent p (fixSubgroup β) J)
    (hJp : p ∣ Nat.card J) : GLAPLayer p (fixSubgroup β) ≠ ⊥ := by
  intro hbot
  have hle : J ≤ GLAPLayer p (fixSubgroup β) := le_sSup hJ
  rw [hbot] at hle
  have hJ1 : Nat.card J = 1 := by
    rw [Subgroup.card_eq_one]
    exact le_bot_iff.1 hle
  rw [hJ1] at hJp
  exact hp.one_lt.ne' (Nat.dvd_one.1 hJp)

end SLevel

end CFSG.LocalAnalysis.GLTheoremA.HDesc
