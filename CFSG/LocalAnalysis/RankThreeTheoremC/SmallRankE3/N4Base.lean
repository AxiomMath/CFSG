module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem n4_isTwoLocal_ne_top (hS : Setting G) {H : Subgroup G} (hH : IsTwoLocal H) : H ≠ ⊤ := by
  haveI := hS.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ1, hQ2, rfl⟩ := hH
  intro htop
  have hnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exact hQ1 h
  · subst h
    have hG2 : IsPGroup 2 G := hQ2.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent G := hG2.isNilpotent
    have hsolv : Group.IsSolvable G := inferInstance
    obtain ⟨a, b, hab⟩ := hS.nonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsolv a b)

theorem n4_centralizer_le_of_central (hS : Setting G) {p : ℕ} {P : Sylow p G} {M : Subgroup G}
    (hsit : SmallRankSituation G p P M) {z : G} (hz : SmallRankCentral P z) :
    centralizer ({z} : Set G) ≤ M := by
  have hprime : p.Prime := sigmaA_prime p hsit.mem_sigmaA
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hsit.mem_sigmaA hsit.isCoreMaxLocal
  have hPC : (P : Subgroup G) ≤ centralizer ({z} : Set G) := fun g hg =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz.centralizes g hg)
  by_contra hCM
  refine hsit.largeObstruction_empty z ⟨hPM hz.mem, hz.ne_one, hz.pow_eq_one, ?_, hCM⟩
  have := CFSG.SectionRank.pRank_mono hprime.one_lt hPC
  omega

theorem n4_normalizer_zpowers_le_of_central (hS : Setting G) {p : ℕ} {P : Sylow p G}
    {M : Subgroup G} (hsit : SmallRankSituation G p P M) {z : G} (hz : SmallRankCentral P z) :
    normalizer ((zpowers z : Subgroup G) : Set G) ≤ M :=
  normalizer_zpowers_le_of_largeObstruction_empty hS hsit.mem_sigmaA hsit.isCoreMaxLocal
    hsit.largeObstruction_empty hz.mem hz.centralizes hz.ne_one hz.pow_eq_one

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
