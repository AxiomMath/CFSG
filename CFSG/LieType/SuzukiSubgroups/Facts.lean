module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.StronglyEmbedded.BenderBorelTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.CGT.T75E.RootOrders
public import CFSG.RankThree.S4Free.SuzukiEight
public import Certificates.Certificate43
public import Certificates.Certificate113
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.CGT.T75E.Reduce
public import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
public import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
public import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
public import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
public import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
public import CFSG.CGT.Timmesfeld75.Sec4Three
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Step511Card
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.S4Free.Statement
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LieType.SuzukiSubgroups

open CFSG.Open Subgroup

variable {n : ℕ} {H : Type} [Group H]

theorem exists_mulEquiv_sz (hH : CFSG.Quasithin.IsSz n H) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (H ≃* ↥(Sz a)) := by
  obtain ⟨-, a, ha, K, _, _, rfl, hcard, ⟨e⟩⟩ := hH
  refine ⟨a, ha, rfl, ⟨e.trans ?_⟩⟩
  exact (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard)

theorem isSz_of_mulEquiv {a : ℕ} (ha : 1 ≤ a) {X : Type} [Group X] (e : X ≃* ↥(Sz a)) :
    CFSG.Quasithin.IsSz (2 * a + 1) X := by
  refine ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl, ?_, ?_⟩
  · exact GaloisField.card 2 (2 * a + 1) (by omega)
  · exact ⟨e.trans
      (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a).some⟩

theorem fusionBenderBorel_of_isSz [Finite H]
    (hH : CFSG.Quasithin.IsSz n H) : fusionBenderBorel H (2 ^ n) 2 := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz hH
  exact (CFSG.Open.bender_suzuki_borel_full a ha).map_mulEquiv e.symm

theorem isPGroup_centralizer_of_isSz (hH : CFSG.Quasithin.IsSz n H) {x : H}
    (hx : orderOf x = 2) : IsPGroup 2 (centralizer ({x} : Set H)) := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz hH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx' : orderOf (e x) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hx
  rw [IsPGroup.iff_orderOf]
  intro y
  have hy : e y.1 ∈ centralizer ({e x} : Set ↥(Sz a)) := by
    have hy2 := y.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hy2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg e hy2
  obtain ⟨k, hk⟩ := (CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_involution_centralizer
    ha (e x) hx').exists_orderOf_eq_pow ⟨e y.1, hy⟩
  refine ⟨k, ?_⟩
  rw [← Subgroup.orderOf_coe y, ← MulEquiv.orderOf_eq e y.1]
  exact (Subgroup.orderOf_mk (e y.1) hy).symm.trans hk

theorem not_three_dvd_card_of_isSz
    (hH : CFSG.Quasithin.IsSz n H) : ¬ 3 ∣ Nat.card H := by
  obtain ⟨a, _, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz hH
  exact CFSG.CGT.T75E.not_three_dvd_card_of_mulEquiv_sz e

theorem card_normalizer_sylow_of_isSz [Finite H]
    (hH : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) :
    Nat.card (normalizer ((Q : Subgroup H) : Set H)) = (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz hH
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  exact CFSG.RankThree.S4Free.Suzuki.card_normalizer_sylow hK
    (e.trans (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup
      a).some) Q

theorem normalizer_le_normalizer_sylow_of_isSz [Finite H]
    (hH : CFSG.Quasithin.IsSz n H) (Q : Sylow 2 H) {P : Subgroup H} (hPQ : P ≤ Q)
    (hP : P ≠ ⊥) : normalizer (P : Set H) ≤ normalizer ((Q : Subgroup H) : Set H) := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ := exists_mulEquiv_sz hH
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  exact CFSG.RankThree.S4Free.Suzuki.normalizer_le_normalizer_sylow hK
    (e.trans (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup
      a).some) Q hPQ hP

end CFSG.LieType.SuzukiSubgroups
