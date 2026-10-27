module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoULift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUModelU4
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUModelU5
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankTwoUScalarTorus
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5
import CFSG.Quasithin.H13.U4ParModel
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU4
public import CFSG.Assembly.QuasithinDefs
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

private theorem hasScalarTorus_of_model_equiv {G₀ L : Type} [Group G₀] [Group L] [Finite L]
    {q : ℕ} (hq : q.Prime) (hqZ : ¬ q ∣ Nat.card (Subgroup.center L))
    {U₀ : Subgroup G₀} (hU₀ : CFSG.QuasithinUnique.IsSylowTwoOf U₀ ⊤)
    (h : HasScalarTorus G₀ q U₀) (φ : G₀ ≃* L ⧸ Subgroup.center L) {U : Subgroup L}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasScalarTorus L q U := by
  have hUidx : ¬ 2 ∣ U.index := by
    simpa only [show (U.subgroupOf ⊤).index = U.index from
      Subgroup.relIndex_top_right U] using hU.2.2
  have hU' : CFSG.QuasithinUnique.IsSylowTwoOf
      (U.map (QuotientGroup.mk' (Subgroup.center L))) ⊤ := by
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    rw [show ((U.map (QuotientGroup.mk' (Subgroup.center L))).subgroupOf ⊤).index =
      (U.map (QuotientGroup.mk' (Subgroup.center L))).index from
      Subgroup.relIndex_top_right _]
    exact fun h2 => hUidx (h2.trans (Subgroup.index_map_dvd U
      (QuotientGroup.mk'_surjective (Subgroup.center L))))
  exact HasScalarTorus.of_quotient_center hq hqZ hU
    (HasScalarTorus.of_mulEquiv φ hU₀ h hU')

theorem hasScalarTorus_of_twistedA_three {L : Type} [Group L] [Finite L]
    {Q : TauCeti.PrimePower} (hQ : Q.p = 2) {hv : (TauCeti.LieTypeIndex.twistedA 3 Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA 3 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Q.card - 1)
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U : Subgroup L}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasScalarTorus L q U := by
  have hdvd' : q ∣ 2 ^ Q.exponent - 1 := by
    simpa only [TauCeti.PrimePower.card_def, hQ] using hdvd
  have hY : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 4 2 Q.exponent :=
    Or.inl ⟨by decide, hQ ▸
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 Q hv e⟩
  obtain ⟨K, _, h, ⟨φ⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hY
  exact hasScalarTorus_of_model_equiv hq hqZ
    (CFSG.Quasithin.H13.Sec53F.Unit.borelAutData_u4 h).sylow
    (hasScalarTorus_hypSU_two_zero h hq hdvd') φ hU

theorem hasScalarTorus_of_twistedA_four {L : Type} [Group L] [Finite L]
    {Q : TauCeti.PrimePower} (hQ : Q.p = 2) {hv : (TauCeti.LieTypeIndex.twistedA 4 Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedA 4 Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ Q.card - 1)
    (hqZ : ¬ q ∣ Nat.card (Subgroup.center L)) {U : Subgroup L}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) : HasScalarTorus L q U := by
  have hdvd' : q ∣ 2 ^ Q.exponent - 1 := by
    simpa only [TauCeti.PrimePower.card_def, hQ] using hdvd
  have hY : CFSG.Blueprint.LieModel (L ⧸ Subgroup.center L) .PSU 5 2 Q.exponent :=
    Or.inl ⟨by decide, hQ ▸
      CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 4 Q hv e⟩
  obtain ⟨K, _, h, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s218_u5_exists_model hY
  exact hasScalarTorus_of_model_equiv hq hqZ
    (CFSG.Quasithin.H13.Sec53F.Unit.borelAutDiag_u5 h).sylow
    (hasScalarTorus_hypPSU_two_one h hq hq2 hdvd') φ hU

end CFSG.LocalAnalysis.RankThreeUC.S15

end
