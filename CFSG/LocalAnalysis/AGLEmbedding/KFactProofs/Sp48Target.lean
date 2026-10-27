module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarTargetTwoData
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveSp4Out
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48
import CFSG.Timmesfeld.Orders.Classical
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeChevTwo
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.Quasithin.Background.A1cTransfer
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.AGLEmbedding

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_elemAbelian_nine_projSp {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ E : Subgroup (StatedProj (StatedSp 2 K)), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨hab, hcard⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.isElemAbelian_sp4E9 (F := K)
  refine ⟨(CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.sp4E9 K).map
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 K),
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hab, ?_⟩
  rw [Subgroup.card_map_of_injective CFSG.RankThree.PartTwo.KFacts.proj_injective_of_charTwo,
    hcard]

theorem stmtSp48Target : StmtSp48Target := by
  intro d hd L _ _ ⟨e⟩
  obtain ⟨q, hq2, hq3, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  simp only at hdq
  subst hdq
  have hm : StatedClassicalModel L .PSp 2 q.p q.exponent :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
  rw [hq2, hq3] at hm
  have hsimple : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 2 2 3 hm
  have hcard : Nat.card L = 3 ^ 4 * 13045760 := by
    have := (CFSG.Timmesfeld.card_statedClassicalModel_two hm).2.2.1 rfl
    rw [this]
    decide
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hm
  have hKc : Nat.card K = 2 ^ 3 := hK
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hKc
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨hOutc, hOutcard⟩ := CFSG.QuasithinUnique.Lin2.sp4OutCyclic K 3
    (by rw [← Nat.card_eq_fintype_card, hKc]) (by norm_num)
  let eO := CFSG.ComponentClassification.OuterAutomorphisms.equivalence eK
  have hOutL : IsCyclic (Outer L) :=
    haveI := hOutc
    isCyclic_of_surjective eO.symm.toMonoidHom eO.symm.surjective
  have hOutn : Nat.card (Outer L) ∣ 3 * 2 := by
    rw [Nat.card_congr eO.toEquiv, hOutcard]
  obtain ⟨E, hE, hE9⟩ := exists_elemAbelian_nine_projSp (K := K)
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
    refine le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨E.map eK.symm.toMonoidHom, le_top,
        CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 _ _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective eK.symm.injective, hE9]
    norm_num
  exact KFactProofs.TargetTwo.target_of_data (p := 3) (a := 4) (n := 13045760) (m := 2) (ℓ := 7)
    Nat.prime_three hsimple hcard (by norm_num) (by norm_num) hrank hOutL hOutn (by norm_num)
    (by norm_num) (by norm_num) (by rw [hcard]; norm_num)
    (fun k hk hk5 => by interval_cases k <;> norm_num)

end CFSG.AGLEmbedding
