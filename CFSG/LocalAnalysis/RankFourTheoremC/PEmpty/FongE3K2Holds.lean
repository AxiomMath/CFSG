module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3K2
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongE3SporC
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278ChevP
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278ChevQ
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDI278Spor
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDL64I204U3
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKFSporB
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3SporSections
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.LocalAnalysis.GL83PartI.I713.Final
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64L3GenCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankThreeTheoremC

theorem sporSectionFacts3_holds :
    SporSectionFacts3 := by
  have h2324 := CFSG.RankThree.PartOne.sectionsForceEvenRankFour_fi23_fi24prime
    CFSG.RankThree.PartOne.sectionsForceEvenRankFour_Fi22
    CFSG.RankThree.PartOne.hasSection_fi23_fi22 CFSG.RankThree.PartOne.hasSection_fi24prime_fi23
  exact ⟨CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group,
    CFSG.RankThree.PartOne.sectionsForceEvenRankFour_Fi22, h2324.1, h2324.2,
    CFSG.RankThree.PartOne.sectionsForceEvenRankFour_B,
    CFSG.RankThree.PartOne.simplePresentationM_sections_of_B_section
      CFSG.RankThree.PartOne.sectionsForceEvenRankFour_B
      CFSG.RankThree.PartOne.simplePresentationMHasBSection_holds⟩

theorem noMonsterSection_of_sections (hsec : SporSectionFacts3) {A : Type} [Group A] [Finite A]
    (he : CFSG.Open.evenRank A = 3) : NoMonsterSection A := by
  intro H N _ K hK hM
  obtain ⟨e⟩ := hM
  exact noExcludedSection3_of_sections hsec he H N K hK .M (by simp [sectionExcludedNames3]) ⟨e⟩

theorem kFactP65RankTwoE3_holds :
    KFactP65RankTwoE3 :=
  kFactP65RankTwoE3_of_kdata GL83.I713.i_7_13_1_holds kdI278ChevP_holds kdi278L3_holds
    kdI278ChevQ_holds kdI278Spor_holds kdI278SporB_holds kdI278SporCNoM_holds kdL64I204U3_holds

theorem kFactP65RankTwoAt_of_evenRank_three
    (A : Type) [Group A] [Finite A]
    (he : CFSG.Open.evenRank A = 3) : KFactP65RankTwoAt A :=
  kFactP65RankTwoE3_holds A (noMonsterSection_of_sections sporSectionFacts3_holds he)

theorem kFactP65RankTwoS_holds :
    KFactP65RankTwoS :=
  fun G _ _ hS => kFactP65RankTwoAt_of_evenRank_three G hS.rank

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
