module

public import CFSG.CGT.PushingUpLit.SolK.TI
public import CFSG.CGT.PushingUpLit.SolK.ThreeR1
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.Timmesfeld75
  CFSG.Assembly.LowTwoRank CFSG.CGT.PushingUpLit CFSG.GH74 CFSG.CGT.PushingUpLit.BHS
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.Open (IsElemAbelian)

@[expose] def SolDegreeThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    CFSG.Assembly.IsCharTwoType G → ∀ M X : Subgroup G, IsMaximalTwoLocal M → X ≤ M →
      (X.subgroupOf M).Normal → IsShortGroup ↥X → IsNaturalAltModule ↥X 1 →
      maximalTwoLocalsContaining (X : Set G) = {M} → SectionalTwoRankLE G 4

@[expose] def SolDegreeThreeRNe1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    CFSG.Assembly.IsCharTwoType G → ∀ M X : Subgroup G, IsMaximalTwoLocal M → X ≤ M →
      (X.subgroupOf M).Normal → IsShortGroup ↥X → IsNaturalAltModule ↥X 1 →
      maximalTwoLocalsContaining (X : Set G) = {M} → rOf M X ≠ ⊥ → SectionalTwoRankLE G 4

theorem solDegreeThree_of_rNe1 (h : SolDegreeThreeRNe1) : SolDegreeThree := by
  intro G _ _ hKP hsimple hchar M X hMmax hXM hnorm hshort hnat huniq
  by_cases hR : rOf M X = ⊥
  · exact sectionalTwoRankLE_four_of_three_rOf_bot hchar hMmax hXM hnorm hshort hnat huniq hR
  · exact h G hKP hsimple hchar M X hMmax hXM hnorm hshort hnat huniq hR

theorem false_of_tiData (hT75 : T75Structural) {G : Type} [Group G] [Finite G]
    (hKP : KProper InCatalog G) {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)
    (hTI : TIData S) : False := by
  have hnormQ : Subgroup.normalizer (pCoreOf 2 M : Set G) = M := S.normalizer_Q_eq
  refine hT75 G hKP S.hyp.simple (pCoreOf 2 M) X n S.hyp.two_le hTI.elem hTI.ti hTI.wc hTI.cent
    ?_ ?_ ?_ S.hyp.short S.hyp.nat
  · rw [hnormQ]; exact S.hyp.le
  · rw [hnormQ]; exact S.hyp.normal
  · rw [← pCoreOf_eq_map]; exact S.xnorm.Y_le_Q

end CFSG.CGT.PushingUpLit.SolK
