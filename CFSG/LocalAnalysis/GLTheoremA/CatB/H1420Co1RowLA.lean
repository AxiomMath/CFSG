module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyLie
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyAlt
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeTwo
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415b
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.InputsAlt72
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8140
public import Certificates.Certificate8141
public import Certificates.Certificate8166
import CFSG.GH74.KGroups.L34Aut
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1ThreeAFinal
import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3All
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.Spor.Easy
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporAll
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCheck
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporCo
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFi23
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporFiveB
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHN3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporHe3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporJ3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporLy
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRu3
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporSuz
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh
import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporTh7
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Pass

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (LieOrderBridge SporadicOrdersTable sporOrd)

theorem not_isChevSimple_of_card_suz (hb : LieOrderBridge) {T : Type} [Group T] [Finite T]
    (hT : Nat.card T = 448345497600) {q : ℕ} (hq : q.Prime) : ¬ IsChevSimple q T := by
  by_cases h2 : q = 2
  · subst h2
    exact I1416Rows.not_isChevSimple_two_of_card_suz hb hT
  · exact not_isChevSimple_odd_of_card hb hT (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by norm_num) (by norm_num)
      hq h2

theorem co1Row_lie_of_facts (hOrd : SporadicOrdersTable) (hb : LieOrderBridge)
    (hD : ∀ q : ℕ, KDChevDownQ 3 q) {S : Type} [Group S] [Finite S]
    (idx : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie idx).Group)
    {β : MulAut S} {J : Subgroup S} (hcore : I1420Core 3 3 .Suz β J) : False :=
  i1420LieSpor_holds hOrd hD (fun _ hq _ _ _ hT => not_isChevSimple_of_card_suz hb hT hq) idx e
    hcore

theorem co1Row_alt_of_facts (hOrd : SporadicOrdersTable) (hAD : KDAltDown) {S : Type} [Group S]
    [Finite S] {n : ℕ} (hn : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n)) {β : MulAut S}
    {J : Subgroup S} (hcore : I1420Core 3 3 .Suz β J) : False :=
  i1420AltSpor_holds Nat.prime_three (by norm_num) hOrd hAD
    (fun m => CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415b.factorial_half_ne_sporOrd m
      .Suz) hn e hcore

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
