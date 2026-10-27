module

public import CFSG.RankThree.PartOne.S10.PlaneLocalRankTwoLocal
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltZ
import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Split
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Fi22Five
public import CFSG.RankThree.PartTwo.Sec4.Census.Open43

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover)

theorem k37R_not_four_le_localRank {X : Type} [Group X] [Finite X]
    (h23 : ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
      CFSG.pRank 3 ↥(Subgroup.normalizer (T : Set X)) ≤ 3) :
    ¬ 4 ≤ localRank 3 X := by
  intro h4
  obtain ⟨U, hU2, hU0, E, hEN, hE, hEc⟩ :=
    (CFSG.RankThree.PartOne.SourceSixThirteen.le_localRank_iff_exists Nat.prime_three
      (by norm_num : 1 ≤ 4)).1 h4
  have h1 : 4 ≤ CFSG.Assembly.pRank 3 (Subgroup.normalizer (U : Set X)) :=
    (CFSG.RankThree.PartOne.Planes.le_pRank_iff Nat.prime_three _ 4).2 ⟨E, hEN, hE, hEc⟩
  rw [CFSG.RankThree.PartOne.assembly_pRank_eq Nat.prime_three] at h1
  exact absurd (h23 U hU0 hU2) (by omega)

theorem k37R_false_of_four_le_localRank {X : Type} [Group X] [Finite X] {K E S : Subgroup X}
    (h : K37Setting X K E S) {Y : Subgroup X} (h4 : 4 ≤ localRank 3 ↥Y) : False :=
  k37R_not_four_le_localRank h.rank23
    (h4.trans (CFSG.RankThree.PartOne.OddCore37.localRank_subgroup_le Nat.prime_three Y))

theorem k37R_exists_cover {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (hcore : CFSG.pPrimeCore 3 ↥K = ⊥) {S : Type} [Group S]
    (hc : IsThreeCenterCover ↥K S) :
    ∃ φ : ↥K →* S, Function.Surjective φ ∧ φ.ker = Subgroup.center ↥K ∧
      3 ∣ Nat.card φ.ker ∧ Odd (Nat.card φ.ker) := by
  obtain ⟨-, h3, ⟨e⟩⟩ := hc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))).ker =
      Subgroup.center ↥K := by
    ext y
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center ↥K) y) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨a, ha⟩ := (CFSG.LocalAnalysis.GLTheoremA.KD264Z.isPGroup_center_of_pPrimeCore
    Nat.prime_three hcore).exists_card_eq
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), hker, by rw [hker]; exact h3, ?_⟩
  rw [hker, ha]
  exact Odd.pow (by decide)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H
