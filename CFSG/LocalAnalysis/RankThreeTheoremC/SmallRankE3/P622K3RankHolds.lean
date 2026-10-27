module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3Defs
public import CFSG.HardMathSupport.Dickson.I271.Support.CyclicRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2401ThreeLie
import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup TauCeti CFSG.HardMathSupport.Dickson.I271
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.TauCetiBridge
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (IsReeIndex IsRankTwoOddIndex)

section Certificates


theorem two_le_pRank_of_lieChar (hB : ChevalleyBridges) (hR : ReeG2Bridge) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p < 5) {S : Type} [Group S] [Finite S]
    (d : TauCeti.ValidLieTypeIndex) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hchar : d.1.characteristic = p) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup S) := by
  by_contra hlt
  have hrk : CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 1 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hv⟩ := d
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    obtain ⟨-, hc | ⟨hn, -⟩⟩ :=
      CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.lieModel_typeA r q hv
    · have h5 := (classical_rankOne hp2
        (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hc) hrk).2.2.1
      omega
    · omega
  | twistedA r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e) hrk).1 (by decide)
  | B r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have hr2 : 2 ≤ r := hrange.1
    rcases (show r = 2 ∨ 3 ≤ r by omega) with rfl | hr3
    · exact absurd (classical_rankOne hp2
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e) hrk).1 (by decide)
    · exact absurd (classical_rankOne hp2
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd r q hv hp2 hr3 e) hrk).1
        (by decide)
  | C r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeC r q hv e) hrk).1 (by decide)
  | D r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e) hrk).1 (by decide)
  | twistedD r q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    exact absurd (classical_rankOne hp2
      (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q hv e) hrk).1
      (by decide)
  | E6 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.e6 (Or.inr (Or.inr (Or.inl rfl))) q hv hp2 e
    omega
  | E7 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.e7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) q hv hp2 e
    omega
  | E8 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.e8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) q hv hp2 e
    omega
  | F4 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.f4 (Or.inr (Or.inl rfl)) q hv hp2 e
    omega
  | G2 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := untwisted_two_le_pRank hB.g2 (Or.inl rfl) q hv hp2 e
    omega
  | twistedE6 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := twistedE6_two_le_pRank hB.twistedE6 q hv hp2 e
    omega
  | trialityD4 q =>
    have hq : q.p = p := by simpa using hchar
    subst hq
    have := trialityD4_two_le_pRank hB.trialityD4 q hv hp2 e
    omega
  | reeG2 m =>
    have hp3 : p = 3 := by simpa using hchar.symm
    subst hp3
    have := reeG2_two_le_pRank hR m hv e
    omega
  | suzuki m => exact (hp2 (by simpa using hchar.symm)).elim
  | reeF4 m => exact (hp2 (by simpa using hchar.symm)).elim
  | tits => exact (hp2 (by simpa using hchar.symm)).elim

theorem characteristic_eq_three_of_isReeIndex {d : TauCeti.LieTypeIndex} (h : IsReeIndex d) :
    d.characteristic = 3 := by
  cases d <;> simp_all [IsReeIndex]

theorem two_le_pRank_three_top {S : Type} [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex)
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : d.1.characteristic = 3 ∨ IsReeIndex d.1 ∨ IsRankTwoOddIndex d.1) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) := by
  by_cases h3 : d.1.characteristic = 3
  · exact two_le_pRank_of_lieChar chevalleyBridges reeG2Bridge Nat.prime_three (by norm_num)
      (by norm_num) d e h3
  have hrk : IsRankTwoOddIndex d.1 := by
    rcases hd with h | h | h
    · exact absurd h h3
    · exact absurd (characteristic_eq_three_of_isReeIndex h) h3
    · exact h
  obtain ⟨dd, hv⟩ := d
  rcases CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.rankTwoOdd_cases dd hrk with
    ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩ | ⟨q, rfl, -⟩
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_A3 hv e
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_twistedA3 hv e
      (by simpa using h3)
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_B2 hv e
  · exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lie2401.two_le_pRank_three_of_G2 hv e

theorem kFactThreeRankTwo_holds : KFactThreeRankTwo := by
  intro A _ _ L d ⟨e⟩ hd
  have hL : CFSG.Open.pRank 3 L = CFSG.pRank 3 ↥L :=
    (CFSG.SectionRank.pRank_coe_eq_openPRank 3 L).symm
  have hA : CFSG.pRank 3 ↥L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
    CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥L
  rw [hL, hA]
  exact two_le_pRank_three_top d e hd

end Certificates

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
