module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanTwoGenInnerLie
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
import CFSG.RankThree.PartOne.S11d.OddOutPSL2
import CFSG.RankThree.PartOne.MB3.OddOutLinear
import CFSG.RankThree.PartOne.SPOR.I613Even

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open TauCeti CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.OutStructure
open CFSG.Blueprint (LieModel EvenLieType)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.AGLEmbedding (IsClassicalOrG2Index IsClassicalTwoOrG2 IsOrthogonalTwo)

section Bridge


theorem evenLieType_of_isClassicalOrG2Index {S : Type} [Group S] [Finite S]
    {d : ValidLieTypeIndex} (hd : IsClassicalOrG2Index d.1)
    (e : S ≃* (CFSGIndex.lie d).Group) : EvenLieType S := by
  obtain ⟨d', hv⟩ := d
  have h : IsoLie S d' := ⟨hv, ⟨e⟩⟩
  cases d' with
  | A r q => exact CFSG.RankThree.PartOne.N143.evenLieType_of_isoLie_A hd h
  | twistedA r q => exact CFSG.RankThree.PartOne.N143.evenLieType_of_isoLie_twistedA hd h
  | B r q =>
    have hr : 2 ≤ r :=
      ((LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1).1
    exact CFSG.RankThree.PartOne.N143.evenLieType_of_isoLie_B hd hr h
  | D r q => exact CFSG.RankThree.PartOne.N143.evenLieType_of_isoLie_D hd h
  | twistedD r q => exact CFSG.RankThree.PartOne.N143.evenLieType_of_isoLie_twistedD hd h
  | G2 q =>
    exact CFSG.RankThree.PartOne.SPOR.evenExceptionalBridge_holds S (Or.inl ⟨q, hd, Or.inl h⟩)
  | _ => exact hd.elim

end Bridge

section Family


theorem pGoodOut_of_isClassicalTwoOrG2 {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : IsClassicalTwoOrG2 S)
    (hL : ∀ {n f : ℕ}, StatedClassicalModel S .PSL n 2 f → ¬ p ∣ Nat.gcd n (2 ^ f - 1))
    (hU : ∀ {n f : ℕ}, StatedClassicalModel S .PSU n 2 f → ¬ p ∣ Nat.gcd n (2 ^ f + 1))
    (hD4 : D4PGood) : PGoodOut p S := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨d, (⟨q, hq, hd⟩ | ⟨q, hq, hd⟩), ⟨e⟩⟩
  · obtain ⟨t, n, f, hadm, hmodel⟩ := evenLieType_of_isClassicalOrG2Index hd e
    exact pGoodOut_of_lieModel hp hp5 hadm hmodel (fun hm => hL hm) (fun hm => hU hm) hD4
  · exact pGoodOut_of_alternating (by omega) hp hp5 e
  ·
    obtain ⟨d', hv⟩ := d
    have hd' : d' = .A 1 q := hd
    subst hd'
    have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
    have h7 : q.p = 7 ∧ q.exponent = 1 :=
      (Nat.Prime.pow_eq_iff (by norm_num : Nat.Prime 7)).1 (by simpa using hq)
    have hp2 : q.p ≠ 2 := by omega
    exact pGoodOut_of_outPNice (outPNice_PSL_two_odd hp (by omega) hp2 hm)
  ·
    obtain ⟨d', hv⟩ := d
    have hd' : d' = .twistedA 2 q := hd
    subst hd'
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
    refine pGoodOut_of_outPNice (outPNice_PSU_odd hp hm fun hdvd => ?_)
    have h3 : p ∣ 2 + 1 := hdvd.trans (Nat.gcd_dvd_left _ _)
    have := Nat.le_of_dvd (by norm_num) h3
    omega

theorem pGoodOut_of_isOrthogonalTwo {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (h : IsOrthogonalTwo S) (hD4 : D4PGood) : PGoodOut p S := by
  rcases h with ⟨d, ⟨m, q, hq, hd⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  swap
  · exact pGoodOut_of_alternating (by omega) hp hp5 e
  have hq1 : q.p = 2 ∧ q.exponent = 1 :=
    (Nat.Prime.pow_eq_iff Nat.prime_two).1 (by simpa using hq)
  obtain ⟨d', hv⟩ := d
  have key : ∃ (t : StatedLieTag) (n : ℕ), StatedLieAdmissible t n 2 1 ∧ LieModel S t n 2 1 := by
    rcases hd with hd | hd | ⟨hm3, hd⟩
    · have hd' : d' = .D m q := hd
      subst hd'
      have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even m q hv hq1.1 e
      rw [hq1.1, hq1.2] at hm
      exact ⟨_, _, hm.1, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hm⟩⟩
    · have hd' : d' = .twistedD m q := hd
      subst hd'
      have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even m q hv hq1.1 e
      rw [hq1.1, hq1.2] at hm
      exact ⟨_, _, hm.1, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hm⟩⟩
    · have hd' : d' = .twistedA 3 q := hd
      subst hd'
      subst hm3
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hq1.1, hq1.2] at hm
      exact ⟨_, _, hm.1, Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hm⟩⟩
  obtain ⟨t, n, hadm, hmodel⟩ := key
  refine pGoodOut_of_lieModel hp hp5 hadm hmodel (fun _ hdvd => ?_) (fun _ hdvd => ?_) hD4
  · exact hp.not_dvd_one (by simpa using hdvd)
  · have h3 : p ∣ 2 ^ 1 + 1 := hdvd.trans (Nat.gcd_dvd_right _ _)
    have := Nat.le_of_dvd (by norm_num) h3
    omega

end Family

end CFSG.AGLEmbedding.TwoGenInner
