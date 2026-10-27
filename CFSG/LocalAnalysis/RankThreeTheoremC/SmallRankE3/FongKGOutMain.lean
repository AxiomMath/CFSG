module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutClassical
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutOmegaMinus
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutExcA
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutExcB
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongNoncycE3Rank
public import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

open TauCeti CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof (OutTwoCyclic)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3 (KGThreeRankBig KGNoncycCentSmall KGNoncycCentE3
  KGNoncycCentL34 KGConcl)

set_option linter.unusedSectionVars false

theorem statedClassical_of_lieModel {G : Type} [Group G] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : CFSG.Models.LieModel G t n p f) : StatedClassicalModel G t n p f := by
  rcases h with ⟨-, h | ⟨h0, -⟩⟩
  · exact h
  · exact absurd h0 hn

@[expose] def L34Data (K : Type) [Group K] : Prop :=
  ∃ (n k : ℕ) (F : Type) (_ : Field F) (_ : Finite F), (n = 3 ∨ n = 4) ∧ Nat.card F = 4 ^ k ∧
    Nonempty (K ≃* LinearFlag.projectiveSL n F)




theorem chev2_dispatch {K : Type} [Group K] [Finite K] (hchev : IsChevSimple 2 K)
    (hnotbig : ¬ catalogIs K (onLie KGThreeRankBig)) : L34Data K ∨ OutTwoCyclic K := by
  rcases hchev with hL | hA
  · obtain ⟨i, hi, ⟨e⟩⟩ := hL
    cases i with
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change d.characteristic = 2 at hi
      have hnb : ¬ KGThreeRankBig d := fun hb => hnotbig ⟨.lie ⟨d, hv⟩, hb, ⟨e⟩⟩
      have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
      cases d with
      | A n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hmodel : StatedClassicalModel K .PSL (n + 1) q.p q.exponent :=
          CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        rw [hp2] at hmodel
        by_cases hn1 : n = 1
        · subst hn1
          right
          exact outTwoCyclic_PSL_two hmodel
        · have hn2 : 2 ≤ n := by omega
          by_cases hev : Even q.exponent
          · have hn3 : n ≤ 3 := by
              by_contra hn3
              exact hnb ⟨by omega, hp2, hev⟩
            left
            obtain ⟨k, hk⟩ := hev
            obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel
            refine ⟨n + 1, k, F, inferInstance, inferInstance, by omega, ?_,
              ⟨eF.trans (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.statedProjSLEquiv (n + 1) F)⟩⟩
            rw [hF, hk, ← two_mul, pow_mul]
            norm_num
          · right
            exact outTwoCyclic_PSL_odd (by omega) (Nat.not_even_iff_odd.mp hev) hmodel
      | twistedA n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hc : ValidLieTypeIndex.characteristic ⟨.twistedA n q, hv⟩ = q.p :=
          LieTypeIndex.characteristic_twistedA n q
        have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA n q, hv⟩ = q.exponent :=
          LieTypeIndex.fieldExponent_twistedA n q
        have hmodel : StatedClassicalModel K .PSU (n + 1) q.p q.exponent := by
          have := statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedA n q hv e)
          rwa [hc, hf] at this
        rw [hp2] at hmodel
        right
        exact outTwoCyclic_PSU hmodel
      | B n q =>
        have hp2 : q.p = 2 := by simpa using hi
        right
        rcases CFSG.Models.lieModel_B n q hv e with hm | hm
        · have hmodel : StatedClassicalModel K .PSp n q.p q.exponent :=
            statedClassical_of_lieModel (by omega) hm
          rw [hp2] at hmodel
          exact outTwoCyclic_PSp (by omega) hmodel
        · exfalso
          obtain ⟨⟨-, -, -, hne⟩, -⟩ := hm
          exact hne hp2
      | C n q =>
        exfalso
        have hp2 : q.p = 2 := by simpa using hi
        exact hr.2 hp2
      | D n q =>
        exfalso
        have hp2 : q.p = 2 := by simpa using hi
        exact hnb hp2
      | twistedD n q =>
        have hp2 : q.p = 2 := by simpa using hi
        by_cases hn5 : 5 ≤ n
        · exact absurd ⟨hn5, hp2⟩ hnb
        · right
          have hn4 : n = 4 := by omega
          subst hn4
          have hmodel : StatedClassicalModel K .POmegaMinus 4 q.p q.exponent :=
            statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedD 4 q hv e)
          rw [hp2] at hmodel
          exact outTwoCyclic_POmegaMinus (le_refl 4) hmodel
      | E6 q => exact absurd trivial hnb
      | E7 q => exact absurd trivial hnb
      | E8 q => exact absurd trivial hnb
      | F4 q => exact absurd trivial hnb
      | G2 q =>
        right
        exact outTwoCyclic_G2 q hv (by simpa using hi) e
      | twistedE6 q => exact absurd trivial hnb
      | trialityD4 q =>
        right
        exact outTwoCyclic_trialityD4 q hv (by simpa using hi) e
      | reeG2 m => exact absurd hi (by simp)
      | suzuki m =>
        right
        exact outTwoCyclic_suzuki m hv e
      | reeF4 m =>
        right
        exact outTwoCyclic_reeF4 m hv e
      | tits =>
        right
        exact outTwoCyclic_tits hv e
  · obtain ⟨i, hi, ⟨e⟩⟩ := hA
    right
    cases i with
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])
    | alternating n hn5 =>
      rcases hi with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨h8, -⟩
      · exact outTwoCyclic_alt_five_eight (Or.inl h5) e
      · subst h6
        exact outTwoCyclic_alt_six e
      · exact outTwoCyclic_alt_five_eight (Or.inr h8) e
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change ambiguousChev 2 (.lie ⟨d, hv⟩) at hi
      cases d with
      | A r q =>
        by_cases hr1 : r = 1
        · subst hr1
          rcases hi with ⟨h7, -⟩ | ⟨-, h23⟩
          · exact outTwoCyclic_A1_seven q hv h7 e
          · exact absurd h23 (by norm_num)
        · exfalso
          simp [ambiguousChev, hr1] at hi
      | twistedA r q =>
        rcases Nat.lt_or_ge r 4 with h4 | h4
        · interval_cases r
          · exact hi.elim
          · exact hi.elim
          · exact outTwoCyclic_twistedA2_three q hv hi.1 e
          · exact absurd hi.2 (by norm_num)
        · obtain ⟨r', rfl⟩ := Nat.exists_eq_add_of_le' h4
          exact False.elim hi
      | _ => exact absurd hi (by simp [ambiguousChev])


theorem kgNoncycCentSmall_of_L34 (hL34 : KGNoncycCentL34) : KGNoncycCentSmall := by
  intro K _ _ p hp hp5 hsimple hnonab hchev hK3 hnotbig
  rcases chev2_dispatch hchev hnotbig with ⟨n, k, F, _, _, hn, hF, ⟨e⟩⟩ | hOut
  · exact kgConcl_of_mulEquiv e (hL34 n k F hn hF p hp hp5)
  · intro S B hS2 hnc hSinn hB hBS
    exact absurd (hOut S hS2 hSinn) hnc

theorem kgNoncycCentE3_of_L34 (hL34 : KGNoncycCentL34) : KGNoncycCentE3 :=
  FongNoncyc.kgNoncycCentE3_of_small (kgNoncycCentSmall_of_L34 hL34)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut
