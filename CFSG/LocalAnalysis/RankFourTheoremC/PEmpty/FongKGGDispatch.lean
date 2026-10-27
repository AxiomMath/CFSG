module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongKGOutMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGLn
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGOutExc

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open TauCeti CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof (OutTwoCyclic)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple catalogIs onLie ambiguousChev)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3 (KGConcl)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongOut

set_option linter.unusedSectionVars false

@[expose] def LnData (K : Type) [Group K] : Prop :=
  ∃ (n k : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 3 ≤ n ∧ Nat.card F = 4 ^ k ∧
    Nonempty (K ≃* LinearFlag.projectiveSL n F)

@[expose] def DnData (K : Type) [Group K] : Prop :=
  ∃ n f : ℕ, 4 ≤ n ∧ StatedClassicalModel K .POmegaPlus n 2 f

@[expose] def E6Data (K : Type) [Group K] : Prop :=
  ∃ f : ℕ, CFSG.Blueprint.ChevalleyExceptionalModel K .E6 2 f

@[expose] def KGConclPOmegaPlus : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (n f : ℕ), 4 ≤ n → StatedClassicalModel K .POmegaPlus n 2 f →
    ∀ p : ℕ, KGConcl K p

@[expose] def KGConclE6 : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (f : ℕ),
    CFSG.Blueprint.ChevalleyExceptionalModel K .E6 2 f → ∀ p : ℕ, KGConcl K p


theorem chev2_dispatch_all {K : Type} [Group K] [Finite K] (hchev : IsChevSimple 2 K) :
    LnData K ∨ DnData K ∨ E6Data K ∨ OutTwoCyclic K := by
  rcases hchev with hL | hA
  · obtain ⟨i, hi, ⟨e⟩⟩ := hL
    cases i with
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
    | lie dd =>
      obtain ⟨d, hv⟩ := dd
      change d.characteristic = 2 at hi
      have hr := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
      cases d with
      | A n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hmodel : StatedClassicalModel K .PSL (n + 1) q.p q.exponent :=
          CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv_typeA hv e
        rw [hp2] at hmodel
        by_cases hn1 : n = 1
        · subst hn1
          right; right; right
          exact outTwoCyclic_PSL_two hmodel
        · have hn2 : 2 ≤ n := by omega
          by_cases hev : Even q.exponent
          · left
            obtain ⟨k, hk⟩ := hev
            obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hmodel
            refine ⟨n + 1, k, F, inferInstance, inferInstance, by omega, ?_,
              ⟨eF.trans (CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.statedProjSLEquiv (n + 1) F)⟩⟩
            rw [hF, hk, ← two_mul, pow_mul]
            norm_num
          · right; right; right
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
        right; right; right
        exact outTwoCyclic_PSU hmodel
      | B n q =>
        have hp2 : q.p = 2 := by simpa using hi
        right; right; right
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
        have hp2 : q.p = 2 := by simpa using hi
        have hmodel : StatedClassicalModel K .POmegaPlus n q.p q.exponent :=
          statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_D n q hv e)
        rw [hp2] at hmodel
        right; left
        exact ⟨n, q.exponent, hmodel.1.2.2, hmodel⟩
      | twistedD n q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hmodel : StatedClassicalModel K .POmegaMinus n q.p q.exponent :=
          statedClassical_of_lieModel (by omega) (CFSG.Models.lieModel_twistedD n q hv e)
        rw [hp2] at hmodel
        right; right; right
        exact outTwoCyclic_POmegaMinus hmodel.1.2.2 hmodel
      | E6 q =>
        have hp2 : q.p = 2 := by simpa using hi
        have hce : CFSG.Blueprint.ChevalleyExceptionalModel K .E6 q.p q.exponent :=
          ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
            CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hp2 e⟩
        rw [hp2] at hce
        right; right; left
        exact ⟨q.exponent, hce⟩
      | E7 q =>
        right; right; right
        exact outTwoCyclic_E7 q hv (by simpa using hi) e
      | E8 q =>
        right; right; right
        exact outTwoCyclic_E8 q hv (by simpa using hi) e
      | F4 q =>
        right; right; right
        exact outTwoCyclic_F4 q hv (by simpa using hi) e
      | G2 q =>
        right; right; right
        exact outTwoCyclic_G2 q hv (by simpa using hi) e
      | twistedE6 q =>
        right; right; right
        exact outTwoCyclic_twistedE6 q hv (by simpa using hi) e
      | trialityD4 q =>
        right; right; right
        exact outTwoCyclic_trialityD4 q hv (by simpa using hi) e
      | reeG2 m => exact absurd hi (by simp)
      | suzuki m =>
        right; right; right
        exact outTwoCyclic_suzuki m hv e
      | reeF4 m =>
        right; right; right
        exact outTwoCyclic_reeF4 m hv e
      | tits =>
        right; right; right
        exact outTwoCyclic_tits hv e
  · obtain ⟨i, hi, ⟨e⟩⟩ := hA
    right; right; right
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

theorem kgNoncycCent_of_gen (hD : KGConclPOmegaPlus) (hE : KGConclE6) :
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGNoncycCent := by
  intro K _ _ p _ _ _ _ hchev
  rcases chev2_dispatch_all hchev with ⟨n, k, F, _, _, hn, hF, ⟨e⟩⟩ | ⟨n, f, hn, hm⟩ | ⟨f, hm⟩ | hOut
  · exact kgConcl_of_mulEquiv e (kgConcl_projectiveSL hn hF p)
  · exact hD K n f hn hm p
  · exact hE K f hm p
  · intro S B hS2 hnc hSinn _ _
    exact absurd (hOut S hS2 hSinn) hnc

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG
