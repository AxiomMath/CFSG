module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Exc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Aut
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3

open CFSG.Open Subgroup TauCeti
open CFSG.RankThree.PartTwo.Sec4.Census (TripleCoverLieIndex)

section Index

theorem char3_tripleCoverLieIndex {d : LieTypeIndex} (hd : d.characteristic = 3)
    (h : TripleCoverLieIndex d) :
    (∃ q, d = .twistedA 3 q ∧ q.card = 3) ∨ (∃ q, d = .B 3 q ∧ q.card = 3) ∨
      (∃ q, d = .G2 q ∧ q.card = 3) := by
  cases d with
  | A r q =>
    have hp : q.p = 3 := by simpa using hd
    have hc : 3 ∣ q.card := by
      rw [PrimePower.card_def, hp]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    have h1 := h.2
    have h2 : 1 ≤ q.card := Nat.one_le_iff_ne_zero.mpr (by
      rw [PrimePower.card_def]
      exact pow_ne_zero _ q.prime_p.ne_zero)
    omega
  | twistedA r q =>
    have hp : q.p = 3 := by simpa using hd
    have hc : 3 ∣ q.card := by
      rw [PrimePower.card_def, hp]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    rcases h with ⟨-, h1⟩ | ⟨rfl, h1⟩
    · omega
    · exact Or.inl ⟨q, rfl, h1⟩
  | B r q =>
    obtain ⟨rfl, h1⟩ := h
    exact Or.inr (Or.inl ⟨q, rfl, h1⟩)
  | C r q => exact h.elim
  | D r q => exact h.elim
  | twistedD r q => exact h.elim
  | E6 q =>
    have hp : q.p = 3 := by simpa using hd
    have hc : 3 ∣ q.card := by
      rw [PrimePower.card_def, hp]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    have h2 : 1 ≤ q.card := Nat.one_le_iff_ne_zero.mpr (by
      rw [PrimePower.card_def]
      exact pow_ne_zero _ q.prime_p.ne_zero)
    have h1 : 3 ∣ q.card - 1 := h
    omega
  | E7 q => exact h.elim
  | E8 q => exact h.elim
  | F4 q => exact h.elim
  | G2 q => exact Or.inr (Or.inr ⟨q, rfl, h⟩)
  | twistedE6 q =>
    have hp : q.p = 3 := by simpa using hd
    have hc : 3 ∣ q.card := by
      rw [PrimePower.card_def, hp]
      exact dvd_pow_self 3 q.exponent_pos.ne'
    have h1 : 3 ∣ q.card + 1 := h
    omega
  | trialityD4 q => exact h.elim
  | suzuki m => exact h.elim
  | reeG2 m => exact h.elim
  | reeF4 m => exact h.elim
  | tits => exact h.elim

end Index

section Certified


variable {X : Type} [Group X] [Finite X]

theorem false_of_cover_setup {L : Subgroup X} {x : X} (h : T29Setup X L x)
    (hZ : center ↥L ≠ ⊥) (d : ValidLieTypeIndex) (hd : d.1.characteristic = 3)
    (e : (↥L ⧸ center ↥L) ≃* (CFSGIndex.lie d).Group) : False := by
  have hp3 : IsPGroup 3 ↥(center ↥L) := h.center_isPGroup
  have hdvd : 3 ∣ Nat.card ↥(center ↥L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp3
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hZ
      exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
    rw [hk]
    exact dvd_pow_self 3 hk0
  have hGA : CFSG.Open.GriessAllModelsStatement :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
  have hcover : CFSG.RankThree.PartTwo.Sec4.Census.IsThreeCenterCover ↥L (CFSGIndex.lie d).Group :=
    ⟨CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isQuasisimple_of_open' h.comp.2.2, hdvd, ⟨e⟩⟩
  have hidx : TripleCoverLieIndex d.1 :=
    CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds d ↥L hcover
  have hle3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) ≤ 3 := h.pRank_component_le
  have hrk := rank_dichotomy d hd e
  have hqs : CFSG.Open.IsQuasisimple ↥L := h.comp.2.2
  have hLC : CFSG.HardMathSupport.Timmesfeld.Coordinator.LieCentralQuotient ↥L := ⟨d, ⟨e⟩⟩
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ center ↥L)) := by
    rcases char3_tripleCoverLieIndex hd hidx with ⟨q, hq, -⟩ | ⟨q, hq, -⟩ | ⟨q, hq, -⟩ <;>
    rcases hrk with h4 | ⟨q', hq', -⟩ | ⟨q', hq', -⟩ | ⟨q', hq', -⟩
    all_goals first
      | exact h4
      | (exfalso
         have := hq'.symm.trans hq
         simp at this)
  have hcov := CFSG.HardMathSupport.Timmesfeld.LieRank.lieCoverRankHighExc3_holds hGA ↥L hqs hLC 3
    Nat.prime_three (by norm_num) hdvd (by omega)
  obtain ⟨dd, hv⟩ := d
  change dd.characteristic = 3 at hd
  have hpar : ∃ (t : CFSG.Open.StatedLieTag) (n r f : ℕ),
      ((t = .PSL ∧ n = 2 ∧ r = 3 ∧ f = 2) ∨ (t = .POmegaOdd ∧ n = 3 ∧ r = 3 ∧ f = 1) ∨
        (t = .G2 ∧ n = 0 ∧ r = 3 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ r = 3 ∧ f = 1)) ∧
      CFSG.Blueprint.LieModel (↥L ⧸ center ↥L) t n r f := by
    rcases char3_tripleCoverLieIndex hd hidx with ⟨q, hq, hqc⟩ | ⟨q, hq, hqc⟩ | ⟨q, hq, hqc⟩
    · subst hq
      obtain ⟨hp, he⟩ := primePower_card_three hqc
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 3 q hv e
      rw [hp, he] at hm
      exact ⟨.PSU, 4, 3, 1, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)),
        Or.inl ⟨by decide, hm⟩⟩
    · subst hq
      obtain ⟨hp, he⟩ := primePower_card_three hqc
      have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_odd 3 q hv
        (by rw [hp]; norm_num) le_rfl e
      rw [hp, he] at hm
      exact ⟨.POmegaOdd, 3, 3, 1, Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩),
        Or.inl ⟨by decide, hm⟩⟩
    · subst hq
      obtain ⟨hp, he⟩ := primePower_card_three hqc
      have hU := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.untwistedChevalleyModel_of_bridge
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 e
      have hU' : CFSG.Blueprint.UntwistedChevalleyModel (↥L ⧸ center ↥L) .G2 (3 ^ 1) := by
        have h1 : q.p ^ q.exponent = 3 ^ 1 := by rw [hp, he]
        rw [← h1]
        exact hU
      exact ⟨.G2, 0, 3, 1, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)),
        Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_three, le_rfl, rfl, by norm_num⟩, hU'⟩)⟩
  obtain ⟨t, n, r, f, hpat, hm⟩ := hpar
  have hle := hcov ⟨rfl, t, n, r, f, hpat, hm⟩
  omega

end Certified

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3
