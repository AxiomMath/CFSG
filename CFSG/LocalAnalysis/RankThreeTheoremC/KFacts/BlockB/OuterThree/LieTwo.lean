module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OrthogonalRank
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOut
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutUnitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutOrth
public import CFSG.LargeExtraspecial.DW2AOutOrth
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankD4
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.LinHard

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
open CFSG.ComponentClassification.OuterAutomorphisms

theorem three_le_rank_of_twistedA_two {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.card = 2) : 3 ≤ r := by
  have hr : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases Nat.lt_or_ge r 3 with h | h
  · have := hr.2 (by omega)
    omega
  · exact h

theorem autThreePowInner_typeA_two {X : Type} [Group X] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A r q).Valid) (hq : q.card = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) : AutThreePowInner X := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have hr : 1 ≤ r ∧ (r = 1 → 4 ≤ q.card) :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hA := CFSG.AGLEmbedding.KFactProofs.CoverFive.statedClassicalModel_psl_of_typeA r q hv e
  rw [hp, hf] at hA
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.projSL_of_statedClassicalModel hA
  refine autThreePowInner_of_mulEquiv φ (autThreePowInner_projSL_gf2 ?_)
  rcases Nat.lt_or_ge r 2 with h | h
  · have := hr.2 (by omega)
    omega
  · omega

theorem autThreePowInner_typeTwistedA_two {X : Type} [Group X] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.card = 2) (h3 : ¬ 3 ∣ r + 1)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) : AutThreePowInner X := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have hr := three_le_rank_of_twistedA_two hv hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hp, hf] at h
  obtain ⟨φ⟩ := CFSG.RankThree.PartOne.projSU_of_statedClassicalModel h
  refine autThreePowInner_of_mulEquiv φ (autThreePowInner_of_not_three_dvd_outer ?_)
  rw [card_outer_projSU_eq (r + 1) 2 1 le_rfl (by omega) (fun h' => by have := h'.1; omega)]
  have hg : Nat.gcd (r + 1) (2 ^ 1 + 1) = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)
  rw [hg]
  norm_num

theorem autThreePowInner_typeB_two {X : Type} [Group X] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.B r q).Valid) (hq : q.card = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) : AutThreePowInner X := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have hr' : 2 ≤ r ∧ ¬(r = 2 ∧ q.card = 2) :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hr : 3 ≤ r := by
    rcases Nat.lt_or_ge r 3 with h' | h'
    · exact absurd ⟨by omega, hq⟩ hr'.2
    · exact h'
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hp hr e
  rw [hp, hf] at h
  exact autThreePowInner_psp_two hr h

theorem autThreePowInner_typeD_two {X : Type} [Group X] [Finite X] {r : ℕ}
    {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D r q).Valid) (hq : q.card = 2)
    (hr : 5 ≤ r) (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) : AutThreePowInner X := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hp e
  rw [hp, hf] at h
  have h2 := CFSG.LargeExtraspecial.DW.isPGroup_outer_POmegaPlus hr (Or.inl ⟨by decide, h⟩)
  have : Finite (MulAut X) := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.finite_mulAut_of_finite X
  have : Finite (Outer X) := Finite.of_surjective _ QuotientGroup.mk_surjective
  refine autThreePowInner_of_not_three_dvd_outer fun h3 => ?_
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [hk] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem autThreePowInner_typeTwistedD_two {X : Type} [Group X] {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid) (hq : q.card = 2)
    (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) : AutThreePowInner X := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have h := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hp e
  rw [hp, hf] at h
  have hr : 4 ≤ r :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  exact autThreePowInner_pomegaMinus_two hr h

theorem four_le_pRank_of_typeD4_two {K : Type} [Group K] [Finite K] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq : q.card = 2)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have hC := ChevTwoInnerRank.centralCoverFour_D4Two q hv hp hf
  obtain ⟨T⟩ : Nonempty (Sylow 3 K) := inferInstance
  exact (ChevTwoInnerRank.four_le_pRank_sylow_of_centralCoverFour hC e T).trans
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top)

theorem four_le_pRank_of_twistedA_two (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hperf : Group.IsPerfect K) {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hq : q.card = 2) (h3 : 3 ∣ r + 1)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    4 ≤ Open.pRank 3 (⊤ : Subgroup K) := by
  obtain ⟨hp, hf⟩ := primePower_card_two' hq
  have hr := three_le_rank_of_twistedA_two hv hq
  have h := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hp, hf] at h
  have h6 : 6 ≤ r + 1 := by omega
  have hpg : 3 ∣ Nat.gcd (r + 1) (2 ^ 1 + 1) := Nat.dvd_gcd h3 (by norm_num)
  have hS := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.n_sub_two_le_pRank_of_model h
    (Or.inr rfl) (by omega) Nat.prime_three (by norm_num) hpg
  by_cases hZ : 3 ∣ Nat.card (Subgroup.center K)
  · obtain ⟨-, h2⟩ := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.lieCoverRankHighLin_aux hGA
      hperf Nat.prime_three (by norm_num) hZ (by omega) (Or.inl ⟨by decide, h⟩) (Or.inr rfl) hpg
    omega
  · have := CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_not_dvd
      Nat.prime_three hZ
    omega

theorem autThreePowInner_of_lie_two (hGA : GriessAllModelsStatement) {K : Type} [Group K]
    [Finite K] (hperf : Group.IsPerfect K) (hr : Open.pRank 3 (⊤ : Subgroup K) ≤ 3)
    (d : TauCeti.ValidLieTypeIndex) (hd : IsClassicalOrG2Index d.1) (h2 : LieField d.1 = 2)
    (e : K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    AutThreePowInner (K ⧸ Subgroup.center K) := by
  obtain ⟨d1, hv⟩ := d
  cases d1 with
  | A r q => exact autThreePowInner_typeA_two hv h2 e
  | twistedA r q =>
    by_cases h3 : 3 ∣ r + 1
    · have := four_le_pRank_of_twistedA_two hGA hperf hv h2 h3 e
      omega
    · exact autThreePowInner_typeTwistedA_two hv h2 h3 e
  | B r q => exact autThreePowInner_typeB_two hv h2 e
  | C r q => exact False.elim hd
  | D r q =>
    have hr4 : 4 ≤ r :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    rcases Nat.lt_or_ge r 5 with h5 | h5
    · obtain rfl : r = 4 := by omega
      have := four_le_pRank_of_typeD4_two hv h2 e
      omega
    · exact autThreePowInner_typeD_two hv h2 h5 e
  | twistedD r q => exact autThreePowInner_typeTwistedD_two hv h2 e
  | E6 q => exact False.elim hd
  | E7 q => exact False.elim hd
  | E8 q => exact False.elim hd
  | F4 q => exact False.elim hd
  | G2 q =>
    have h3 : 3 ≤ q.card :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have h2' : q.card = 2 := h2
    omega
  | twistedE6 q => exact False.elim hd
  | trialityD4 q => exact False.elim hd
  | suzuki m => exact False.elim hd
  | reeG2 m => exact False.elim hd
  | reeF4 m => exact False.elim hd
  | tits => exact False.elim hd

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.OuterThree
