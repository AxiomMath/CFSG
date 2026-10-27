module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoRest
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeArith
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeExc
import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterTwisted
import CFSG.RankThree.PartTwo.Census.Suzuki
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank
public import CFSG.StronglyEmbedded.Catalog.Suzuki

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)

theorem I294Cross.false_of_nonabelian_sylow_rank_three {L : Type} [Group L] [Finite L]
    (hS : ∃ S : Sylow 3 L, ¬ IsMulCommutative (S : Subgroup L))
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3) (h81 : ¬ 3 ^ 4 ∣ Nat.card L) : False := by
  obtain ⟨S, hS⟩ := hS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup L)
  rw [hr] at hEc
  have hEp : IsPGroup 3 E := IsPGroup.of_card hEc
  obtain ⟨T, hET⟩ := hEp.exists_le_sylow
  obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
  have hdvd : Nat.card (T : Subgroup L) ∣ Nat.card L := Subgroup.card_subgroup_dvd_card _
  have hk3 : k ≤ 3 := by
    by_contra h
    exact h81 ((pow_dvd_pow 3 (by omega : 4 ≤ k)).trans (hk ▸ hdvd))
  have hle : Nat.card E ≤ Nat.card (T : Subgroup L) := Subgroup.card_le_of_le hET
  rw [hEc, hk] at hle
  have hk3' : k = 3 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
    omega
  have hEeq : E = (T : Subgroup L) :=
    Subgroup.eq_of_le_of_card_ge hET (by rw [hEc, hk, hk3'])
  have hTc : IsMulCommutative (T : Subgroup L) := by
    rw [← hEeq]; exact hE.1
  exact hS ⟨⟨fun a b => (Sylow.equiv S T).injective (by
    rw [map_mul, map_mul]; exact hTc.is_comm.comm _ _)⟩⟩

theorem I294Cross.three_pow_five_dvd_ordTwistedF4 {q : ℕ} (hq2 : 2 ≤ q) (hq : q % 3 = 2)
    (h : 3 ^ 4 ∣ ordTwistedF4 q) : 3 ^ 5 ∣ ordTwistedF4 q := by
  rw [CFSG.RankThree.PartOne.S12K.ordTwistedF4_eq_factored hq2] at h ⊢
  obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
  have hd : (3 * k + 2) ^ 2 - (3 * k + 2) + 1 = 3 * (3 * k ^ 2 + 3 * k + 1) := by
    have : (3 * k + 2) ^ 2 = 9 * k ^ 2 + 12 * k + 4 := by ring
    omega
  have hg : ((3 * k + 2) ^ 4 - (3 * k + 2) ^ 2 + 1) % 3 = 1 := by
    have h2 : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring
    have h4 : (3 * k + 2) ^ 4 = ((3 * k + 2) ^ 2) ^ 2 := by ring
    rw [h4, h2]
    generalize 3 * k ^ 2 + 4 * k + 1 = s
    have : (3 * s + 1) ^ 2 = 3 * (3 * s ^ 2 + 2 * s) + 1 := by ring
    omega
  set g := (3 * k + 2) ^ 4 - (3 * k + 2) ^ 2 + 1 with hgdef
  have hN : (3 * k + 2) ^ 12 * (3 * k + 2 - 1) ^ 2 * (3 * k + 2 + 1) ^ 2 *
        ((3 * k + 2) ^ 2 + 1) ^ 2 * ((3 * k + 2) ^ 2 - (3 * k + 2) + 1) * g =
      27 * ((k + 1) ^ 2 * ((3 * k + 2) ^ 12 * (3 * k + 1) ^ 2 * ((3 * k + 2) ^ 2 + 1) ^ 2 *
        (3 * k ^ 2 + 3 * k + 1) * g)) := by
    rw [hd, show 3 * k + 2 - 1 = 3 * k + 1 by omega]
    ring
  rw [hN] at h ⊢
  have h3 : 3 ∣ (k + 1) ^ 2 * ((3 * k + 2) ^ 12 * (3 * k + 1) ^ 2 * ((3 * k + 2) ^ 2 + 1) ^ 2 *
      (3 * k ^ 2 + 3 * k + 1) * g) := by
    have : 27 * 3 ∣ 27 * ((k + 1) ^ 2 * ((3 * k + 2) ^ 12 * (3 * k + 1) ^ 2 *
        ((3 * k + 2) ^ 2 + 1) ^ 2 * (3 * k ^ 2 + 3 * k + 1) * g)) := by simpa using h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
  · have hk : 3 ∣ k + 1 := Nat.prime_three.dvd_of_dvd_pow h3
    obtain ⟨t, ht⟩ := hk
    have hk1 : k + 1 = 3 * t := ht
    refine ⟨(t ^ 2 * ((3 * k + 2) ^ 12 * (3 * k + 1) ^ 2 * ((3 * k + 2) ^ 2 + 1) ^ 2 *
      (3 * k ^ 2 + 3 * k + 1) * g)), ?_⟩
    rw [hk1]; ring
  · exfalso
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
    · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
      · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
        · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h3 | h3
          · have := Nat.prime_three.dvd_of_dvd_pow h3; omega
          · have := Nat.prime_three.dvd_of_dvd_pow h3; omega
        · have := Nat.prime_three.dvd_of_dvd_pow h3
          have h2 : (3 * k + 2) ^ 2 = 3 * (3 * k ^ 2 + 4 * k + 1) + 1 := by ring
          omega
      · omega
    · omega

section Families

theorem i294CrossThreeRankThreeOn_excBig :
    I294CrossThreeRankThreeOn I294CrossIsExcBig := by
  intro L _ _ _ _ d hd _ hLe _ _ _ hr _ _
  obtain ⟨e⟩ := hLe
  have := four_le_pRank_three_of_isExcBig d hd e
  omega

theorem i294CrossThreeRankThreeOn_reeG2 : I294CrossThreeRankThreeOn I294CrossIsReeG2 := by
  intro L _ _ _ _ d hd hch
  obtain ⟨i, hv⟩ := d
  cases i with
  | reeG2 m => exact (hch (TauCeti.LieTypeIndex.characteristic_reeG2 m)).elim
  | _ => exact (hd : False).elim

theorem i294CrossThreeRankThreeOn_sz : I294CrossThreeRankThreeOn I294CrossIsSz := by
  intro L _ _ _ _ d hd _ e _ hS _ _ _ _
  obtain ⟨i, hv⟩ := d
  cases i with
  | suzuki m =>
    have hm : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have h3 : ¬ 3 ∣ Nat.card L := by
      obtain ⟨e'⟩ := e
      rw [Nat.card_congr
        (e'.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).toEquiv]
      exact CFSG.RankThree.PartTwo.Census.not_three_dvd_card_suzukiMatrixGroup hm
    obtain ⟨S, hS'⟩ := hS
    have hcard : Nat.card (S : Subgroup L) = 1 := by
      rcases IsPGroup.card_eq_or_dvd S.isPGroup' with h | h
      · exact h
      · exact (h3 (dvd_trans h (Subgroup.card_subgroup_dvd_card _))).elim
    have hsub : Subsingleton (S : Subgroup L) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact (hS' (IsMulCommutative.of_comm fun a b => by rw [Subsingleton.elim a b])).elim
  | _ => exact (hd : False).elim

theorem i294CrossThreeRankThreeOn_g2 :
    I294CrossThreeRankThreeOn I294CrossIsG2 := by
  intro L _ _ _ _ d hG hc3 hLe _ hS h243 hr _ _
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ : ∃ q : TauCeti.PrimePower, idx = .G2 q := by
    cases idx
    case G2 q => exact ⟨q, rfl⟩
    all_goals simp [I294CrossIsG2] at hG
  obtain ⟨eL⟩ := hLe
  have hp3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_G2] using hc3
  have hord : Nat.card L = CFSG.Open.ordG2 q.card := by
    rw [Nat.card_congr eL.toEquiv,
      CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv]
  have hq3 : ¬ 3 ∣ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  exfalso
  by_cases h81 : 3 ^ 4 ∣ Nat.card L
  · rw [hord] at h81
    exact h243 (hord ▸ CrossArith.three_pow_five_dvd_ordG2 hq3 h81)
  · exact I294Cross.false_of_nonabelian_sylow_rank_three hS hr h81

theorem i294CrossThreeRankThreeOn_reeF4 :
    I294CrossThreeRankThreeOn I294CrossIsReeF4 := by
  intro L _ _ _ _ d hd _ he _ hS h243 hr _ _
  obtain ⟨d, hv⟩ := d
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, d = .reeF4 m := by
    cases d <;> first
      | exact ⟨_, rfl⟩
      | exact False.elim hd
      | simp [I294CrossIsReeF4] at hd
  obtain ⟨e⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_twistedF4_of_index m hv e
  have hord : Nat.card L = CFSG.Open.ordTwistedF4 (2 ^ (2 * m + 1)) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 hR
  have hmod : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq2 : 2 ≤ 2 ^ (2 * m + 1) := Nat.le_self_pow (by omega) 2
  exfalso
  by_cases h81 : 3 ^ 4 ∣ Nat.card L
  · rw [hord] at h81
    exact h243 (hord ▸ I294Cross.three_pow_five_dvd_ordTwistedF4 hq2 hmod h81)
  · exact I294Cross.false_of_nonabelian_sylow_rank_three hS hr h81

theorem i294CrossThreeRankThreeOn_tits :
    I294CrossThreeRankThreeOn I294CrossIsTits := by
  intro L _ _ _ _ d hd _ he _ hS _ hr _ _
  have hdT : d.1 = .tits := by
    obtain ⟨i, hv⟩ := d
    cases i <;> first | rfl | exact False.elim hd
  obtain ⟨d, hv⟩ := d
  have hd' : d = .tits := hdT
  subst hd'
  obtain ⟨e0⟩ := he
  have hR := CFSG.HardMathSupport.Timmesfeld.DefChar.lot_reeTitsModel_tits_of_index hv e0
  obtain ⟨e'⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv L 2 1 hR
  have hord : Nat.card L = 17971200 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Schreier.Tits.card_titsD
  exfalso
  refine I294Cross.false_of_nonabelian_sylow_rank_three hS hr ?_
  rw [hord]
  norm_num

theorem i294CrossThreeRankThreeOn_triality :
    I294CrossThreeRankThreeOn I294CrossIsTriality := by
  intro L _ _ _ _ d hd hc3 hLe _ _ _ hr _ _
  exfalso
  obtain ⟨idx, hv⟩ := d
  obtain ⟨q, rfl⟩ : ∃ q : TauCeti.PrimePower, idx = .trialityD4 q := by
    cases idx
    case trialityD4 q => exact ⟨q, rfl⟩
    all_goals simp [I294CrossIsTriality] at hd
  obtain ⟨e⟩ := hLe
  have hq3 : q.p ≠ 3 := by simpa [TauCeti.LieTypeIndex.characteristic_trialityD4] using hc3
  have hR : CFSG.LieType.SeitzGeneration.RankLE2 3 L :=
    CFSG.LieType.SeitzGeneration.RankLE2.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Timmesfeld.CrossChar.rankLE2_three_cat_trialityD4 q hv hq3)
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) (⊤ : Subgroup L)
  rw [hr] at hEc
  have := hR E hE
  rw [hEc] at this
  norm_num at this

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
