module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QPerm
public import CFSG.GH74.Generic.BProg.B2.L2Cover
public import CFSG.GH74.Generic.S3.L3Cover
public import CFSG.HardMathSupport.Dickson.I271.Support.AmbL2
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open TauCeti

theorem primePower_eq_of_card_pow {q : TauCeti.PrimePower} {r s : ℕ} (hr : r.Prime) (hs : 0 < s)
    (h : q.card = r ^ s) : q.p = r ∧ q.exponent = s := by
  rw [TauCeti.PrimePower.card_def] at h
  obtain ⟨m, hm⟩ : ∃ m, q.exponent = m + 1 := ⟨q.exponent - 1, by have := q.exponent_pos; omega⟩
  obtain ⟨k, hk⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  rw [hm, hk] at h
  obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj q.prime_p hr h
  exact ⟨h1, by omega⟩

theorem statedClassical_of_lieModel {S : Type} [Group S] {t : StatedLieTag} {n p f : ℕ}
    (hn : n ≠ 0) (h : CFSG.Models.LieModel S t n p f) : StatedClassicalModel S t n p f := by
  rcases h.2 with h' | ⟨h0, -⟩
  · exact h'
  · exact absurd h0 hn

theorem le_sixteen_of_twoRank_le_three {X : Type} [Group X] [Finite X] {r : ℕ} (hr : r ≤ 3)
    (h : twoRank X ≤ r) (E : Subgroup X) (hE : IsElemAbelian 2 E) : Nat.card E ≤ 16 :=
  (card_le_two_pow_of_twoRank_le h hE).trans (by
    calc 2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hr
      _ = 8 := by norm_num
      _ ≤ 16 := by norm_num)

theorem twoRank_lt_six_of_A_one_seven
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J)
    {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.card = 7)
    (e : J ⧸ Subgroup.center J ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) : twoRank J < 6 := by
  have hL := CFSG.Models.lieModel_A 1 q hv e
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_pow (r := 7) (s := 1) (by norm_num) (by norm_num)
    (by rw [hq]; norm_num)
  rw [hp, hf] at hL
  have hS : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 2 7 1 :=
    statedClassical_of_lieModel (by norm_num) hL
  have hsmall := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd
    (G := J ⧸ Subgroup.center J) (p := 7) (f := 1) (by norm_num) (by norm_num) hS
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hS
  have hKc : Nat.card K = 7 := by rw [hK]; norm_num
  have hodd : Odd (Nat.card K) := by rw [hKc]; decide
  have h5 : 5 ≤ Nat.card K := by rw [hKc]; norm_num
  obtain ⟨m, hmodd, hm⟩ := CFSG.GH74.Generic.BProg.B2.L2Cover.card_hopfMultiplier_psl2 (F := K) hodd h5
  let e' : J ⧸ Subgroup.center J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hZ : Nat.card (Subgroup.center J) ∣ 2 * m := by
    have h1 := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hJ
      (MulEquiv.refl (J ⧸ Subgroup.center J))
    have h2 : Nat.card (CFSG.Open.griessHopfMultiplier (J ⧸ Subgroup.center J)) =
        Nat.card (CFSG.Open.griessHopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
      Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e').toEquiv
    have h3 : Nat.card (CFSG.Open.griessHopfMultiplier (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) =
        2 * m := by
      rw [← CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier]
      exact hm
    rw [← h3, ← h2]
    exact h1
  refine twoRank_lt_six_of_center_quotient hJ hmodd hZ (fun F hF => ?_)
  exact le_sixteen_of_twoRank_le_three (r := 2) (by norm_num) hsmall F hF

theorem twoRank_lt_six_of_A_one_eight
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J) (hJq : CFSG.Open.IsQuasisimple J)
    {q : PrimePower} (hv : (LieTypeIndex.A 1 q).Valid) (hq : q.card = 8)
    (e : J ⧸ Subgroup.center J ≃* ValidLieTypeIndex.Group ⟨.A 1 q, hv⟩) : twoRank J < 6 := by
  have hL := CFSG.Models.lieModel_A 1 q hv e
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_pow (r := 2) (s := 3) (by norm_num) (by norm_num)
    (by rw [hq]; norm_num)
  rw [hp, hf] at hL
  have hS : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 2 2 3 :=
    statedClassical_of_lieModel (by norm_num) hL
  have htw := CFSG.GH74.SmallRanks.twoRank_eq_of_statedClassicalModel_PSL_two_two hS
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hS
  have hK8 : Nat.card K = 8 := by rw [hK]; norm_num
  let e' : J ⧸ Subgroup.center J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hcen : Subgroup.center J = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.Amb.l2Eight_center_eq_bot hK8 hJq e'
  have hZ : Nat.card (Subgroup.center J) ∣ 2 * 1 := by
    rw [hcen, Subgroup.card_bot]
    simp
  refine twoRank_lt_six_of_center_quotient hJ odd_one hZ (fun F hF => ?_)
  exact le_sixteen_of_twoRank_le_three (r := 3) (by norm_num) htw.le F hF

theorem lieModel_twistedA_pp {G : Type} [Group G] (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (e : G ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    CFSG.Models.LieModel G .PSU (r + 1) q.p q.exponent := by
  have h := CFSG.Models.lieModel_twistedA r q hv e
  have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  rwa [hc, hf] at h

theorem twoRank_lt_six_of_twistedA_two_three
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    {J : Type} [Group J] [Finite J] (hJ : Group.IsPerfect J)
    {q : PrimePower} (hv : (LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3)
    (e : J ⧸ Subgroup.center J ≃* ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) : twoRank J < 6 := by
  have hL := lieModel_twistedA_pp 2 q hv e
  obtain ⟨hp, hf⟩ := primePower_eq_of_card_pow (r := 3) (s := 1) (by norm_num) (by norm_num)
    (by rw [hq]; norm_num)
  rw [hp, hf] at hL
  have hL' : CFSG.Models.LieModel (J ⧸ Subgroup.center J) .PSU 3 3 1 := hL
  have hS : StatedClassicalModel (J ⧸ Subgroup.center J) .PSU 3 3 1 :=
    statedClassical_of_lieModel (by norm_num) hL'
  have hsmall := CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSU_three_three hS
  have hmul := CFSG.GH74.Generic.S3.card_hopfMultiplier_psu_three hGA hL'
  have hgr : Nat.card (CFSG.Open.griessHopfMultiplier (J ⧸ Subgroup.center J)) = 1 := by
    rw [← CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.card_hopfMultiplier_eq_card_griessHopfMultiplier,
      hmul]
    norm_num
  have hZ : Nat.card (Subgroup.center J) ∣ 2 * 1 := by
    have h1 := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hJ
      (MulEquiv.refl (J ⧸ Subgroup.center J))
    rw [hgr] at h1
    exact h1.trans (by norm_num)
  refine twoRank_lt_six_of_center_quotient hJ odd_one hZ (fun F hF => ?_)
  exact le_sixteen_of_twoRank_le_three (r := 2) (by norm_num) hsmall F hF

end CFSG.LocalAnalysis.GLTheoremA

end
