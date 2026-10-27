module

public import CFSG.HardMathSupport.Foote.Coordinator.CoverThree.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow
public import CFSG.HardMathSupport.Foote.Proving.CoverThree.PSL3ThreePart
public import CFSG.GH74.GLS.LU.Local.L3Cover
public import CFSG.Quasithin.H13.A5W1620Ta
public import CFSG.LieType.SeitzGeneration.UnitaryHyperEx
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus

public section

namespace CFSG.HardMathSupport.Foote.Coordinator

open CFSG.RankThree.PartTwo.Sec4.Census CFSG.Models CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.Multiplier
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

theorem factorization_three_eq_one_of_dvd {n : ℕ} (hn : n ≠ 0) (h3 : 3 ∣ n) (h9 : ¬ 9 ∣ n) :
    n.factorization 3 = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have h1 : 1 ≤ n.factorization 3 :=
    (hp.pow_dvd_iff_le_factorization hn).1 (by simpa using h3)
  have h2 : ¬ 2 ≤ n.factorization 3 := fun h =>
    h9 (by simpa using (hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem not_nine_dvd_tableOrder_psl_three (p f : ℕ) :
    ¬ 9 ∣ tableOrder .PSL 3 p f := by
  have hexc : (exceptionalOrders .PSL 3 p f).1 * (exceptionalOrders .PSL 3 p f).2 = 1 ∨
      (exceptionalOrders .PSL 3 p f).1 * (exceptionalOrders .PSL 3 p f).2 = 2 ∨
      (exceptionalOrders .PSL 3 p f).1 * (exceptionalOrders .PSL 3 p f).2 = 16 := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : Nat.gcd 3 (p ^ f - 1) = 1 ∨ Nat.gcd 3 (p ^ f - 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left _ _)
  have hgen : genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := rfl
  unfold tableOrder
  rw [hgen]
  simp only
  rcases hg with hg | hg <;> rcases hexc with he | he | he <;> rw [hg, he] <;> omega

theorem not_nine_dvd_tableOrder_psu_three (p f : ℕ) :
    ¬ 9 ∣ tableOrder .PSU 3 p f := by
  have hexc : (exceptionalOrders .PSU 3 p f).1 * (exceptionalOrders .PSU 3 p f).2 = 1 := by
    unfold exceptionalOrders
    split <;> simp_all
  have hg : Nat.gcd 3 (p ^ f + 1) = 1 ∨ Nat.gcd 3 (p ^ f + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left _ _)
  have hgen : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := rfl
  unfold tableOrder
  rw [hgen, hexc]
  simp only
  rcases hg with hg | hg <;> rw [hg] <;> omega

theorem coverThree_center_three (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex) (hd : CoverThreeIndex d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    (Nat.card (Subgroup.center K)).factorization 3 = 1 := by
  obtain ⟨e⟩ := e
  have hq' : CFSG.IsQuasisimple K :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.isQuasisimple_of_open hK
  refine factorization_three_eq_one_of_dvd Nat.card_pos.ne' hz fun h9 => ?_
  rcases hd with ⟨q, hdq, -⟩ | ⟨q, hdq, -⟩
  · obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    exact not_nine_dvd_tableOrder_psl_three _ _
      (h9.trans (card_center_dvd_tableOrder hGA hq' e (lieModel_typeA 2 q hv)))
  · obtain ⟨dd, hv⟩ := d
    simp only at hdq
    subst hdq
    exact not_nine_dvd_tableOrder_psu_three _ _
      (h9.trans (card_center_dvd_tableOrder hGA hq' e (lieModel_of_statedClassicalModel
        (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)))))

theorem padicValNat_card_typeA_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (h3 : 3 ∣ q.card - 1) (h9 : ¬ 9 ∣ q.card - 1) :
    padicValNat 3 (Nat.card (TauCeti.CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) = 2 := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField q.p q.exponent) = q.card := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card _ _ q.exponent_pos.ne',
      TauCeti.PrimePower.card_def]
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.HardMathSupport.Foote.Proving.padicValNat_three_natCard_PSL3_of_three_cover _
    (by rwa [hF]) (by rwa [hF])

theorem padicValNat_card_twistedA_two (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (h3 : 3 ∣ q.card + 1)
    (h9 : ¬ 9 ∣ q.card + 1) :
    padicValNat 3 (Nat.card (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) = 2 := by
  have hq : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ^
      TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.card :=
    CFSG.LieType.SeitzGeneration.card_twistedA 2 q hv
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ with hf
  have hf1 : 1 ≤ f := TauCeti.ValidLieTypeIndex.fieldExponent_pos _
  have hℓp : ℓ.Prime := by
    rw [hℓ]
    exact Fact.out
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hF : Nat.card (GaloisField ℓ (2 * f)) = (ℓ ^ f) ^ 2 := by
    rw [GaloisField.card _ _ (by omega), ← pow_mul, mul_comm]
  have hqc : 1 < ℓ ^ f := by
    rw [hq, TauCeti.PrimePower.card_def]
    exact Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  rw [← hq] at h3 h9
  let eU := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv
  rw [Nat.card_congr eU.toEquiv]
  show padicValNat 3 (Nat.card (StatedProj (StatedSU 3 (ℓ ^ f) (GaloisField ℓ (2 * f))))) = 2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) (GaloisField ℓ (2 * f))).subgroupOf
      (StatedSU 3 (ℓ ^ f) (GaloisField ℓ (2 * f))))
  rw [CFSG.GH74.GLS.LU.Local.card_scalars_statedSU_three hℓp hf1 hF,
    Nat.gcd_eq_left h3, CFSG.Quasithin.H13.A5.card_statedSU_three_of hF] at h1
  have h2 := CFSG.HardMathSupport.Foote.Proving.three_part_SU3_of_three_cover (ℓ ^ f) hqc h3 h9
  rw [h1] at h2
  have hne : Nat.card (StatedProj (StatedSU 3 (ℓ ^ f) (GaloisField ℓ (2 * f)))) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, padicValNat_zero_right] at h2
    exact absurd h2 (by norm_num)
  rw [padicValNat.mul hne (by norm_num), padicValNat_self] at h2
  omega

theorem coverThree_card_three_part (hGA : GriessMultipliersAllModels) {K : Type} [Group K]
    [Finite K] (hK : Open.IsQuasisimple K) (d : TauCeti.ValidLieTypeIndex)
    (hd : CoverThreeIndex d) (h9 : ¬ CoverThreeNine d)
    (e : Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    (Nat.card K).factorization 3 = 3 := by
  have hZ := coverThree_center_three hGA hK d hd e hz
  obtain ⟨e⟩ := e
  have hcard : Nat.card K = Nat.card (K ⧸ Subgroup.center K) * Nat.card (Subgroup.center K) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hQ : (Nat.card (TauCeti.CFSGIndex.lie d).Group).factorization 3 = 2 := by
    rw [Nat.factorization_def _ Nat.prime_three]
    rcases hd with ⟨q, hdq, h3⟩ | ⟨q, hdq, h3⟩
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      exact padicValNat_card_typeA_two q hv h3 fun h => h9 (Or.inl ⟨q, rfl, h⟩)
    · obtain ⟨dd, hv⟩ := d
      simp only at hdq
      subst hdq
      exact padicValNat_card_twistedA_two q hv h3 fun h => h9 (Or.inr ⟨q, rfl, h⟩)
  rw [hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
  simp only [Finsupp.add_apply]
  rw [hZ, Nat.card_congr e.toEquiv, hQ]

end CFSG.HardMathSupport.Foote.Coordinator
