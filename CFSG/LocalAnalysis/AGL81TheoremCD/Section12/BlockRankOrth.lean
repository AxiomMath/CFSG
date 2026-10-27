module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20x
public import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.HardMathSupport.Curtis.Coordinator.PLTypeFactsOrth
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankAlt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankArith
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut
import CFSG.LocalAnalysis.AGLEmbedding.BlockTransvectionCyclicCenter

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open
open CFSG.HardMathSupport.Curtis.Coordinator.PLType
open CFSG.LocalAnalysis.RankThreeUC.S15


private theorem four_le_rkOmPlus_three {m : ℕ} (hm : 4 ≤ m) : 4 ≤ rkOmPlus m 2 3 := by
  have heP : eP 2 3 = 2 := by simpa using eP_two_pow_three 1
  have heS : eS 2 3 = 1 := by simpa using eS_two_pow_three 1
  unfold rkOmPlus
  rw [heP, heS, Nat.div_one]
  split_ifs with h
  · have hodd : Odd m := Nat.not_even_iff_odd.mp fun he => h.2 he.two_dvd
    obtain ⟨k, hk⟩ := hodd
    have hdiv : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by norm_num)
    omega
  · omega

private theorem eq_four_of_rkOmMinus_three {m : ℕ} (hm : 4 ≤ m)
    (h : rkOmMinus m 2 3 ≤ 3) : m = 4 := by
  have heP : eP 2 3 = 2 := by simpa using eP_two_pow_three 1
  have heS : eS 2 3 = 1 := by simpa using eS_two_pow_three 1
  unfold rkOmMinus at h
  rw [heP, heS, Nat.div_one] at h
  split_ifs at h <;> omega

private theorem factorization_omegaMinus_eight_le_one {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    (2 ^ 12 * 3 ^ 4 * 5 * 7 * 17).factorization d ≤ 1 := by
  by_contra h
  push Not at h
  have hdvd : d ^ 2 ∣ 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 :=
    (hd.pow_dvd_iff_le_factorization (by norm_num)).mpr h
  have hdvd' : d ∣ 2 ^ 12 * (3 ^ 4 * (5 * (7 * 17))) := by
    have h1 : d ∣ 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 :=
      (dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hdvd
    rwa [show 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 =
      2 ^ 12 * (3 ^ 4 * (5 * (7 * 17))) by ring] at h1
  have hd2 : d ≠ 2 := by omega
  have hd3 : d ≠ 3 := by omega
  have h2 : ¬ d ∣ 2 ^ 12 := fun h => hd2
    ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h))
  have h3 : ¬ d ∣ 3 ^ 4 := fun h => hd3
    ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h))
  have hp : d = 5 ∨ d = 7 ∨ d = 17 := by
    rcases hd.dvd_mul.mp hdvd' with h | h
    · exact absurd h h2
    rcases hd.dvd_mul.mp h with h | h
    · exact absurd h h3
    rcases hd.dvd_mul.mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hd (by norm_num : Nat.Prime 5)).mp h)
    rcases hd.dvd_mul.mp h with h | h
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hd (by norm_num : Nat.Prime 7)).mp h))
    · exact Or.inr (Or.inr
        ((Nat.prime_dvd_prime_iff_eq hd (by norm_num : Nat.Prime 17)).mp h))
  rcases hp with rfl | rfl | rfl <;> exact absurd hdvd (by norm_num)

private theorem factorization_u4_le_one {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    (2 ^ 6 * 3 ^ 4 * 5).factorization d ≤ 1 := by
  by_contra h
  push Not at h
  have hdvd : d ^ 2 ∣ 2 ^ 6 * 3 ^ 4 * 5 :=
    (hd.pow_dvd_iff_le_factorization (by norm_num)).mpr h
  have hdvd' : d ∣ 2 ^ 6 * (3 ^ 4 * 5) := by
    have h1 : d ∣ 2 ^ 6 * 3 ^ 4 * 5 :=
      (dvd_pow_self d (by norm_num : 2 ≠ 0)).trans hdvd
    rwa [show 2 ^ 6 * 3 ^ 4 * 5 = 2 ^ 6 * (3 ^ 4 * 5) by ring] at h1
  have h2 : ¬ d ∣ 2 ^ 6 := fun h => (by omega : d ≠ 2)
    ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow h))
  have h3 : ¬ d ∣ 3 ^ 4 := fun h => (by omega : d ≠ 3)
    ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp (hd.dvd_of_dvd_pow h))
  have hp : d = 5 := by
    rcases hd.dvd_mul.mp hdvd' with h | h
    · exact absurd h h2
    rcases hd.dvd_mul.mp h with h | h
    · exact absurd h h3
    · exact (Nat.prime_dvd_prime_iff_eq hd (by norm_num : Nat.Prime 5)).mp h
  subst d
  exact absurd hdvd (by norm_num)

private theorem not_prime_card_of_isOrthogonalTwo {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.AGLEmbedding.IsOrthogonalTwo Y) : ¬ (Nat.card Y).Prime := by
  rcases hY with ⟨dL, ⟨m, q, hq, hdL⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hcard : Nat.card Y = Nat.card (TauCeti.CFSGIndex.lie dL).Group :=
      Nat.card_congr e.toEquiv
    rcases hdL with hdL | hdL | ⟨-, hdL⟩
    · have hm : 4 ≤ m := four_le_of_valid_D (hdL ▸ dL.2)
      have hf := tauCetiOrthFacts_holds.1 m dL ⟨q, hq, Or.inl hdL⟩
      rw [hcard]
      exact not_prime_of_two_le_factorization (by
        rw [hf.2]
        exact two_le_mul_pred hm)
    · have hm : 4 ≤ m := four_le_of_valid_twistedD (hdL ▸ dL.2)
      have hf := tauCetiOrthFacts_holds.1 m dL ⟨q, hq, Or.inr hdL⟩
      rw [hcard]
      exact not_prime_of_two_le_factorization (by
        rw [hf.2]
        exact two_le_mul_pred hm)
    · have hf := tauCetiOrthFacts_holds.2 dL ⟨q, hq, hdL⟩
      rw [hcard, hf.2]
      norm_num
  · have hcard : Nat.card Y = Nat.card (alternatingGroup (Fin n)) :=
      Nat.card_congr e.toEquiv
    rcases hn with rfl | rfl | rfl
    · rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    · rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    · rw [hcard, nat_card_alternatingGroup, Nat.card_fin]
      norm_num

private theorem quasisimple_center_of_isOrthogonalTwo {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.AGLEmbedding.IsOrthogonalTwo Y) :
    CFSG.Open.IsQuasisimple Y ∧ Subgroup.center Y = ⊥ := by
  have hsimple : IsSimpleGroup Y :=
    CFSG.AGLEmbedding.TransvectionCyclic.isSimpleGroup_of_isOrthogonalTwo hY
  have hnp : ¬ (Nat.card Y).Prime := not_prime_card_of_isOrthogonalTwo hY
  have hnab : ∃ a b : Y, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    let _ : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hab }
    exact hnp (IsSimpleGroup.prime_card (α := Y))
  obtain ⟨hQ, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := Y) hnab
  exact ⟨⟨hQ.1.commutator_eq_top, hQ.2.1⟩, hZ⟩

private theorem pRank_le_one_of_lie_D {Y : Type} [Group Y] [Finite Y]
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower}
    (hq : q.card = 2) (hdL : dL.1 = .D m q) {d : ℕ}
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r (⊤ : Subgroup Y) = mRankChev dL.1 r (Nat.card (Subgroup.center Y))) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) ≤ 1 := by
  have hm : 4 ≤ m := four_le_of_valid_D (hdL ▸ dL.2)
  have hq2 : q.p ^ q.exponent = 2 := by
    simpa [TauCeti.PrimePower.card_def] using hq
  have h3eq : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = rkOmPlus m 2 3 := by
    have := hrank 3 Nat.prime_three (by norm_num)
    simpa [mRankChev, hdL, hq2] using this
  have h4 := four_le_rkOmPlus_three hm
  omega

private theorem pRank_le_one_of_lie_twistedD {Y : Type} [Group Y] [Finite Y]
    {dL : TauCeti.ValidLieTypeIndex} {m : ℕ} {q : TauCeti.PrimePower}
    (hq : q.card = 2) (hdL : dL.1 = .twistedD m q) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    (hrank : ∀ r : ℕ, r.Prime → r ≠ 2 →
      CFSG.Open.pRank r (⊤ : Subgroup Y) = mRankChev dL.1 r (Nat.card (Subgroup.center Y)))
    (e : Y ≃* (TauCeti.CFSGIndex.lie dL).Group) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) ≤ 1 := by
  have hm : 4 ≤ m := four_le_of_valid_twistedD (hdL ▸ dL.2)
  have hq2 : q.p ^ q.exponent = 2 := by
    simpa [TauCeti.PrimePower.card_def] using hq
  have h3eq : CFSG.Open.pRank 3 (⊤ : Subgroup Y) = rkOmMinus m 2 3 := by
    have := hrank 3 Nat.prime_three (by norm_num)
    simpa [mRankChev, hdL, hq2] using this
  have hm4 : m = 4 := eq_four_of_rkOmMinus_three hm (by omega)
  subst m
  have hcard : Nat.card Y = 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 := by
    rw [Nat.card_congr e.toEquiv, card_lie_twistedD_two 4 dL q hq hdL]
    decide +kernel
  have hle := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
    (A := Y) hd
  rw [hcard] at hle
  exact hle.trans (factorization_omegaMinus_eight_le_one hd hd5)

private theorem pRank_le_one_of_lie_twistedA {Y : Type} [Group Y] [Finite Y]
    {dL : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower}
    (hq : q.card = 2) (hdL : dL.1 = .twistedA 3 q) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d)
    (e : Y ≃* (TauCeti.CFSGIndex.lie dL).Group) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) ≤ 1 := by
  have hcard : Nat.card Y = 25920 := by
    rw [Nat.card_congr e.toEquiv, card_lie_twistedA_three_two dL q hq hdL]
  have hle := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_top_le_factorization
    (A := Y) hd
  rw [hcard] at hle
  exact hle.trans (factorization_u4_le_one hd hd5)

private theorem pRank_le_one_of_alt {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 8) (e : Y ≃* alternatingGroup (Fin n))
    (hZ : Subgroup.center Y = ⊥) (hquasi : CFSG.Open.IsQuasisimple Y)
    {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) ≤ 1 := by
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl | rfl <;> norm_num
  have hquot : Nonempty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
  have hrank := lieOddRankAlt_holds Y hquasi n hn5 hquot d hd (by omega)
  rw [hrank]
  have hn8 : n ≤ 8 := by rcases hn with rfl | rfl | rfl <;> norm_num
  have h2d : n < 2 * d := by omega
  have hlt : n / d < 2 := (Nat.div_lt_iff_lt_mul hd.pos).mpr h2d
  omega

theorem pRank_le_one_of_isOrthogonalTwo {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.AGLEmbedding.IsOrthogonalTwo Y)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3) {d : ℕ} (hd : d.Prime) (hd5 : 5 ≤ d) :
    CFSG.Open.pRank d (⊤ : Subgroup Y) ≤ 1 ∧ Subgroup.center Y = ⊥ := by
  obtain ⟨hquasi, hZ⟩ := quasisimple_center_of_isOrthogonalTwo hY
  refine ⟨?_, hZ⟩
  rcases hY with ⟨dL, ⟨m, q, hq, hdL⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hT : LieOddRankChev :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20x_lieOddRankChev
        CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    have hcl : CFSG.AGLEmbedding.IsClassicalOrG2Index dL.1 := by
      rcases hdL with hdL | hdL | ⟨-, hdL⟩
      · simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index, hdL] using
          (primePower_card_two hq).1
      · simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index, hdL] using
          (primePower_card_two hq).1
      · simpa [CFSG.AGLEmbedding.IsClassicalOrG2Index, hdL] using
          (primePower_card_two hq).1
    have hquot : Nonempty ((Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.lie dL).Group) :=
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
    have hrank := hT Y hquasi dL hcl hquot
    rcases hdL with hdL | hdL | ⟨-, hdL⟩
    · exact pRank_le_one_of_lie_D hq hdL h3 hrank
    · exact pRank_le_one_of_lie_twistedD hq hdL hd hd5 h3 hrank e
    · exact pRank_le_one_of_lie_twistedA hq hdL hd hd5 e
  · exact pRank_le_one_of_alt hn e hZ hquasi hd hd5

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
