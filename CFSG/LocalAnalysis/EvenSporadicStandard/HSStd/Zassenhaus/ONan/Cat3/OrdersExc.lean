module

public import CFSG.HardMathSupport.Malle.E27Lie.Outer.Arith27
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ExcSmall

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.EvenSmallLie.CatalogOrders

theorem false_of_twentySeven_dvd {L : Type*} [Group L] [Finite L]
    (h3 : (Nat.card L).factorization 3 = 2) (h : 27 ∣ Nat.card L) : False := by
  have h' : 3 ^ 3 ∣ Nat.card L := by simpa using h
  have hle : 3 ≤ (Nat.card L).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (Nat.card_pos).ne').mp h'
  omega

private theorem twentySeven_dvd_lieOrd_of_q_three {t : StatedLieTag} (hmin : lieMin t ≤ 0)
    (he : 3 ≤ lieExp t 0) {f : ℕ} (hf : 1 ≤ f) : 27 ∣ lieOrd t 0 (3 ^ f) := by
  have hdvd := pow_lieExp_dvd hmin (3 ^ f)
  have h27 : 27 ∣ (3 ^ f) ^ lieExp t 0 := by
    have h : 3 ≤ f * lieExp t 0 := by nlinarith
    rw [← pow_mul, show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact pow_dvd_pow 3 h
  exact h27.trans hdvd

private theorem twentySeven_dvd_lieOrd_chevalley_charThree {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {f : ℕ} (hf : 1 ≤ f) :
    27 ∣ lieOrd t 0 (3 ^ f) := by
  have hspec : lieMin t ≤ 0 ∧ 3 ≤ lieExp t 0 := by
    simp only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact twentySeven_dvd_lieOrd_of_q_three hspec.1 hspec.2 hf

private theorem twentySeven_dvd_lieOrd_chevalley_ne_three {t : StatedLieTag}
    (ht : t ∈ chevalleyExceptionalTags) {q : ℕ} (hq3 : ¬ 3 ∣ q) (hq1 : 1 ≤ q) :
    27 ∣ lieOrd t 0 q := by
  have ht' : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 := by
    simpa only [chevalleyExceptionalTags, Finset.mem_insert, Finset.mem_singleton] using ht
  rcases ht' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show 27 ∣ ordG2 q
    exact CFSG.HardMathSupport.Malle.E27Lie.twentySeven_dvd_ordG2 q hq1
  · show 27 ∣ ordF4 q
    exact (by norm_num : (27 : ℕ) ∣ 3 ^ 5).trans
      (CFSG.ComponentClassification.CatFC.KGHS3.three_pow_five_dvd_ordF4 hq3)
  · show 27 ∣ ordE6 q
    exact (by norm_num : (27 : ℕ) ∣ 3 ^ 5).trans
      (CFSG.ComponentClassification.CatFC.KGHS3.three_pow_five_dvd_ordE6 hq3)
  · show 27 ∣ ordE7 q
    exact (by norm_num : (27 : ℕ) ∣ 3 ^ 5).trans
      (CFSG.ComponentClassification.CatFC.KGHS3.three_pow_five_dvd_ordE7 hq3)
  · show 27 ∣ ordE8 q
    exact (by norm_num : (27 : ℕ) ∣ 3 ^ 5).trans
      (CFSG.ComponentClassification.CatFC.KGHS3.three_pow_five_dvd_ordE8 hq3)
  · show 27 ∣ ordTwistedE6 q
    exact (by norm_num : (27 : ℕ) ∣ 3 ^ 5).trans
      (CFSG.ComponentClassification.CatFC.KGHS3.three_pow_five_dvd_ordTwistedE6 hq3)
  · show 27 ∣ ordTrialityD4 q
    have h9 : 9 ∣ q ^ 6 - 1 := CFSG.ComponentClassification.CatFC.KGHS3.rest_nine_dvd_six hq3
    have h3 : 3 ∣ q ^ 2 - 1 :=
      CFSG.ComponentClassification.CatFC.KGHS3.rest_three_dvd_sq_sub_one hq3
    have h27 : 27 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) :=
      (by norm_num : (27 : ℕ) ∣ 9 * 3).trans (mul_dvd_mul h9 h3)
    have hdvd : (q ^ 6 - 1) * (q ^ 2 - 1) ∣ ordTrialityD4 q := by
      unfold ordTrialityD4
      rw [mul_assoc]
      exact dvd_mul_of_dvd_right (dvd_refl _) _
    exact h27.trans hdvd

theorem false_of_exceptionalRep
    {L : Type} [Group L] [Finite L]
    (h : ExceptionalRep L) (h3 : (Nat.card L).factorization 3 = 2) : False := by
  rcases h with ⟨t, p, f, ht, hM⟩ | ⟨t, p, f, ht, hM⟩ | ⟨p, f, hM⟩
  ·
    have hp : p.Prime := hM.1.1
    have hf : 1 ≤ f := hM.1.2.1
    by_cases hp3 : p = 3
    · subst hp3
      have hcard : Nat.card L = lieOrd t 0 (3 ^ f) := card_eq_lieOrd_of_exceptional hM
      have h27 : 27 ∣ Nat.card L := by
        rw [hcard]
        exact twentySeven_dvd_lieOrd_chevalley_charThree ht hf
      exact false_of_twentySeven_dvd h3 h27
    · have hcard : Nat.card L = lieOrd t 0 (p ^ f) := card_eq_lieOrd_of_exceptional hM
      have hq3 : ¬ 3 ∣ p ^ f := fun hdvd =>
        hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
          (Nat.prime_three.dvd_of_dvd_pow hdvd)).symm
      have hq1 : 1 ≤ p ^ f := Nat.one_le_pow f p hp.pos
      have h27 : 27 ∣ Nat.card L := by
        rw [hcard]
        exact twentySeven_dvd_lieOrd_chevalley_ne_three ht hq3 hq1
      exact false_of_twentySeven_dvd h3 h27
  ·
    have ht' : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      simpa only [reeTitsTags, Finset.mem_insert, Finset.mem_singleton] using ht
    rcases ht' with rfl | rfl | rfl
    ·
      obtain ⟨hp, ⟨a, ha, hf⟩, hcard⟩ := card_eq_lieOrd_of_ree hM
      subst hp
      have hf1 : 1 ≤ f := by omega
      have h27 : 27 ∣ Nat.card L := by
        rw [hcard]
        exact twentySeven_dvd_lieOrd_of_q_three (le_refl 0) (by decide) hf1
      exact false_of_twentySeven_dvd h3 h27
    ·
      obtain ⟨-, -, -, hp2, hodd, -⟩ := hM.1
      subst hp2
      have hcard : Nat.card L = ordTwistedF4 (2 ^ f) :=
        CFSG.ComponentClassification.CatLeafProof.card_of_reeTitsModel_twistedF4 hM
      have hqmod : (2 ^ f) % 3 = 2 := by
        obtain ⟨k, rfl⟩ := hodd
        rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      have h27 : 27 ∣ Nat.card L := by
        rw [hcard]
        simpa only [ordTwistedF4] using
          CFSG.HardMathSupport.Malle.E27Lie.twentySeven_dvd_numTwistedF4 (2 ^ f) hqmod
      exact false_of_twentySeven_dvd h3 h27
    ·
      have h27 : 27 ∣ Nat.card L := dvd_card_of_reeTitsModel_Tits hM (by decide) (by norm_num)
      exact false_of_twentySeven_dvd h3 h27
  ·
    obtain ⟨hp, ⟨a, ha, hf⟩, hcard⟩ := card_eq_lieOrd_of_suzuki hM
    subst hp
    have hcard' : Nat.card L = ordSuzuki (2 ^ f) := hcard
    have h3dvd : 3 ∣ Nat.card L := by
      have h : 3 ^ 1 ∣ Nat.card L :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (Nat.card_pos).ne').mpr
          (by omega)
      simpa using h
    have : 3 ∣ ordSuzuki (2 ^ f) := by rwa [← hcard']
    exact CFSG.ComponentClassification.CatFC.KGHS3.three_not_dvd_ordSuzuki ⟨a, hf⟩ this

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3
