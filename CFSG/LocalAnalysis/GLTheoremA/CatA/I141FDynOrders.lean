module

public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F.Ord

open CFSG.Open CFSG.Blueprint CFSG.Yardstones.Md0ec50421ce4 CFSG.SeitzReduction.F4Pilot
open CFSG.Timmesfeld.Orders CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.GLTheoremA.CanonTriL
open CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

theorem mul_half_mul_succ_eq_five {n f : ℕ} (hn : 2 ≤ n) (hf : 1 ≤ f)
    (h : f * ((n - 1) * ((n - 1) + 1) / 2) = 5) : n = 2 ∧ f = 5 := by
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h
  set m : ℕ := (n - 1) * n / 2 with hm
  have hdvd : m ∣ 5 := ⟨f, by rw [mul_comm]; exact h.symm⟩
  rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with hm1 | hm5
  · have hn2 : n = 2 := by
      by_contra hne
      have h3 : 3 ≤ n := by omega
      have h3m : 3 ≤ m := by
        rw [hm, Nat.le_div_iff_mul_le (by norm_num)]
        have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        nlinarith
      omega
    subst hn2
    rw [hm1, mul_one] at h
    exact ⟨rfl, h⟩
  · exfalso
    have hle : n - 1 ≤ m := by
      rw [hm, Nat.le_div_iff_mul_le (by norm_num)]
      have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
      nlinarith
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> norm_num [hm] at hm5

theorem evenLieOrder_ne_6048_linear {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) (ht : t = .PSL ∨ t = .PSU) :
    evenLieOrder t n f ≠ 6048 := by
  have hf : 1 ≤ f := hadm.2.1
  have h189 : Odd 189 := by decide
  intro h
  rw [show (6048 : ℕ) = 2 ^ 5 * 189 by norm_num] at h
  rcases ht with rfl | rfl
  · have hn : 2 ≤ n := hadm.2.2.1
    by_cases h5 : f * ((n - 1) * ((n - 1) + 1) / 2) = 5
    · obtain ⟨rfl, rfl⟩ := mul_half_mul_succ_eq_five hn hf h5
      unfold evenLieOrder at h
      norm_num [CFSG.Open.ordA] at h
    · exact (profile_ordA (n := n - 1) (by omega) hf).ne_of_ne h189 h5 h
  · have hn : 3 ≤ n := hadm.2.2.1
    by_cases h5 : f * ((n - 1) * ((n - 1) + 1) / 2) = 5
    · obtain ⟨hn2, -⟩ := mul_half_mul_succ_eq_five (by omega : 2 ≤ n) hf h5
      omega
    · exact (profile_ordTwistedA (n := n - 1) (by omega) hf).ne_of_ne h189 h5 h

theorem evenLieOrder_ne_6048_classical {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f)
    (ht : t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    evenLieOrder t n f ≠ 6048 := by
  have hf : 1 ≤ f := hadm.2.1
  have h189 : Odd 189 := by decide
  intro h
  rw [show (6048 : ℕ) = 2 ^ 5 * 189 by norm_num] at h
  rcases ht with rfl | rfl | rfl | rfl
  · have hn : 2 ≤ n := hadm.2.2.1
    have hN : f * (n * n) ≠ 5 := by
      intro h5
      have hd : n * n ∣ 5 := ⟨f, by rw [mul_comm]; exact h5.symm⟩
      rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h5'
      · nlinarith
      · have hle : n ≤ 5 := Nat.le_of_dvd (by norm_num) ⟨n, h5'.symm⟩
        interval_cases n <;> norm_num at h5'
    exact (profile_ordBC (n := n) hf).ne_of_ne h189 hN h
  · exact absurd rfl hadm.2.2.2
  · have hn : 4 ≤ n := hadm.2.2
    have hN : f * (n * (n - 1)) ≠ 5 := by
      intro h5
      have hd : n * (n - 1) ∣ 5 := ⟨f, by rw [mul_comm]; exact h5.symm⟩
      rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h5'
      · have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        nlinarith
      · have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        nlinarith
    exact (profile_ordD (by omega) hf).ne_of_ne h189 hN h
  · have hn : 4 ≤ n := hadm.2.2
    have hN : f * (n * (n - 1)) ≠ 5 := by
      intro h5
      have hd : n * (n - 1) ∣ 5 := ⟨f, by rw [mul_comm]; exact h5.symm⟩
      rcases (Nat.dvd_prime Nat.prime_five).1 hd with h1 | h5'
      · have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        nlinarith
      · have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
        nlinarith
    exact (profile_ordTwistedD (by omega) hf).ne_of_ne h189 hN h

theorem evenLieOrder_ne_6048_exceptional {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f)
    (ht : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
      t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits) :
    evenLieOrder t n f ≠ 6048 := by
  have hf : 1 ≤ f := hadm.2.1
  have h189 : Odd 189 := by decide
  intro h
  rw [show (6048 : ℕ) = 2 ^ 5 * 189 by norm_num] at h
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hN : f * 6 ≠ 5 := by omega
    exact (profile_ordG2 hf).ne_of_ne h189 hN h
  · have hN : f * 24 ≠ 5 := by omega
    exact (profile_ordF4 hf).ne_of_ne h189 hN h
  · have hN : f * 36 ≠ 5 := by omega
    exact (profile_ordE6 hf).ne_of_ne h189 hN h
  · have hN : f * 63 ≠ 5 := by omega
    exact (profile_ordE7 hf).ne_of_ne h189 hN h
  · have hN : f * 120 ≠ 5 := by omega
    exact (profile_ordE8 hf).ne_of_ne h189 hN h
  · have hN : f * 36 ≠ 5 := by omega
    exact (profile_ordTwistedE6 hf).ne_of_ne h189 hN h
  · have hN : f * 12 ≠ 5 := by omega
    exact (profile_ordTrialityD4 hf).ne_of_ne h189 hN h
  · have hN : f * 2 ≠ 5 := by omega
    exact (profile_ordSuzuki hf).ne_of_ne h189 hN h
  · exact absurd hadm.2.2.2.1 (by norm_num)
  · have hN : f * 12 ≠ 5 := by omega
    exact (profile_ordTwistedF4 hf).ne_of_ne h189 hN h
  · unfold evenLieOrder at h
    rw [ordTits_eq] at h
    norm_num at h

theorem tag_cases (t : StatedLieTag) :
    (t = .PSL ∨ t = .PSU) ∨
      (t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) ∨
      (t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
        t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits) := by
  cases t <;> simp

theorem evenLieOrder_ne_6048 {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 2 f) : evenLieOrder t n f ≠ 6048 := by
  rcases tag_cases t with h | h | h
  · exact evenLieOrder_ne_6048_linear hadm h
  · exact evenLieOrder_ne_6048_classical hadm h
  · exact evenLieOrder_ne_6048_exceptional hadm h

section LieModel


theorem card_ne_6048_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel X t n 2 f) : Nat.card X ≠ 6048 := by
  rw [card_eq_evenLieOrder h]
  exact evenLieOrder_ne_6048 (statedLieAdmissible_of_lieModel h)

theorem card_ne_6048_of_compType {X : Type} [Group X]
    (h : (∃ (t : StatedLieTag) (r e : ℕ), LieModel X t r 2 e) ∨ Nat.card X = 360) :
    Nat.card X ≠ 6048 := by
  rcases h with ⟨t, r, e, hM⟩ | h360
  · exact card_ne_6048_of_lieModel hM
  · omega

end LieModel

section Small


theorem false_of_small {S : Type} [Group S] [Finite S] {labL : GLALabel} {β : MulAut S}
    (hcen : Subgroup.center S = ⊥) (hin : InnDiagKind S labL β) (hβ1 : β ≠ 1)
    (ht : labL.tag = .B2der ∨ labL.tag = .G2der ∨ labL.tag = .twF4der ∨ labL.tag = .twB2)
    {J : Subgroup S} (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β))
    (hJc : Nat.card (↥J ⧸ Subgroup.center ↥J) = 6048) : False := by
  have hS : HasLabel S (· = labL) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hlam : CFSG.Assembly.LargeEvenInLambda2 labL := lambda2_of_hasLabel hS
  have hdvd : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card S :=
    (Subgroup.index_dvd_card _).trans (Subgroup.card_subgroup_dvd_card J)
  rw [hJc] at hdvd
  obtain ⟨t, r, n⟩ := labL
  simp only at ht
  rcases ht with rfl | rfl | rfl | rfl
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have hM := markedModel_of_hasLabel hS
    have h360 := card_of_B2der hM
    rw [Nat.card_congr
      (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).toEquiv] at h360
    rw [h360] at hdvd
    norm_num at hdvd
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have hM := markedModel_of_hasLabel hS
    have h6048 := card_of_G2der hM
    rw [Nat.card_congr
      (CFSG.LocalAnalysis.GLTheoremA.CanonInn.quotCenterEquivOfBot hcen).toEquiv] at h6048
    have hJle : Nat.card (↥J ⧸ Subgroup.center ↥J) ≤ Nat.card ↥J :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have hJfix : Nat.card ↥J ≤ Nat.card (fixSubgroup β) := Subgroup.card_le_of_le hJ.1
    have hlt := card_fixSubgroup_lt hβ1
    omega
  · obtain ⟨-, rfl, rfl⟩ := hlam
    have hc := card_of_label_char_two hcen hS rfl
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
    have h7 : 7 ∣ Nat.card S := (by norm_num : 7 ∣ 6048).trans hdvd
    rw [hc] at h7
    norm_num [CFSG.Open.ordTits] at h7
  · obtain ⟨-, rfl, hodd, -⟩ := hlam
    have hc := card_of_label_char_two hcen hS rfl
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
      CFSG.StandardType.markDeg, CFSG.SeitzReduction.F4Pilot.evenLieOrder] at hc
    have h3 : 3 ∣ Nat.card S := (by norm_num : 3 ∣ 6048).trans hdvd
    rw [hc] at h3
    exact CFSG.LocalAnalysis.EvenBN.GMSK.TypeDet.not_three_dvd_ordSuzuki
      (CFSG.LocalAnalysis.EvenBN.GMSK.TypeDet.two_pow_mod_three_of_odd hodd) h3

end Small

end CFSG.LocalAnalysis.GLTheoremA.I141F.Ord
