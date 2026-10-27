module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.CentralCover.FourGroupWitness

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open (griessHopfMultiplier GriessAllModelsStatement)
open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank CFSG.RankThree.CentralCover

theorem cov_three_dvd_table_L3 (p f : ℕ)
    (h : 3 ∣ Nat.card (generic .PSL 3 p f × exceptional .PSL 3 p f)) : 3 ∣ p ^ f - 1 := by
  have hg : genericOrders .PSL 3 p f = (Nat.gcd 3 (p ^ f - 1), 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSL 3 p f =
      (if p = 2 ∧ f = 1 then (2, 1) else if p = 2 ∧ f = 2 then (4, 4) else (1, 1)) := by
    unfold exceptionalOrders
    split_ifs <;> simp_all
  have hgpos : Nat.gcd 3 (p ^ f - 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hexc : (exceptionalOrders .PSL 3 p f).1 ≠ 0 ∧ (exceptionalOrders .PSL 3 p f).2 ≠ 0 := by
    rw [he]
    split_ifs <;> simp
  have hc := lbi_card_gen_exc .PSL 3 p f (by rw [hg]; exact hgpos) (by rw [hg]; simp) hexc.1 hexc.2
  rw [hc, hg] at h
  simp only [mul_one] at h
  have hE : Nat.Coprime 3 ((exceptionalOrders .PSL 3 p f).1 * (exceptionalOrders .PSL 3 p f).2) := by
    rw [he]
    split_ifs <;> norm_num
  exact (Nat.Coprime.dvd_of_dvd_mul_right hE h).trans (Nat.gcd_dvd_right _ _)

theorem cov_three_dvd_table_U3 (p f : ℕ)
    (h : 3 ∣ Nat.card (generic .PSU 3 p f × exceptional .PSU 3 p f)) : 3 ∣ p ^ f + 1 := by
  have hg : genericOrders .PSU 3 p f = (Nat.gcd 3 (p ^ f + 1), 1) := by simp [genericOrders]
  have he : exceptionalOrders .PSU 3 p f = (1, 1) := by simp [exceptionalOrders]
  have hgpos : Nat.gcd 3 (p ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hc := lbi_card_gen_exc .PSU 3 p f (by rw [hg]; exact hgpos) (by rw [hg]; simp)
    (by rw [he]; simp) (by rw [he]; simp)
  rw [hc, hg, he] at h
  simp only [mul_one] at h
  exact h.trans (Nat.gcd_dvd_right _ _)

theorem cov_three_dvd_card {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (h3 : IsPGroup 3 (Subgroup.center Y)) (hZ : Subgroup.center Y ≠ ⊥) {A : Type} [Group A]
    [Finite A] (eH : griessHopfMultiplier (Y ⧸ Subgroup.center Y) ≃* A) : 3 ∣ Nat.card A := by
  have hdvd := lbi_card_ker_dvd (QuotientGroup.mk' (Subgroup.center Y))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hq.1 eH
  rw [QuotientGroup.ker_mk'] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h3
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hZ
    rw [pow_zero, Subgroup.card_eq_one] at hk
    simpa using hk
  rw [hk] at hdvd
  exact (dvd_pow_self 3 hk0).trans hdvd

theorem cov_mod_three_L3 (hG : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (h3 : IsPGroup 3 (Subgroup.center Y))
    (hZ : Subgroup.center Y ≠ ⊥) {K : Type} [Field K] [Finite K]
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSL 3 K)) : Nat.card K % 3 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hn⟩ := FiniteField.card' K
  have hadm : StatedLieAdmissible .PSL 3 p n := ⟨hp, n.pos, by norm_num, by simp, by simp⟩
  have hLie : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSL 3 p n :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, by rw [Nat.card_eq_fintype_card, hn],
      ⟨e⟩⟩⟩
  obtain ⟨-, ⟨eH⟩⟩ := hG _ .PSL 3 p n hLie
  obtain ⟨hfin, -⟩ := lbi_card_table_L3 p n
  have : Finite (CFSG.Blueprint.Multiplier.generic .PSL 3 p n ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 3 p n) := hfin
  have hd := cov_three_dvd_table_L3 p n (cov_three_dvd_card hq h3 hZ eH)
  have hcard : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hpos : 0 < p ^ (n : ℕ) := pow_pos hp.pos _
  rw [hcard]
  omega

theorem cov_mod_three_U3 (hG : GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.Open.IsQuasisimple Y) (h3 : IsPGroup 3 (Subgroup.center Y))
    (hZ : Subgroup.center Y ≠ ⊥) {K : Type} [Field K] [Finite K] {p m : ℕ}
    (hadm : StatedLieAdmissible .PSU 3 p m) (hKq : Nat.card K = (p ^ m) ^ 2)
    (e : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 3 (p ^ m) K)) : (p ^ m) % 3 = 2 := by
  have hLie : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) .PSU 3 p m :=
    ⟨hadm, Or.inl ⟨hadm, K, inferInstance, inferInstance, hKq, ⟨e⟩⟩⟩
  obtain ⟨-, ⟨eH⟩⟩ := hG _ .PSU 3 p m hLie
  obtain ⟨hfin, -⟩ := lbi_card_table_U3 p m
  have : Finite (CFSG.Blueprint.Multiplier.generic .PSU 3 p m ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 3 p m) := hfin
  have hd := cov_three_dvd_table_U3 p m (cov_three_dvd_card hq h3 hZ eH)
  omega

end CFSG.HardMathSupport.Solomon.Coordinator
