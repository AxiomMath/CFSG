module

public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalOrder504Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Count
public import Mathlib.Data.Int.Star

public section

namespace CFSG.GroupTheory.SmallFixedTwoGroup

variable {G : Type*} [Group G]

open Subgroup

private theorem false_of_sylow_index_bound_arith (p m : ℕ) (hp : 7 ≤ p) (hm : p + 1 ≤ m)
    (hbound : m * (p - 4) ≤ 4 * (p - 1)) : p = 7 ∧ m = 8 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hq3 : 7 + q - 4 = q + 3 := by omega
  have hq1 : 7 + q - 1 = q + 6 := by omega
  rw [hq3, hq1] at hbound
  have hm' : q + 8 ≤ m := by omega
  have h1 : (q + 8) * (q + 3) ≤ 4 * (q + 6) :=
    (Nat.mul_le_mul_right _ hm').trans hbound
  have hq0 : q = 0 := by nlinarith
  subst hq0
  norm_num at hbound
  omega

theorem false_of_sylow_index_bound [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p)
    (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (hab : ∀ a ∈ (P : Subgroup G), ∀ b ∈ (P : Subgroup G), a * b = b * a)
    (hbound : (centralizer ((P : Subgroup G) : Set G)).index * (p - 4) ≤ 4 * (p - 1)) :
    False := by
  classical
  set C : Subgroup G := centralizer ((P : Subgroup G) : Set G) with hC
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hpG
  have hPcard_ne_one : Nat.card (P : Subgroup G) ≠ 1 := fun h =>
    hPne (Subgroup.card_eq_one.mp h)
  have hPG : Nat.card (P : Subgroup G) ≠ Nat.card G := by
    intro h
    have htop : (P : Subgroup G) = ⊤ := Subgroup.eq_top_of_card_eq (P : Subgroup G) h
    obtain ⟨a, b, hab'⟩ := hnab
    exact hab' (hab a (htop ▸ mem_top a) b (htop ▸ mem_top b))
  have hPnotnormal : ¬ (P : Subgroup G).Normal :=
    CFSG.ComponentClassification.LiteratureLocal.Order504.not_normal_of_card hPcard_ne_one hPG
  have hPC : (P : Subgroup G) ≤ C := by
    intro a ha
    rw [hC, mem_centralizer_iff]
    intro b hb
    exact hab b hb a ha
  have hCne : C ≠ ⊤ := by
    intro hCtop
    apply hPnotnormal
    rw [← normalizer_eq_top_iff]
    have hle : C ≤ normalizer ((P : Subgroup G) : Set G) := by
      rw [hC]; exact centralizer_le_normalizer _
    rw [hCtop] at hle
    exact top_le_iff.mp hle
  have hdvd_fact : Nat.card G ∣ C.index.factorial :=
    CFSG.EvenSporadicStandard.Induction.Balance.card_dvd_factorial_index hCne
  have hpdvd_fact : p ∣ C.index.factorial := hpG.trans hdvd_fact
  have hple_m : p ≤ C.index :=
    (Nat.Prime.dvd_factorial (p := p) (n := C.index) Fact.out).mp hpdvd_fact
  have hm_dvd_Pidx : C.index ∣ (P : Subgroup G).index := Subgroup.index_dvd_of_le hPC
  have hp_not_dvd_m : ¬ p ∣ C.index := fun h => Sylow.not_dvd_index P (h.trans hm_dvd_Pidx)
  have hp1m : p + 1 ≤ C.index := by
    rcases lt_or_eq_of_le hple_m with h | h
    · omega
    · exact absurd h.symm (fun heq => hp_not_dvd_m (heq ▸ dvd_refl p))
  obtain ⟨hp7, hm8⟩ := false_of_sylow_index_bound_arith p C.index hp hp1m hbound
  subst hp7
  set N : Subgroup G := normalizer ((P : Subgroup G) : Set G) with hN
  have hCN : C ≤ N := by
    rw [hC, hN]; exact centralizer_le_normalizer _
  have hNidx8 : N.index = 8 := by
    have hdvd : N.index ∣ C.index := Subgroup.index_dvd_of_le hCN
    rw [hm8] at hdvd
    have hmod : N.index % 7 = 1 := by
      rw [hN, CFSG.ComponentClassification.LiteratureLocal.Order504.index_normalizer_sylow P]
      exact card_sylow_modEq_one 7 G
    have htop : N ≠ ⊤ := by
      rw [hN]
      exact fun h => hPnotnormal (normalizer_eq_top_iff.mp h)
    have hne1 : N.index ≠ 1 := fun h => htop (Subgroup.index_eq_one.mp h)
    set n := N.index with hn
    have hdvd' : n ∣ 8 := by rw [hn]; exact hdvd
    have hmod' : n % 7 = 1 := by rw [hn]; exact hmod
    have hne1' : n ≠ 1 := by rw [hn]; exact hne1
    have hle' : n ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd'
    interval_cases n <;> omega
  have hNC : N ≤ C := by
    rw [← Subgroup.relIndex_eq_one]
    have h := Subgroup.relIndex_mul_index hCN
    rw [hNidx8, hm8] at h
    omega
  refine CFSG.ComponentClassification.LiteratureLocal.Order504.false_of_normalizer_le_centralizer
    P hpG hPG ?_
  rw [hN, hC] at hNC
  exact hNC

end CFSG.GroupTheory.SmallFixedTwoGroup
