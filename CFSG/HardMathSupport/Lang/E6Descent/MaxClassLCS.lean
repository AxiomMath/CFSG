module

public import CFSG.HardMathSupport.Lang.E6Descent.MaxClassBasic
public import CFSG.Walter.W67.Section5.MaxClass

public section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Walter.W67

universe u

theorem le_center_of_lcs_succ_eq_bot {Q : Type u} [Group Q] {n : ℕ}
    (h : (⊤ : Subgroup Q).lowerCentralSeries (n + 1) = ⊥) :
    (⊤ : Subgroup Q).lowerCentralSeries n ≤ Subgroup.center Q := by
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
  intro x hx
  have := h hx
  rw [Subgroup.mem_centralizer_iff] at this
  rw [Subgroup.mem_center_iff]
  intro g
  exact (this g (Subgroup.mem_top g))

theorem lcs_pred_eq_center {p : ℕ} [hp : Fact p.Prime] {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) {m : ℕ} (hm : 3 ≤ m) (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) :
    (⊤ : Subgroup P).lowerCentralSeries (m - 2) = Subgroup.center P := by
  have hbot := lcs_eq_bot_of_card m P hP hcard (by omega)
  have hle : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≤ Subgroup.center P :=
    le_center_of_lcs_succ_eq_bot (by rwa [show m - 2 + 1 = m - 1 by omega])
  have hZ := card_center_of_maxClass hP hm hcard hne
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hZ]
  have hd : Nat.card ((⊤ : Subgroup P).lowerCentralSeries (m - 2)) ∣ p := by
    rw [← hZ]; exact Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp.out).mp hd with h1 | h1
  · exfalso; apply hne
    rwa [Subgroup.card_eq_one] at h1
  · rw [h1]

theorem card_lcs_of_maxClass {p : ℕ} [hp : Fact p.Prime] :
    ∀ m : ℕ, ∀ (P : Type u) [Group P] [Finite P], IsPGroup p P → Nat.card P = p ^ m →
      (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥ → 3 ≤ m →
      ∀ j, 1 ≤ j → j ≤ m - 1 →
        Nat.card ((⊤ : Subgroup P).lowerCentralSeries j) = p ^ (m - 1 - j) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro P _ _ hP hcard hne hm j hj hjm
  have hbot := lcs_eq_bot_of_card m P hP hcard (by omega)
  have hZ := card_center_of_maxClass hP hm hcard hne
  have hcen := lcs_pred_eq_center hP hm hcard hne
  rcases hjm.eq_or_lt with hjeq | hjlt
  · subst hjeq
    rw [hbot]; simp
  have hjm2 : j ≤ m - 2 := by omega
  rcases (show m = 3 ∨ 4 ≤ m by omega) with h3 | h4
  · subst h3
    have : j = 1 := by omega
    subst this
    rw [show (3 : ℕ) - 2 = 1 by norm_num] at hcen
    rw [hcen, hZ]; simp
  · have hmax : IsMaximalClass p P := ⟨m, by omega, hcard, hne⟩
    have hmaxQ := isMaximalClass_quotient_center hP hmax (by
      rw [hcard]; exact Nat.pow_le_pow_right hp.out.pos (by omega))
    obtain ⟨m', hm'2, hm'card, hm'ne⟩ := hmaxQ
    have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
    have hQ : Nat.card (P ⧸ Subgroup.center P) = p ^ (m - 1) := by
      have : p ^ m = p ^ (m - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [hZ, hcard, this] at hmul
      exact (Nat.eq_of_mul_eq_mul_right hp.out.pos hmul).symm
    have hm'eq : m' = m - 1 := by
      rw [hQ] at hm'card
      exact (Nat.pow_right_injective hp.out.two_le hm'card).symm
    subst hm'eq
    have hQp := hP.to_quotient (Subgroup.center P)
    have ihQ := ih (m - 1) (by omega) (P ⧸ Subgroup.center P) hQp hQ hm'ne (by omega) j hj
      (by omega)
    have hmap := Subgroup.map_lowerCentralSeries (⊤ : Subgroup P) (QuotientGroup.mk' (Subgroup.center P)) j
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hmap
    have hker : (QuotientGroup.mk' (Subgroup.center P)).ker ≤
        (⊤ : Subgroup P).lowerCentralSeries j := by
      rw [QuotientGroup.ker_mk', ← hcen]
      exact Subgroup.lowerCentralSeries_antitone _ hjm2
    have hcomap := Subgroup.comap_map_eq_self hker
    have hcc := MaxClass.card_comap_mk
      (((⊤ : Subgroup P).lowerCentralSeries j).map (QuotientGroup.mk' (Subgroup.center P)))
    rw [hcomap, hZ, hmap, ihQ] at hcc
    rw [hcc, ← pow_succ]
    congr 1
    omega

end CFSG.HardMathSupport.Lang.E6Descent
