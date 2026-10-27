module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open scoped commutatorElement

variable {P : Type*} [Group P]

theorem lcs_succ_lt [Group.IsNilpotent P] {k : ℕ} (hk : (⊤ : Subgroup P).lowerCentralSeries k ≠ ⊥) :
    ¬ (⊤ : Subgroup P).lowerCentralSeries k ≤ (⊤ : Subgroup P).lowerCentralSeries (k + 1) := by
  intro hle
  have heq : (⊤ : Subgroup P).lowerCentralSeries (k + 1) = (⊤ : Subgroup P).lowerCentralSeries k :=
    le_antisymm (Subgroup.lowerCentralSeries_antitone _ (Nat.le_succ k)) hle
  have hall : ∀ j, (⊤ : Subgroup P).lowerCentralSeries (k + j) =
      (⊤ : Subgroup P).lowerCentralSeries k := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [← add_assoc, Subgroup.lowerCentralSeries_succ, ih, ← Subgroup.lowerCentralSeries_succ, heq]
  apply hk
  rw [← hall (Group.nilpotencyClass P)]
  have : (⊤ : Subgroup P).lowerCentralSeries (Group.nilpotencyClass P) = ⊥ :=
    Subgroup.lowerCentralSeries_nilpotencyClass
  exact le_bot_iff.1 (this ▸ Subgroup.lowerCentralSeries_antitone _ (Nat.le_add_left _ _))

variable {p : ℕ} [Fact p.Prime] [Finite P]

theorem relIndex_lcs_ge (hPg : IsPGroup p P) {m : ℕ} (hcard : Nat.card P = p ^ m) {k : ℕ}
    (hk : (⊤ : Subgroup P).lowerCentralSeries k ≠ ⊥) :
    p ≤ ((⊤ : Subgroup P).lowerCentralSeries (k + 1)).relIndex
      ((⊤ : Subgroup P).lowerCentralSeries k) := by
  have hnil : Group.IsNilpotent P := hPg.isNilpotent
  set A := (⊤ : Subgroup P).lowerCentralSeries k
  set B := (⊤ : Subgroup P).lowerCentralSeries (k + 1)
  have hBA : B ≤ A := Subgroup.lowerCentralSeries_antitone _ (Nat.le_succ k)
  have hmul : B.relIndex A * Nat.card B = Nat.card A := by
    have := Subgroup.relIndex_mul_card (H := B) (K := A)
    rwa [inf_of_le_left hBA] at this
  have hdvdA : Nat.card A ∣ p ^ m := hcard ▸ Subgroup.card_subgroup_dvd_card A
  have hdvd : B.relIndex A ∣ p ^ m := (Dvd.intro _ hmul).trans hdvdA
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  have hne : B.relIndex A ≠ 1 := fun h1 => lcs_succ_lt hk (Subgroup.relIndex_eq_one.1 h1)
  rcases a with _ | a
  · exact absurd (by simpa using ha) hne
  · rw [ha]; exact Nat.le_self_pow (Nat.succ_ne_zero a) p

omit [Finite P] in
theorem relIndex_mul_card_lcs (k : ℕ) :
    ((⊤ : Subgroup P).lowerCentralSeries (k + 1)).relIndex ((⊤ : Subgroup P).lowerCentralSeries k) *
      Nat.card ((⊤ : Subgroup P).lowerCentralSeries (k + 1)) =
      Nat.card ((⊤ : Subgroup P).lowerCentralSeries k) := by
  have := Subgroup.relIndex_mul_card (H := (⊤ : Subgroup P).lowerCentralSeries (k + 1))
    (K := (⊤ : Subgroup P).lowerCentralSeries k)
  rwa [inf_of_le_left (Subgroup.lowerCentralSeries_antitone _ (Nat.le_succ k))] at this

theorem card_lcs_ge (hPg : IsPGroup p P) {m : ℕ} (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) :
    ∀ d, d ≤ m - 1 → p ^ d ≤ Nat.card ((⊤ : Subgroup P).lowerCentralSeries (m - 1 - d)) := by
  intro d
  induction d with
  | zero => intro _; exact Nat.card_pos
  | succ d ih =>
    intro hd
    have hj : m - 1 - (d + 1) + 1 = m - 1 - d := by omega
    have hk : (⊤ : Subgroup P).lowerCentralSeries (m - 1 - (d + 1)) ≠ ⊥ := fun h0 =>
      hne (le_bot_iff.1 (h0 ▸ Subgroup.lowerCentralSeries_antitone _ (by omega)))
    have h1 := relIndex_lcs_ge hPg hcard hk
    have h2 := relIndex_mul_card_lcs (P := P) (m - 1 - (d + 1))
    rw [hj] at h1 h2
    have h3 := ih (by omega)
    rw [← h2, pow_succ']
    exact Nat.mul_le_mul h1 h3

omit [Finite P] in
theorem lcs_one_le_two_of_index_dvd_prime
    (hdiv : ((⊤ : Subgroup P).lowerCentralSeries 1).index ∣ p) :
    (⊤ : Subgroup P).lowerCentralSeries 1 ≤ (⊤ : Subgroup P).lowerCentralSeries 2 := by
  set N := (⊤ : Subgroup P).lowerCentralSeries 2 with hN
  let π : P →* P ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hc : (⊤ : Subgroup P).lowerCentralSeries 1 ≤ (Subgroup.center (P ⧸ N)).comap π := by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := hπ q
    have hmem : ⁅u, g⁆ ∈ N := by
      rw [hN, Subgroup.lowerCentralSeries_succ]
      exact Subgroup.commutator_mem_commutator hu (Subgroup.mem_top g)
    have h1 : π ⁅u, g⁆ = 1 := (QuotientGroup.eq_one_iff _).2 hmem
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hidx : (Subgroup.center (P ⧸ N)).index ∣ p := by
    rw [← Subgroup.index_comap_of_surjective _ hπ]
    exact (Subgroup.index_dvd_of_le hc).trans hdiv
  have hcyc : IsCyclic ((P ⧸ N) ⧸ Subgroup.center (P ⧸ N)) :=
    isCyclic_of_card_dvd_prime hidx
  have hcomm : IsMulCommutative (P ⧸ N) :=
    (QuotientGroup.mk' (Subgroup.center (P ⧸ N))).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
  have hQ : ∀ a b : P, ⁅a, b⁆ ∈ N := by
    intro a b
    rw [← QuotientGroup.eq_one_iff (N := N)]
    change π ⁅a, b⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _
  rw [Subgroup.top_lowerCentralSeries_one]
  show ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ N
  rw [Subgroup.commutator_le]
  exact fun a _ b _ => hQ a b

theorem two_dvd_index_lcs_one (hPg : IsPGroup p P) {m : ℕ} (hm : 3 ≤ m)
    (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) :
    p ^ 2 ∣ ((⊤ : Subgroup P).lowerCentralSeries 1).index := by
  have hnil : Group.IsNilpotent P := hPg.isNilpotent
  by_contra hnd
  have hdvd : ((⊤ : Subgroup P).lowerCentralSeries 1).index ∣ p ^ m :=
    hcard ▸ Subgroup.index_dvd_card _
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 hdvd
  have ha1 : a ≤ 1 := by
    by_contra h2
    exact hnd (ha ▸ pow_dvd_pow p (by omega))
  have hdiv : ((⊤ : Subgroup P).lowerCentralSeries 1).index ∣ p := by
    rw [ha]; exact (pow_dvd_pow p ha1).trans (by simp)
  have hk : (⊤ : Subgroup P).lowerCentralSeries 1 ≠ ⊥ := fun h0 =>
    hne (le_bot_iff.1 (h0 ▸ Subgroup.lowerCentralSeries_antitone _ (by omega)))
  exact lcs_succ_lt hk (lcs_one_le_two_of_index_dvd_prime hdiv)

theorem index_lcs_ge (hPg : IsPGroup p P) {m : ℕ} (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥)
    (hnc : p ^ 2 ∣ ((⊤ : Subgroup P).lowerCentralSeries 1).index) :
    ∀ k, 1 ≤ k → k ≤ m - 1 → p ^ (k + 1) ≤ ((⊤ : Subgroup P).lowerCentralSeries k).index := by
  intro k hk1
  induction k, hk1 using Nat.le_induction with
  | base =>
    intro _
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hnc
  | succ k hk ih =>
    intro hk'
    have hkb : (⊤ : Subgroup P).lowerCentralSeries k ≠ ⊥ := fun h0 =>
      hne (le_bot_iff.1 (h0 ▸ Subgroup.lowerCentralSeries_antitone _ (by omega)))
    have h1 := relIndex_lcs_ge hPg hcard hkb
    have h2 := Subgroup.relIndex_mul_index
      (Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup P) (Nat.le_succ k))
    rw [← h2, pow_succ]
    calc p ^ (k + 1) * p = p * p ^ (k + 1) := mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul h1 (ih (by omega))

theorem card_lcs_eq (hPg : IsPGroup p P) {m : ℕ} (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥)
    (hnc : p ^ 2 ∣ ((⊤ : Subgroup P).lowerCentralSeries 1).index) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ m - 1) :
    Nat.card ((⊤ : Subgroup P).lowerCentralSeries k) = p ^ (m - 1 - k) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hlo := card_lcs_ge hPg hcard hne (m - 1 - k) (by omega)
  rw [show m - 1 - (m - 1 - k) = k by omega] at hlo
  have hI := index_lcs_ge hPg hcard hne hnc k hk1 hk
  have hmul := Subgroup.card_mul_index ((⊤ : Subgroup P).lowerCentralSeries k)
  rw [hcard] at hmul
  have hup : Nat.card ((⊤ : Subgroup P).lowerCentralSeries k) ≤ p ^ (m - 1 - k) := by
    refine Nat.le_of_mul_le_mul_right (c := p ^ (k + 1)) ?_ (pow_pos hp _)
    calc Nat.card ((⊤ : Subgroup P).lowerCentralSeries k) * p ^ (k + 1)
        ≤ Nat.card ((⊤ : Subgroup P).lowerCentralSeries k) *
          ((⊤ : Subgroup P).lowerCentralSeries k).index := Nat.mul_le_mul_left _ hI
      _ = p ^ m := hmul
      _ = p ^ (m - 1 - k) * p ^ (k + 1) := by rw [← pow_add]; congr 1; omega
  have hge : p ^ (m - 1 - k) ≤ Nat.card ((⊤ : Subgroup P).lowerCentralSeries k) := hlo
  omega

theorem relIndex_lcs_eq (hPg : IsPGroup p P) {m : ℕ} (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥)
    (hnc : p ^ 2 ∣ ((⊤ : Subgroup P).lowerCentralSeries 1).index) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : k ≤ m - 2) :
    ((⊤ : Subgroup P).lowerCentralSeries (k + 1)).relIndex
      ((⊤ : Subgroup P).lowerCentralSeries k) = p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 := card_lcs_eq hPg hcard hne hnc hk1 (by omega)
  have h2 := card_lcs_eq hPg hcard hne hnc (k := k + 1) (by omega) (by omega)
  have h3 := relIndex_mul_card_lcs (P := P) k
  rw [h1, h2, show m - 1 - k = (m - 1 - (k + 1)) + 1 by omega, pow_succ] at h3
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp _) (by rw [mul_comm] at h3; exact h3)

theorem lcs_eq_bot (hPg : IsPGroup p P) {m : ℕ} (hm : 3 ≤ m) (hcard : Nat.card P = p ^ m)
    (hne : (⊤ : Subgroup P).lowerCentralSeries (m - 2) ≠ ⊥) :
    (⊤ : Subgroup P).lowerCentralSeries (m - 1) = ⊥ := by
  have := card_lcs_eq hPg hcard hne (two_dvd_index_lcs_one hPg hm hcard hne) (k := m - 1)
    (by omega) le_rfl
  rw [Nat.sub_self, pow_zero] at this
  exact Subgroup.card_eq_one.1 this

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms
