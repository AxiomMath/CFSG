module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup

section Pair

variable {N : Type*} [Group N]

theorem pow_eq_one_of_mem_closure_pair {a b : N} {p : ℕ} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : a * b = b * a) : ∀ x ∈ Subgroup.closure ({a, b} : Set N), x ^ p = 1 := by
  have hS : ({a, b} : Set N) ⊆ (Subgroup.centralizer ({a, b} : Set N) : Set N) := by
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hh
    rcases hx with rfl | rfl <;> rcases hh with rfl | rfl
    · rfl
    · exact hab.symm
    · exact hab
    · rfl
  have hcl : Subgroup.closure ({a, b} : Set N) ≤ Subgroup.centralizer ({a, b} : Set N) :=
    (Subgroup.closure_le _).2 hS
  have hcomm : ∀ x ∈ Subgroup.closure ({a, b} : Set N), ∀ y ∈ Subgroup.closure ({a, b} : Set N),
      x * y = y * x := by
    intro x hx y hy
    have hx' := Subgroup.closure_le_centralizer_centralizer ({a, b} : Set N) hx
    exact (Subgroup.mem_centralizer_iff.1 hx' y (hcl hy)).symm
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> assumption
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

variable [Finite N]

omit [Finite N] in
theorem isPGroup_closure_pair {a b : N} {p : ℕ} [Fact p.Prime] (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : a * b = b * a) : IsPGroup p (Subgroup.closure ({a, b} : Set N)) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one
    (pow_eq_one_of_mem_closure_pair ha hb hab x hx)
  rw [Subgroup.orderOf_mk]
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h | h
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

theorem sq_dvd_card_closure_pair {a b : N} {p : ℕ} (hp : p.Prime) (ha : a ^ p = 1) (hb : b ^ p = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ∉ Subgroup.zpowers a) :
    p ^ 2 ∣ Nat.card (Subgroup.closure ({a, b} : Set N)) := by
  have := Fact.mk hp
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (isPGroup_closure_pair ha hb hab)
  have ha_mem : a ∈ Subgroup.closure ({a, b} : Set N) := Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure ({a, b} : Set N) := Subgroup.subset_closure (by simp)
  have hA : Subgroup.zpowers a ≤ Subgroup.closure ({a, b} : Set N) :=
    (Subgroup.zpowers_le).2 ha_mem
  have hAcard : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha ha1
  by_contra hcon
  have hk1 : k ≤ 1 := by
    by_contra h2
    push Not at h2
    exact hcon (hk ▸ pow_dvd_pow p h2)
  have hle : Nat.card (Subgroup.closure ({a, b} : Set N)) ≤ Nat.card (Subgroup.zpowers a) := by
    rw [hk, hAcard]
    calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
      _ = p := pow_one p
  exact hb1 ((Subgroup.eq_of_le_of_card_ge hA hle) ▸ hb_mem)

theorem triples_false_core {r : ℕ} (hr : r.Prime) {a0 b0 : N} (ha : a0 ^ r = 1) (hb : b0 ^ r = 1)
    (hab : a0 * b0 = b0 * a0) (ha1 : a0 ≠ 1) (hb1 : b0 ∉ Subgroup.zpowers a0)
    (hcube : ¬ r ^ 3 ∣ Nat.card N)
    (hC : ∀ g : N, g * a0 = a0 * g → g * b0 = b0 * g → g ^ (r ^ 2) = 1)
    {s : ℕ} (hs : s.Prime) (hrs : r ≠ s) {a b y : N} (ha' : a ^ r = 1) (hb' : b ^ r = 1)
    (hy : y ^ s = 1) (ha1' : a ≠ 1) (hb1' : b ∉ Subgroup.zpowers a) (hy1 : y ≠ 1)
    (hab' : a * b = b * a) (hay : a * y = y * a) (hby : b * y = y * b) : False := by
  have := Fact.mk hr
  set H := Subgroup.closure ({a, b} : Set N) with hH
  set P0 := Subgroup.closure ({a0, b0} : Set N) with hP0
  have hHsq : r ^ 2 ∣ Nat.card H := sq_dvd_card_closure_pair hr ha' hb' hab' ha1' hb1'
  have hP0sq : r ^ 2 ∣ Nat.card P0 := sq_dvd_card_closure_pair hr ha hb hab ha1 hb1
  have hcardQ : ∀ Q : Sylow r N, Nat.card Q ≤ r ^ 2 := by
    intro Q
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 Q.isPGroup'
    have hdv : r ^ k ∣ Nat.card N := hk ▸ Subgroup.card_subgroup_dvd_card (Q : Subgroup N)
    have hk2 : k ≤ 2 := by
      by_contra h
      push Not at h
      exact hcube ((pow_dvd_pow r h).trans hdv)
    rw [hk]
    exact Nat.pow_le_pow_right hr.pos hk2
  obtain ⟨Q0, hQ0⟩ := (isPGroup_closure_pair ha hb hab).exists_le_sylow
  obtain ⟨Q1, hQ1⟩ := (isPGroup_closure_pair ha' hb' hab').exists_le_sylow
  have hP0Q0 : P0 = (Q0 : Subgroup N) :=
    Subgroup.eq_of_le_of_card_ge hQ0 ((hcardQ Q0).trans (Nat.le_of_dvd Nat.card_pos hP0sq))
  have hHQ1 : H = (Q1 : Subgroup N) :=
    Subgroup.eq_of_le_of_card_ge hQ1 ((hcardQ Q1).trans (Nat.le_of_dvd Nat.card_pos hHsq))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q0 Q1
  have hyc : ∀ x ∈ H, y * x = x * y := by
    intro x hx
    have hle : H ≤ Subgroup.centralizer ({y} : Set N) := by
      refine (Subgroup.closure_le _).2 ?_
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hay.symm
      · exact hby.symm
    exact Subgroup.mem_centralizer_iff.1 (hle hx) y rfl
  have hconj : ∀ q ∈ (Q0 : Subgroup N), g * q * g⁻¹ ∈ (Q1 : Subgroup N) := by
    intro q hq
    have h1 : MulAut.conj g q ∈ ((g • Q0 : Sylow r N) : Set N) := by
      rw [Sylow.coe_smul]
      exact Set.smul_mem_smul_set hq
    rw [hg] at h1
    exact h1
  have key : ∀ q ∈ P0, (g⁻¹ * y * g) * q = q * (g⁻¹ * y * g) := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ H := by
      rw [hHQ1]
      exact hconj q (hP0Q0 ▸ hq)
    have h2 := hyc _ h1
    calc g⁻¹ * y * g * q = g⁻¹ * (y * (g * q * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * q * g⁻¹) * y) * g := by rw [h2]
      _ = q * (g⁻¹ * y * g) := by group
  have ha0 : a0 ∈ P0 := Subgroup.subset_closure (by simp)
  have hb0 : b0 ∈ P0 := Subgroup.subset_closure (by simp)
  have hz := hC (g⁻¹ * y * g) (key a0 ha0) (key b0 hb0)
  have hyr : y ^ (r ^ 2) = 1 := by
    have h := conj_pow (a := g) (b := g⁻¹ * y * g) (i := r ^ 2)
    rw [hz, mul_one, mul_inv_cancel] at h
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e] at h
    exact h
  have hcop : Nat.Coprime s (r ^ 2) := ((Nat.coprime_primes hs hr).2 hrs.symm).pow_right 2
  have hdv : orderOf y ∣ Nat.gcd s (r ^ 2) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (orderOf_dvd_of_pow_eq_one hyr)
  rw [hcop.gcd_eq_one] at hdv
  exact hy1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdv))

theorem triples_false_of_sylow {r : ℕ} (hr : r.Prime) {a0 b0 : N} (ha : a0 ^ r = 1)
    (hb : b0 ^ r = 1) (hab : a0 * b0 = b0 * a0) (ha1 : a0 ≠ 1) (hb1 : b0 ∉ Subgroup.zpowers a0)
    (hcube : ¬ r ^ 3 ∣ Nat.card N)
    (hC : ∀ g : N, g * a0 = a0 * g → g * b0 = b0 * g → g ^ (r ^ 2) = 1)
    (hsq : ∀ q : ℕ, q.Prime → Odd q → q ^ 2 ∣ Nat.card N → q = r) :
    ∀ (r' s : ℕ) (a b y : N), r'.Prime → s.Prime → Odd r' → Odd s → r' ≠ s → a ^ r' = 1 →
      b ^ r' = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 → a * b = b * a →
        a * y = y * a → b * y = y * b → False := by
  intro r' s a b y hr' hs hodd _ hrs ha' hb' hy ha1' hb1' hy1 hab' hay hby
  have hr'r : r' = r :=
    hsq r' hr' hodd ((sq_dvd_card_closure_pair hr' ha' hb' hab' ha1' hb1').trans
      (Subgroup.card_subgroup_dvd_card _))
  subst hr'r
  exact triples_false_core hr ha hb hab ha1 hb1 hcube hC hs hrs ha' hb' hy ha1' hb1' hy1 hab' hay
    hby

end Pair

end CFSG.GH74.GLS.Stage2.Bender.Thm1
