module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup

variable {N : Type*} [Group N] [Finite N]

theorem triples_false_of_sylow_cover_eq {r k t : ℕ} (hr : r.Prime) {P : Subgroup N}
    (hPcard : Nat.card P = r ^ k) (hk : ¬ r ^ (k + 1) ∣ Nat.card N) {Es : Set (N × N)}
    (hcover : ∀ a b : N, a ∈ P → b ∈ P → a ^ r = 1 → b ^ r = 1 → a ≠ 1 →
      b ∉ Subgroup.zpowers a → a * b = b * a →
        ∃ e ∈ Es, e.1 ∈ Subgroup.closure ({a, b} : Set N) ∧
          e.2 ∈ Subgroup.closure ({a, b} : Set N))
    (hC : ∀ e ∈ Es, ∀ g : N, g * e.1 = e.1 * g → g * e.2 = e.2 * g → g ^ (2 ^ t * r ^ k) = 1) :
    ∀ (r' s : ℕ) (a b y : N), r' = r → r'.Prime → s.Prime → Odd r' → Odd s → r' ≠ s → a ^ r' = 1 →
      b ^ r' = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 → a * b = b * a →
        a * y = y * a → b * y = y * b → False := by
  intro r' s a b y hr'r hr' hs hodd hsodd hrs ha' hb' hy ha1' hb1' hy1 hab' hay hby
  have := Fact.mk hr
  rw [hr'r] at ha' hb' hrs
  have hHp : IsPGroup r (Subgroup.closure ({a, b} : Set N)) :=
    isPGroup_closure_pair ha' hb' hab'
  obtain ⟨Q1, hQ1⟩ := hHp.exists_le_sylow
  have hPp : IsPGroup r P := IsPGroup.iff_card.2 ⟨k, hPcard⟩
  obtain ⟨Q0, hQ0⟩ := hPp.exists_le_sylow
  have hcardQ : ∀ Q : Sylow r N, Nat.card Q ≤ r ^ k := by
    intro Q
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 Q.isPGroup'
    have hdv : r ^ j ∣ Nat.card N := hj ▸ Subgroup.card_subgroup_dvd_card (Q : Subgroup N)
    have hjk : j ≤ k := by
      by_contra h
      push Not at h
      exact hk ((pow_dvd_pow r h).trans hdv)
    rw [hj]
    exact Nat.pow_le_pow_right hr.pos hjk
  have hPQ0 : P = (Q0 : Subgroup N) :=
    Subgroup.eq_of_le_of_card_ge hQ0 (by rw [hPcard]; exact hcardQ Q0)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N Q0 Q1
  have hconj' : ∀ x ∈ (Q1 : Subgroup N), g⁻¹ * x * g ∈ (Q0 : Subgroup N) := by
    intro x hx
    rw [← hg] at hx
    have hx' : x ∈ ((g • Q0 : Sylow r N) : Set N) := hx
    rw [Sylow.coe_smul] at hx'
    obtain ⟨q, hq, rfl⟩ := Set.mem_smul_set.1 hx'
    have e : g⁻¹ * (MulAut.conj g • q) * g = q := by
      show g⁻¹ * (g * q * g⁻¹) * g = q
      group
    rw [e]
    exact hq
  set φ := MulAut.conj g⁻¹ with hφ
  have hφapp : ∀ x : N, φ x = g⁻¹ * x * g := by
    intro x
    simp [hφ]
  have hmemP : ∀ x ∈ Subgroup.closure ({a, b} : Set N), φ x ∈ P := by
    intro x hx
    rw [hPQ0, hφapp]
    exact hconj' x (hQ1 hx)
  have ha_mem : a ∈ Subgroup.closure ({a, b} : Set N) := Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure ({a, b} : Set N) := Subgroup.subset_closure (by simp)
  obtain ⟨e, he, he1, he2⟩ := hcover (φ a) (φ b) (hmemP a ha_mem) (hmemP b hb_mem)
    (by rw [← map_pow, ha', map_one]) (by rw [← map_pow, hb', map_one])
    (fun h => ha1' (φ.injective (by rw [h, map_one])))
    (by
      intro h
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 h
      exact hb1' (Subgroup.mem_zpowers_iff.2 ⟨m, φ.injective (by rw [map_zpow, hm])⟩))
    (by rw [← map_mul, ← map_mul, hab'])
  have hyc : ∀ x ∈ Subgroup.closure ({φ a, φ b} : Set N), φ y * x = x * φ y := by
    intro x hx
    have hle : Subgroup.closure ({φ a, φ b} : Set N) ≤ Subgroup.centralizer ({φ y} : Set N) := by
      refine (Subgroup.closure_le _).2 ?_
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [← map_mul, ← map_mul, hay]
      · rw [← map_mul, ← map_mul, hby]
    exact Subgroup.mem_centralizer_iff.1 (hle hx) (φ y) rfl
  have hz := hC e he (φ y) (hyc _ he1) (hyc _ he2)
  have hyr : y ^ (2 ^ t * r ^ k) = 1 := φ.injective (by rw [map_pow, hz, map_one])
  have hs2 : Nat.Coprime s 2 :=
    (Nat.coprime_primes hs Nat.prime_two).2 (by rintro rfl; exact absurd hsodd (by decide))
  have hcop : Nat.Coprime s (2 ^ t * r ^ k) :=
    Nat.Coprime.mul_right (hs2.pow_right t) (((Nat.coprime_primes hs hr).2 hrs.symm).pow_right k)
  have hdv : orderOf y ∣ Nat.gcd s (2 ^ t * r ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy) (orderOf_dvd_of_pow_eq_one hyr)
  rw [hcop.gcd_eq_one] at hdv
  exact hy1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdv))

theorem triples_false_of_sylow_cover {r k t : ℕ} (hr : r.Prime) {P : Subgroup N}
    (hPcard : Nat.card P = r ^ k) (hk : ¬ r ^ (k + 1) ∣ Nat.card N) {Es : Set (N × N)}
    (hcover : ∀ a b : N, a ∈ P → b ∈ P → a ^ r = 1 → b ^ r = 1 → a ≠ 1 →
      b ∉ Subgroup.zpowers a → a * b = b * a →
        ∃ e ∈ Es, e.1 ∈ Subgroup.closure ({a, b} : Set N) ∧
          e.2 ∈ Subgroup.closure ({a, b} : Set N))
    (hC : ∀ e ∈ Es, ∀ g : N, g * e.1 = e.1 * g → g * e.2 = e.2 * g → g ^ (2 ^ t * r ^ k) = 1)
    (hsq : ∀ q : ℕ, q.Prime → Odd q → q ^ 2 ∣ Nat.card N → q = r) :
    ∀ (r' s : ℕ) (a b y : N), r'.Prime → s.Prime → Odd r' → Odd s → r' ≠ s → a ^ r' = 1 →
      b ^ r' = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 → a * b = b * a →
        a * y = y * a → b * y = y * b → False := by
  intro r' s a b y hr' hs hodd hsodd hrs ha' hb' hy ha1' hb1' hy1 hab' hay hby
  have hHsq := sq_dvd_card_closure_pair hr' ha' hb' hab' ha1' hb1'
  have hr'r : r' = r := hsq r' hr' hodd (hHsq.trans (Subgroup.card_subgroup_dvd_card _))
  exact triples_false_of_sylow_cover_eq hr hPcard hk hcover hC r' s a b y hr'r hr' hs hodd hsodd
    hrs ha' hb' hy ha1' hb1' hy1 hab' hay hby

end CFSG.GH74.GLS.Stage2.Bender.Thm1
