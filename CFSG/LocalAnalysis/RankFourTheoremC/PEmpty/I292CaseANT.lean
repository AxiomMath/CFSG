module

public import Mathlib.GroupTheory.Sylow
public meta import Lean.Meta.Tactic.NormCast
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.RingTheory.IntegralDomain
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

theorem dvd_sub_one_of_sq {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {w : ℤ} (h1 : (p : ℤ) ∣ w - 1)
    (h2 : (p : ℤ) ^ a ∣ w ^ 2 - 1) : (p : ℤ) ^ a ∣ w - 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hnd : ¬ (p : ℤ) ∣ w + 1 := by
    intro h
    have h3 : (p : ℤ) ∣ (w + 1) - (w - 1) := dvd_sub h h1
    have h4 : (w + 1) - (w - 1) = 2 := by ring
    rw [h4] at h3
    have h5 : p ∣ 2 := by exact_mod_cast h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h5)
  have hcop : IsCoprime ((p : ℤ) ^ a) (w + 1) :=
    ((Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hnd).pow_left
  have h6 : (p : ℤ) ^ a ∣ (w - 1) * (w + 1) := by
    have : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
    rwa [this] at h2
  exact hcop.dvd_of_dvd_mul_right h6

theorem dvd_sub_one_of_pow_two_pow {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) {w : ℤ}
    (h1 : (p : ℤ) ∣ w - 1) (h2 : (p : ℤ) ^ a ∣ w ^ (2 ^ k) - 1) : (p : ℤ) ^ a ∣ w - 1 := by
  induction k with
  | zero => simpa using h2
  | succ k ih =>
    refine ih ?_
    have h3 : (p : ℤ) ∣ w ^ (2 ^ k) - 1 :=
      h1.trans (by simpa using sub_dvd_pow_sub_pow w 1 (2 ^ k))
    have h4 : w ^ (2 ^ (k + 1)) = (w ^ (2 ^ k)) ^ 2 := by rw [pow_succ, pow_mul]
    rw [h4] at h2
    exact dvd_sub_one_of_sq hp hp2 h3 h2


theorem trivial_of_two_power {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Sylow p Kˣ) (α : Kˣ →* Kˣ) {m : ℤ} (hαm : ∀ x, α x = x ^ m) {j : ℕ}
    (hn : (Nat.card Kˣ : ℤ) ∣ m ^ (2 ^ j) - 1) {d : Kˣ} (hd : ∀ b : Kˣ, b ^ p ≠ d)
    (hαd : ∃ l : Kˣ, α d = l ^ p * d) : ∀ x ∈ (Q : Subgroup Kˣ), α x = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  set N := Nat.card Kˣ with hN
  have hog : orderOf g = N := orderOf_eq_card_of_forall_mem_zpowers hg
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpN : p ∣ N := by
    by_contra hnd
    have hcop : Nat.Coprime N p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    obtain ⟨b, hb⟩ := (powCoprime hcop).surjective d
    exact hd b (by simpa using hb)
  obtain ⟨e, he⟩ := Subgroup.mem_zpowers_iff.1 (hg d)
  have hpe : ¬ (p : ℤ) ∣ e := by
    rintro ⟨u, hu⟩
    refine hd (g ^ u) ?_
    rw [← zpow_natCast, ← zpow_mul, ← he, hu]
    congr 1
    ring
  obtain ⟨l, hl⟩ := hαd
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1 (hg l)
  have h1 : g ^ (e * m) = g ^ (t * (p : ℤ) + e) := by
    have hdm : α d = d ^ m := hαm d
    rw [hdm, ← he, ← ht, ← zpow_mul] at hl
    rw [hl, ← zpow_natCast (g ^ t) p, ← zpow_mul, ← zpow_add]
  have h2 : (N : ℤ) ∣ (t * p + e) - e * m := by
    have h2' := zpow_eq_zpow_iff_modEq.1 h1
    rw [hog] at h2'
    exact Int.modEq_iff_dvd.1 h2'
  have h3 : (p : ℤ) ∣ e * (m - 1) := by
    have h4 : (p : ℤ) ∣ (t * p + e) - e * m := (Int.natCast_dvd_natCast.2 hpN).trans h2
    have h5 : (t * p + e) - e * m = p * t - e * (m - 1) := by ring
    rw [h5] at h4
    have h6 : (p : ℤ) ∣ p * t := dvd_mul_right _ _
    have h7 := dvd_sub h6 h4
    simpa using h7
  have hpm : (p : ℤ) ∣ m - 1 := (hpz.dvd_or_dvd h3).resolve_left hpe
  have h7 : (N : ℤ) ∣ m ^ (2 ^ j) - 1 := hn
  have hpaN : (p : ℤ) ^ (N.factorization p) ∣ (N : ℤ) := by
    exact_mod_cast Nat.ordProj_dvd N p
  have h9 : (p : ℤ) ^ (N.factorization p) ∣ m - 1 :=
    dvd_sub_one_of_pow_two_pow hp hp2 j hpm (hpaN.trans h7)
  intro x hxQ
  have hcardQ : Nat.card (Q : Subgroup Kˣ) = p ^ N.factorization p := by
    rw [Sylow.card_eq_multiplicity]
  have hxp : x ^ (p ^ N.factorization p) = 1 := by
    have h10 : (⟨x, hxQ⟩ : (Q : Subgroup Kˣ)) ^ Nat.card (Q : Subgroup Kˣ) = 1 :=
      pow_card_eq_one'
    rw [hcardQ] at h10
    simpa using congrArg Subtype.val h10
  obtain ⟨u, hu⟩ := h9
  have hm : m = ((p ^ N.factorization p : ℕ) : ℤ) * u + 1 := by
    push_cast
    linarith
  rw [hαm, hm, zpow_add, zpow_one, zpow_mul, zpow_natCast, hxp, one_zpow, one_mul]


theorem trivial_of_field_aut {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (Q : Sylow p Kˣ) (σ : K ≃+* K) {j : ℕ} (hj : 1 ≤ j) (hσ : σ ^ (2 ^ j) = 1)
    {s : ℤ} (hs : s = 1 ∨ s = -1) {d : Kˣ} (hd : ∀ b : Kˣ, b ^ p ≠ d)
    (hl : ∃ l : Kˣ, (Units.map (σ : K →* K) d) ^ s = l ^ p * d) :
    ∀ x ∈ (Q : Subgroup Kˣ), (Units.map (σ : K →* K) x) ^ s = x := by
  set σ' : Kˣ →* Kˣ := Units.map (σ : K →* K) with hσ'
  obtain ⟨m₀, hm₀⟩ := MonoidHom.map_cyclic σ'
  set α : Kˣ →* Kˣ := (zpowGroupHom s).comp σ' with hα
  have hαm : ∀ x, α x = x ^ (m₀ * s) := by
    intro x
    simp only [hα, MonoidHom.comp_apply, zpowGroupHom_apply, hm₀, ← zpow_mul]
  have hpow : ∀ n : ℕ, ∀ x : Kˣ, Units.map ((σ ^ n : K ≃+* K) : K →* K) x = x ^ (m₀ ^ n) := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, pow_zero, zpow_one]
      exact Units.ext rfl
    | succ n ih =>
      intro x
      have h1 : Units.map ((σ ^ (n + 1) : K ≃+* K) : K →* K) x =
          σ' (Units.map ((σ ^ n : K ≃+* K) : K →* K) x) := by
        rw [pow_succ']
        rfl
      rw [h1, ih, hm₀, ← zpow_mul, pow_succ, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hog : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have h2 : (Nat.card Kˣ : ℤ) ∣ m₀ ^ (2 ^ j) - 1 := by
    have h3 := hpow (2 ^ j) g
    rw [hσ] at h3
    have h3' : g ^ (m₀ ^ (2 ^ j)) = g := h3.symm.trans (Units.ext rfl)
    have h4 : g ^ (m₀ ^ (2 ^ j) - 1) = 1 := by
      rw [zpow_sub_one, h3']
      exact mul_inv_cancel g
    have h5 := orderOf_dvd_iff_zpow_eq_one.2 h4
    rwa [hog] at h5
  have hs2 : s ^ (2 ^ j) = 1 := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rcases hs with rfl | rfl
    · exact one_pow _
    · exact Even.neg_one_pow ⟨2 ^ i, by ring⟩
  have h6 : (Nat.card Kˣ : ℤ) ∣ (m₀ * s) ^ (2 ^ j) - 1 := by
    rwa [mul_pow, hs2, mul_one]
  intro x hx
  have := trivial_of_two_power hp hp2 Q α hαm h6 hd (by simpa [hα] using hl) x hx
  simpa [hα] using this

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA


