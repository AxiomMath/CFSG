module

public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoDefs

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup

variable {P : Type*} [Group P]

theorem commute_of_commute_sq_of_odd {x q : P} (hx : Odd (orderOf x))
    (h : x ^ 2 * q = q * x ^ 2) : x * q = q * x := by
  obtain ⟨m, hm⟩ := hx
  have hx1 : x = (x ^ 2) ^ (m + 1) := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [hx1]
  exact Commute.pow_left h (m + 1)

theorem exists_conj_eq_mul_pow {t x : P} (ht : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹)
    (hx : Odd (orderOf x)) (k : ℕ) : ∃ j : ℕ, x⁻¹ ^ j * t * x ^ j = t * x ^ k := by
  obtain ⟨m, hm⟩ := hx
  refine ⟨k * (m + 1), ?_⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * x⁻¹ * t⁻¹ = x := by
    rw [show t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ by group, htx, inv_inv]
  have h2 : t * x⁻¹ ^ (k * (m + 1)) * t = x ^ (k * (m + 1)) := by
    have h3 : (t * x⁻¹ * t⁻¹) ^ (k * (m + 1)) = x ^ (k * (m + 1)) := by rw [h1]
    rw [conj_pow, htinv] at h3
    exact h3
  have hjk : x ^ (k * (m + 1) + k * (m + 1)) = x ^ k := by
    rw [show k * (m + 1) + k * (m + 1) = (orderOf x + 1) * k by rw [hm]; ring, pow_mul,
      pow_succ, pow_orderOf_eq_one, one_mul]
  calc x⁻¹ ^ (k * (m + 1)) * t * x ^ (k * (m + 1))
      = (t * t) * x⁻¹ ^ (k * (m + 1)) * t * x ^ (k * (m + 1)) := by rw [ht, one_mul]
    _ = t * (t * x⁻¹ ^ (k * (m + 1)) * t) * x ^ (k * (m + 1)) := by group
    _ = t * x ^ (k * (m + 1)) * x ^ (k * (m + 1)) := by rw [h2]
    _ = t * x ^ k := by rw [mul_assoc, ← pow_add, hjk]

theorem card_le_four_of_dihedral [Finite P] {Q : Subgroup P} {t x : P} (ht : t * t = 1)
    (htx : t * x * t⁻¹ = x⁻¹) (hx : Odd (orderOf x)) (hxQ : ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (htQ : ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) (hfix : ∀ q ∈ Q, x * q = q * x → q = 1)
    (hct : ∀ a ∈ Q, ∀ b ∈ Q, a * t = t * a → b * t = t * b → a ≠ 1 → b ≠ 1 → a = b) :
    Nat.card Q ≤ 4 := by
  classical
  have : Fintype P := Fintype.ofFinite P
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let τ : ℕ → P := fun k => t * x ^ k
  have hτinv : ∀ k, (τ k)⁻¹ = τ k := by
    intro k
    apply inv_eq_of_mul_eq_one_right
    have h1 : (t * x * t⁻¹) ^ k = x⁻¹ ^ k := by rw [htx]
    rw [conj_pow, htinv] at h1
    calc τ k * τ k = (t * x ^ k * t) * x ^ k := by simp only [τ]; group
      _ = 1 := by rw [h1, inv_pow, inv_mul_cancel]
  have hττ : ∀ k, τ k * τ k = 1 := fun k => by
    have := hτinv k
    calc τ k * τ k = τ k * (τ k)⁻¹ := by rw [this]
      _ = 1 := mul_inv_cancel _
  have hxpow : ∀ n : ℕ, ∀ q ∈ Q, x ^ n * q * (x ^ n)⁻¹ ∈ Q := by
    intro n
    induction n with
    | zero => intro q hq; simpa using hq
    | succ n ih =>
      intro q hq
      rw [show x ^ (n + 1) * q * (x ^ (n + 1))⁻¹ = x * (x ^ n * q * (x ^ n)⁻¹) * x⁻¹ by
        rw [pow_succ']; group]
      exact hxQ _ (ih q hq)
  have hτQ : ∀ k, ∀ q ∈ Q, τ k * q * (τ k)⁻¹ ∈ Q := by
    intro k q hq
    rw [show τ k * q * (τ k)⁻¹ = t * (x ^ k * q * (x ^ k)⁻¹) * t⁻¹ by simp only [τ]; group]
    exact htQ _ (hxpow k q hq)
  have hcτ : ∀ k, ∀ a ∈ Q, ∀ b ∈ Q, a * τ k = τ k * a → b * τ k = τ k * b → a ≠ 1 → b ≠ 1 →
      a = b := by
    intro k a ha b hb hat hbt ha1 hb1
    obtain ⟨j, hj⟩ := exists_conj_eq_mul_pow ht htx hx k
    have hτ : τ k = (x ^ j)⁻¹ * t * x ^ j := by simp only [τ]; rw [← hj, inv_pow]
    have key : ∀ c ∈ Q, c * τ k = τ k * c →
        (x ^ j * c * (x ^ j)⁻¹) * t = t * (x ^ j * c * (x ^ j)⁻¹) := by
      intro c _ hc
      rw [hτ] at hc
      calc x ^ j * c * (x ^ j)⁻¹ * t = x ^ j * (c * ((x ^ j)⁻¹ * t * x ^ j)) * (x ^ j)⁻¹ := by
            group
        _ = x ^ j * (((x ^ j)⁻¹ * t * x ^ j) * c) * (x ^ j)⁻¹ := by rw [hc]
        _ = t * (x ^ j * c * (x ^ j)⁻¹) := by group
    have hne : ∀ c : P, c ≠ 1 → x ^ j * c * (x ^ j)⁻¹ ≠ 1 := by
      intro c hc h1; apply hc
      calc c = (x ^ j)⁻¹ * (x ^ j * c * (x ^ j)⁻¹) * x ^ j := by group
        _ = 1 := by rw [h1]; group
    have := hct _ (hxpow j a ha) _ (hxpow j b hb) (key a ha hat) (key b hb hbt) (hne a ha1)
      (hne b hb1)
    calc a = (x ^ j)⁻¹ * (x ^ j * a * (x ^ j)⁻¹) * x ^ j := by group
      _ = (x ^ j)⁻¹ * (x ^ j * b * (x ^ j)⁻¹) * x ^ j := by rw [this]
      _ = b := by group
  let QF : Finset P := Finset.univ.filter (· ∈ Q)
  let IF : ℕ → Finset P := fun k => QF.filter (fun q => τ k * q * (τ k)⁻¹ = q⁻¹)
  have hQF : Nat.card Q = QF.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hI : ∀ k, QF.card ≤ 2 * (IF k).card := by
    intro k
    let f : P → P := fun q => q * (τ k * q⁻¹ * (τ k)⁻¹)
    refine Finset.card_le_mul_card_image_of_maps_to (f := f) ?_ 2 ?_
    · intro q hq
      have hqQ : q ∈ Q := (Finset.mem_filter.mp hq).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        mul_mem hqQ (hτQ k _ (inv_mem hqQ))⟩, ?_⟩
      simp only [f]
      rw [hτinv]
      calc τ k * (q * (τ k * q⁻¹ * τ k)) * τ k = τ k * q * τ k * q⁻¹ * (τ k * τ k) := by group
        _ = τ k * q * τ k * q⁻¹ := by rw [hττ, mul_one]
        _ = (q * (τ k * q⁻¹ * τ k))⁻¹ := by
          rw [show (q * (τ k * q⁻¹ * τ k))⁻¹ = (τ k)⁻¹ * q * (τ k)⁻¹ * q⁻¹ by group, hτinv]
    · intro b _
      by_contra hlt
      push Not at hlt
      obtain ⟨a₁, ha₁, a₂, ha₂, a₃, ha₃, h12, h13, h23⟩ := Finset.two_lt_card.mp hlt
      simp only [Finset.mem_filter] at ha₁ ha₂ ha₃
      have hmemQ : ∀ q ∈ QF, q ∈ Q := fun q hq => (Finset.mem_filter.mp hq).2
      have hQ1 : a₁ ∈ Q := hmemQ _ ha₁.1
      have hfib : ∀ c, c ∈ Q → f c = b → (a₁⁻¹ * c) * τ k = τ k * (a₁⁻¹ * c) := by
        intro c _ hc
        have he : a₁ * τ k * a₁⁻¹ = c * τ k * c⁻¹ := by
          have := ha₁.2.trans hc.symm
          change a₁ * (τ k * a₁⁻¹ * (τ k)⁻¹) = c * (τ k * c⁻¹ * (τ k)⁻¹) at this
          rw [hτinv] at this
          have h' : a₁ * (τ k * a₁⁻¹ * τ k) * τ k = c * (τ k * c⁻¹ * τ k) * τ k := by
            rw [this]
          rw [show a₁ * (τ k * a₁⁻¹ * τ k) * τ k = a₁ * τ k * a₁⁻¹ * (τ k * τ k) by group,
            show c * (τ k * c⁻¹ * τ k) * τ k = c * τ k * c⁻¹ * (τ k * τ k) by group] at h'
          rw [hττ, mul_one, mul_one] at h'
          exact h'
        calc a₁⁻¹ * c * τ k = a₁⁻¹ * (c * τ k * c⁻¹) * c := by group
          _ = a₁⁻¹ * (a₁ * τ k * a₁⁻¹) * c := by rw [he]
          _ = τ k * (a₁⁻¹ * c) := by group
      have hne : ∀ c : P, c ≠ a₁ → a₁⁻¹ * c ≠ 1 := by
        intro c hc h1; apply hc
        calc c = a₁ * (a₁⁻¹ * c) := by group
          _ = a₁ := by rw [h1, mul_one]
      have := hcτ k _ (mul_mem (inv_mem hQ1) (hmemQ _ ha₂.1)) _
        (mul_mem (inv_mem hQ1) (hmemQ _ ha₃.1))
        (hfib a₂ (hmemQ _ ha₂.1) ha₂.2) (hfib a₃ (hmemQ _ ha₃.1) ha₃.2) (hne a₂ (Ne.symm h12))
        (hne a₃ (Ne.symm h13))
      apply h23
      calc a₂ = a₁ * (a₁⁻¹ * a₂) := by group
        _ = a₁ * (a₁⁻¹ * a₃) := by rw [this]
        _ = a₃ := by group
  have hconj : ∀ j k : ℕ, ∀ q : P, τ j * q * (τ j)⁻¹ = τ k * q * (τ k)⁻¹ →
      x ^ j * q * (x ^ j)⁻¹ = x ^ k * q * (x ^ k)⁻¹ := by
    intro j k q h
    rw [show τ j * q * (τ j)⁻¹ = t * (x ^ j * q * (x ^ j)⁻¹) * t⁻¹ by simp only [τ]; group,
      show τ k * q * (τ k)⁻¹ = t * (x ^ k * q * (x ^ k)⁻¹) * t⁻¹ by simp only [τ]; group] at h
    exact mul_left_cancel (mul_right_cancel h)
  have hmem : ∀ k, ∀ q ∈ IF k, q ∈ Q ∧ τ k * q * (τ k)⁻¹ = q⁻¹ := fun k q hq =>
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2, (Finset.mem_filter.mp hq).2⟩
  have hx2 : ∀ q ∈ Q, x ^ 2 * q * (x ^ 2)⁻¹ = q → q = 1 := by
    intro q hq h
    apply hfix q hq
    apply commute_of_commute_sq_of_odd hx
    calc x ^ 2 * q = x ^ 2 * q * (x ^ 2)⁻¹ * x ^ 2 := by group
      _ = q * x ^ 2 := by rw [h]
  have hx1 : ∀ q ∈ Q, x * q * x⁻¹ = q → q = 1 := by
    intro q hq h
    apply hfix q hq
    calc x * q = x * q * x⁻¹ * x := by group
      _ = q * x := by rw [h]
  have h01 : ∀ q ∈ IF 0 ∩ IF 1, q = 1 := by
    intro q hq
    rw [Finset.mem_inter] at hq
    obtain ⟨hq0, h0⟩ := hmem 0 q hq.1
    obtain ⟨-, h1⟩ := hmem 1 q hq.2
    have := hconj 0 1 q (h0.trans h1.symm)
    simp only [pow_zero, pow_one, one_mul, inv_one, mul_one] at this
    exact hx1 q hq0 this.symm
  have h02 : ∀ q ∈ IF 0 ∩ IF 2, q = 1 := by
    intro q hq
    rw [Finset.mem_inter] at hq
    obtain ⟨hq0, h0⟩ := hmem 0 q hq.1
    obtain ⟨-, h2⟩ := hmem 2 q hq.2
    have := hconj 0 2 q (h0.trans h2.symm)
    simp only [pow_zero, one_mul, inv_one, mul_one] at this
    exact hx2 q hq0 this.symm
  have h12 : ∀ q ∈ IF 1 ∩ IF 2, q = 1 := by
    intro q hq
    rw [Finset.mem_inter] at hq
    obtain ⟨hq1, h1⟩ := hmem 1 q hq.1
    obtain ⟨-, h2⟩ := hmem 2 q hq.2
    have := hconj 1 2 q (h1.trans h2.symm)
    apply hx1 q hq1
    rw [pow_one] at this
    have h3 : q = x * q * x⁻¹ := by
      calc q = x⁻¹ * (x * q * x⁻¹) * x := by group
        _ = x⁻¹ * (x ^ 2 * q * (x ^ 2)⁻¹) * x := by rw [this]
        _ = x * q * x⁻¹ := by group
    exact h3.symm
  have hsub : ∀ k, IF k ⊆ QF := fun k => Finset.filter_subset _ _
  have hle1 : ∀ s : Finset P, (∀ q ∈ s, q = 1) → s.card ≤ 1 := fun s hs =>
    Finset.card_le_one.mpr fun a ha b hb => (hs a ha).trans (hs b hb).symm
  have hu1 := Finset.card_union_add_card_inter (IF 0) (IF 1)
  have hu2 := Finset.card_union_add_card_inter (IF 0 ∪ IF 1) (IF 2)
  have hi1 : (IF 0 ∩ IF 1).card ≤ 1 := hle1 _ h01
  have hi2 : ((IF 0 ∪ IF 1) ∩ IF 2).card ≤ 1 := hle1 _ fun q hq => by
    rw [Finset.mem_inter, Finset.mem_union] at hq
    rcases hq.1 with h | h
    · exact h02 q (Finset.mem_inter.mpr ⟨h, hq.2⟩)
    · exact h12 q (Finset.mem_inter.mpr ⟨h, hq.2⟩)
  have hU : (IF 0 ∪ IF 1 ∪ IF 2).card ≤ QF.card :=
    Finset.card_le_card (Finset.union_subset (Finset.union_subset (hsub 0) (hsub 1)) (hsub 2))
  have hI0 := hI 0
  have hI1 := hI 1
  have hI2 := hI 2
  rw [hQF]
  omega


section Fixed

variable {X : Type*} [Group X]

@[expose] def secTwoOmegaZ (Q : Subgroup X) : Subgroup X where
  carrier := {a | a ∈ Q ∧ (∀ q ∈ Q, q * a = a * q) ∧ a ^ 2 = 1}
  mul_mem' {a b} ha hb := by
    refine ⟨mul_mem ha.1 hb.1, fun q hq => ?_, ?_⟩
    · rw [← mul_assoc, ha.2.1 q hq, mul_assoc, hb.2.1 q hq, mul_assoc]
    · rw [sq, show a * b * (a * b) = a * (b * a) * b by group, ha.2.1 b hb.1,
        show a * (a * b) * b = a ^ 2 * b ^ 2 by rw [sq, sq]; group, ha.2.2, hb.2.2, one_mul]
  one_mem' := ⟨one_mem _, fun q _ => by simp, one_pow 2⟩
  inv_mem' {a} ha := by
    refine ⟨inv_mem ha.1, fun q hq => ?_, by rw [inv_pow, ha.2.2, inv_one]⟩
    have := ha.2.1 q hq
    calc q * a⁻¹ = a⁻¹ * (a * q) * a⁻¹ := by group
      _ = a⁻¹ * (q * a) * a⁻¹ := by rw [this]
      _ = a⁻¹ * q := by group

theorem mem_secTwoOmegaZ {Q : Subgroup X} {a : X} :
    a ∈ secTwoOmegaZ Q ↔ a ∈ Q ∧ (∀ q ∈ Q, q * a = a * q) ∧ a ^ 2 = 1 := Iff.rfl

theorem secTwoOmegaZ_le (Q : Subgroup X) : secTwoOmegaZ Q ≤ Q := fun _ ha => ha.1

theorem secTwoOmegaZ_comm {Q : Subgroup X} {a : X} (ha : a ∈ secTwoOmegaZ Q) {q : X}
    (hq : q ∈ Q) : q * a = a * q := ha.2.1 q hq

theorem secTwoOmegaZ_sq {Q : Subgroup X} {a : X} (ha : a ∈ secTwoOmegaZ Q) : a ^ 2 = 1 :=
  ha.2.2

theorem secTwoOmegaZ_conj {Q : Subgroup X} (hQ : Q.Normal) {a : X} (ha : a ∈ secTwoOmegaZ Q)
    (g : X) : g * a * g⁻¹ ∈ secTwoOmegaZ Q := by
  refine ⟨hQ.conj_mem a ha.1 g, fun q hq => ?_, by rw [conj_pow, ha.2.2]; group⟩
  have h1 : g⁻¹ * q * g ∈ Q := by
    have := hQ.conj_mem q hq g⁻¹
    simpa using this
  have h2 := ha.2.1 _ h1
  calc q * (g * a * g⁻¹) = g * ((g⁻¹ * q * g) * a) * g⁻¹ := by group
    _ = g * (a * (g⁻¹ * q * g)) * g⁻¹ := by rw [h2]
    _ = g * a * g⁻¹ * q := by group

instance secTwoOmegaZ_normal (Q : Subgroup X) [hQ : Q.Normal] : (secTwoOmegaZ Q).Normal :=
  ⟨fun _ ha g => secTwoOmegaZ_conj hQ ha g⟩

@[instance_reducible]
def secTwoConjAction {H K : Subgroup X} (hHK : H ≤ normalizer (K : Set X)) : MulAction H K where
  smul h k := ⟨(h : X) * k * (h : X)⁻¹, (mem_normalizer_iff.mp (hHK h.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by change (1 : X) * k * (1 : X)⁻¹ = k; group)
  mul_smul a b k := Subtype.ext (by
    change ((a : X) * b) * k * ((a : X) * b)⁻¹ = a * (b * k * (b : X)⁻¹) * (a : X)⁻¹
    group)

theorem secTwo_exists_fixed_of_two [Finite X] {K : Subgroup X} (hK : IsPGroup 2 K)
    (hne : K ≠ ⊥) {g : X} (hg : IsPGroup 2 (zpowers g)) (hgK : g ∈ normalizer (K : Set X)) :
    ∃ c ∈ K, c ≠ 1 ∧ g * c * g⁻¹ = c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := secTwoConjAction (zpowers_le.mpr hgK)
  obtain ⟨n, hn, hcard⟩ := hK.nontrivial_iff_card.mp
    ((Subgroup.nontrivial_iff_ne_bot K).mpr hne)
  have h1 : (1 : K) ∈ MulAction.fixedPoints (zpowers g) K := by
    intro h; apply Subtype.ext; change (h : X) * 1 * (h : X)⁻¹ = 1; group
  obtain ⟨c, hc, hc1⟩ := hg.exists_fixed_point_of_prime_dvd_card_of_fixed_point K
    (by rw [hcard]; exact dvd_pow_self 2 (by omega)) h1
  refine ⟨c, c.2, fun h => hc1 (Subtype.ext h.symm), ?_⟩
  have := congrArg Subtype.val (hc ⟨g, mem_zpowers g⟩)
  exact this

theorem secTwo_mem_of_conj_mem_coset [Finite X] {M N : Subgroup X} (hNM : N ≤ M)
    (hN : IsPGroup 2 N) {x : X} (hx : IsPGroup 3 (zpowers x)) (hxN : x ∈ normalizer (N : Set X))
    (hfix : ∀ m ∈ M, x * m * x⁻¹ = m → m = 1) {q : X} (hq : q ∈ M)
    (hqx : q⁻¹ * (x * q * x⁻¹) ∈ N) : q ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Set X := {c | q⁻¹ * c ∈ N}
  have hxC : ∀ c ∈ C, x * c * x⁻¹ ∈ C := by
    intro c hc
    change q⁻¹ * (x * c * x⁻¹) ∈ N
    rw [show q⁻¹ * (x * c * x⁻¹) = (q⁻¹ * (x * q * x⁻¹)) * (x * (q⁻¹ * c) * x⁻¹) by group]
    exact mul_mem hqx ((mem_normalizer_iff.mp hxN _).mp hc)
  have hpowC : ∀ n : ℕ, ∀ c ∈ C, x ^ n * c * (x ^ n)⁻¹ ∈ C := by
    intro n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [show x ^ (n + 1) * c * (x ^ (n + 1))⁻¹ = x * (x ^ n * c * (x ^ n)⁻¹) * x⁻¹ by
        rw [pow_succ']; group]
      exact hxC _ (ih c hc)
  have hgC : ∀ g ∈ zpowers x, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨n, rfl⟩ := (mem_powers_iff_mem_zpowers.mpr hg)
    exact hpowC n c hc
  let _ : MulAction (zpowers x) C :=
    { smul := fun g c => ⟨(g : X) * c * (g : X)⁻¹, hgC g g.2 c c.2⟩
      one_smul := fun c => Subtype.ext (by change (1 : X) * c * (1 : X)⁻¹ = c; group)
      mul_smul := fun a b c => Subtype.ext (by
        change ((a : X) * b) * c * ((a : X) * b)⁻¹ = a * (b * c * (b : X)⁻¹) * (a : X)⁻¹
        group) }
  have hcard : Nat.card C = Nat.card N := by
    refine Nat.card_congr
      { toFun := fun c => ⟨q⁻¹ * c, c.2⟩
        invFun := fun n => ⟨q * n, by change q⁻¹ * (q * n) ∈ N; simp⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  have h3 : ¬ 3 ∣ Nat.card C := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hN.exists_card_eq
    rw [hk]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  obtain ⟨c, hc⟩ := hx.nonempty_fixed_point_of_prime_not_dvd_card C h3
  have hcx : x * (c : X) * x⁻¹ = c := congrArg Subtype.val (hc ⟨x, mem_zpowers x⟩)
  have hcM : (c : X) ∈ M := by
    have h1 : q⁻¹ * (c : X) ∈ N := c.2
    have : (c : X) = q * (q⁻¹ * c) := by group
    rw [this]
    exact mul_mem hq (hNM h1)
  have hc1 := hfix _ hcM hcx
  have h1 : q⁻¹ * (c : X) ∈ N := c.2
  rw [hc1, mul_one] at h1
  simpa using h1

theorem secTwo_eq_of_card_le_four [Finite X] {W : Subgroup X} (hW : Nat.card W ≤ 4)
    {a b c d : X} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {e : X} (he : e ∈ W) :
    e = a ∨ e = b ∨ e = c ∨ e = d := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hea, heb, hec, hed⟩ := hne
  let F : Finset X := {a, b, c, d, e}
  have hF : F.card = 5 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had, Ne.symm hea]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd, Ne.symm heb]),
      Finset.card_insert_of_notMem (by simp [hcd, Ne.symm hec]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hed]), Finset.card_singleton]
  have hinj : Function.Injective (fun f : F => (⟨f.1, by
      rcases Finset.mem_insert.mp f.2 with h | h
      · rw [h]; exact ha
      rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hb
      rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hc
      rcases Finset.mem_insert.mp h with h | h
      · rw [h]; exact hd
      rw [Finset.mem_singleton.mp h]; exact he⟩ : W)) := by
    intro f₁ f₂ hf
    have h1 := congrArg Subtype.val hf
    exact Subtype.ext h1
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard, hF] at this
  omega

end Fixed

end CFSG.LocalAnalysis.EvenBN.Tits
