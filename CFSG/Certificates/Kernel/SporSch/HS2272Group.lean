module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.HS2272

open Subgroup CFSG.Sporadic.SmallOddCore

theorem ncard_conjClass_mul_fix {n : ℕ} (P : Subgroup (Equiv.Perm (Fin n)))
    (htr : ∀ x y : Fin n, ∃ p ∈ P, p x = y) (t : Equiv.Perm (Fin n)) (x₀ : Fin n) :
    (conjClass P t).ncard * (Finset.univ.filter fun x => t x = x).card =
      n * {y ∈ conjClass P t | y x₀ = x₀}.ncard := by
  classical
  set X : Finset (Equiv.Perm (Fin n)) := Finset.univ.filter fun y => y ∈ conjClass P t with hX
  have hXc : (conjClass P t).ncard = X.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp [X]
  have hX0 : {y ∈ conjClass P t | y x₀ = x₀}.ncard = (X.filter fun y => y x₀ = x₀).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext y
    simp [X]
  have hfix : ∀ y ∈ X, (Finset.univ.filter fun x => y x = x).card =
      (Finset.univ.filter fun x => t x = x).card := by
    intro y hy
    simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, mem_conjClass] at hy
    obtain ⟨g, -, rfl⟩ := hy
    refine Finset.card_bij (fun x _ => (g⁻¹ : Equiv.Perm (Fin n)) x) ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      have h2 := hx.2
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h2
      have h3 := congrArg (g⁻¹ : Equiv.Perm (Fin n)) h2
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_apply] at h3
      exact h3
    · intro x _ y _ h
      exact (g⁻¹ : Equiv.Perm (Fin n)).injective h
    · intro x hx
      refine ⟨g x, ?_, by simp⟩
      rw [Finset.mem_filter] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply,
        hx.2]
  have hpt : ∀ ω : Fin n, (X.filter fun y => y ω = ω).card = (X.filter fun y => y x₀ = x₀).card := by
    intro ω
    obtain ⟨p, hp, hpx⟩ := htr x₀ ω
    refine Finset.card_bij (fun y _ => p⁻¹ * y * p) ?_ ?_ ?_
    · intro y hy
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, mem_conjClass] at hy ⊢
      obtain ⟨⟨g, hg, rfl⟩, hyω⟩ := hy
      refine ⟨⟨p⁻¹ * g, P.mul_mem (P.inv_mem hp) hg, by group⟩, ?_⟩
      simp only [Equiv.Perm.mul_apply, hpx, hyω]
      simp [← hpx]
    · intro y _ z _ h
      simpa using h
    · intro z hz
      refine ⟨p * z * p⁻¹, ?_, by group⟩
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, mem_conjClass] at hz ⊢
      obtain ⟨⟨g, hg, rfl⟩, hz0⟩ := hz
      refine ⟨⟨p * g, P.mul_mem hp hg, by group⟩, ?_⟩
      rw [← hpx]
      simp [Equiv.Perm.mul_apply, hz0]
  have hsum : ∑ y ∈ X, (Finset.univ.filter fun x => y x = x).card =
      ∑ ω : Fin n, (X.filter fun y => y ω = ω).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl hfix, Finset.sum_congr rfl (fun ω _ => hpt ω),
    Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    smul_eq_mul] at hsum
  rw [hXc, hX0]
  exact hsum

variable {M : Type*} [Group M]

theorem exists_conj_mem_of_card_prime [Finite M] {K Q : Subgroup M} (hQK : Q ≤ K) {p : ℕ}
    [hp : Fact p.Prime] (hQ : Nat.card Q = p ^ (Nat.card K).factorization p) {y : M} (hy : y ∈ K)
    (hyp : orderOf y = p) : ∃ c ∈ K, c⁻¹ * y * c ∈ Q := by
  let Q' : Sylow p K := Sylow.ofCard (Q.subgroupOf K) (by
    rw [← hQ]
    exact Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv)
  have hyK : IsPGroup p (zpowers (⟨y, hy⟩ : K)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hyp, pow_one]
  obtain ⟨T, hT⟩ := hyK.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq K Q' T
  refine ⟨x, x.2, ?_⟩
  have hyT : (⟨y, hy⟩ : K) ∈ (T : Subgroup K) := hT (mem_zpowers _)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyT
  obtain ⟨s, hs, hsy⟩ := hyT
  have hsQ : (s : M) ∈ Q := by
    have : s ∈ Q.subgroupOf K := by
      rwa [show ((Q' : Subgroup K)) = Q.subgroupOf K from Sylow.coe_ofCard _ _] at hs
    exact mem_subgroupOf.mp this
  have e : x⁻¹ * ⟨y, hy⟩ * x = s := by
    rw [← hsy, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsQ

theorem oddCore_eq_bot_of_sylow [Finite M] (K : Subgroup M) (W : M → Prop)
    (hW : ∀ x, W x → ∃ h ∈ K, 2 ∣ orderOf (x * (h * x * h⁻¹)))
    (hQ : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card K → ∃ Q : Subgroup M, Q ≤ K ∧
      Nat.card Q = p ^ (Nat.card K).factorization p ∧
      ∀ y ∈ Q, y ≠ 1 → ∃ x, W x ∧ x ∈ zpowers y) :
    CFSG.oddCore ↥K = ⊥ := by
  classical
  have : Fintype M := Fintype.ofFinite M
  let xs : List M := (Finset.univ.filter fun y : M => y ≠ 1 ∧ ∃ x, W x ∧ x ∈ zpowers y).toList
  refine oddCore_eq_bot_of_witnesses K xs ?_ ?_
  · intro y hy hpr hp2
    have : Fact (orderOf y).Prime := ⟨hpr⟩
    have hdvd : orderOf y ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : K)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨Q, hQK, hQc, hQw⟩ := hQ _ hpr hp2 hdvd
    obtain ⟨c, hc, hcQ⟩ := exists_conj_mem_of_card_prime hQK hQc hy rfl
    have hx1 : c⁻¹ * y * c ≠ 1 := by
      intro h1
      have : y = 1 := by
        have := congrArg (fun z => c * z * c⁻¹) h1
        simpa [mul_assoc] using this
      rw [this, orderOf_one] at hpr
      exact Nat.not_prime_one hpr
    refine ⟨c⁻¹ * y * c, ?_, c, hc, by group⟩
    simp only [xs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hx1, hQw _ hcQ hx1⟩
  · intro x hx N hNK hNn hxN
    simp only [xs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨-, w, hw, hwx⟩ := hx
    have hwN : w ∈ N := (zpowers_le.mpr hxN) hwx
    obtain ⟨h, hh, h2⟩ := hW w hw
    exact ⟨w * (h * w * h⁻¹), N.mul_mem hwN (hNn h hh w hwN), h2⟩

theorem mem_of_enum [Finite M] {gs : Set M} {E : ℕ → M} {N : ℕ} (h1 : ∃ i < N, E i = 1)
    (hmul : ∀ i < N, ∀ s ∈ gs, ∃ j < N, E i * s = E j) :
    ∀ x ∈ closure gs, ∃ i < N, x = E i := by
  set T : Set M := {y | ∃ i < N, y = E i} with hT
  have hTf : T.Finite := by
    have : T = (fun i => E i) '' {i | i < N} := by
      ext y
      simp only [hT, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, hi, rfl⟩
    rw [this]
    exact (Set.finite_lt_nat N).image _
  have hstep : ∀ x : M, (∀ t ∈ T, t * x ∈ T) → ∀ t ∈ T, t * x⁻¹ ∈ T := by
    intro x hx t ht
    have hmaps : Set.MapsTo (fun y => y * x) T T := fun y hy => hx y hy
    have hinj : Set.InjOn (fun y => y * x) T := fun a _ b _ h => mul_right_cancel h
    have hbij := (hTf.injOn_iff_bijOn_of_mapsTo hmaps).1 hinj
    obtain ⟨y, hy, hyt⟩ := hbij.surjOn ht
    have : t * x⁻¹ = y := by
      rw [← hyt]
      group
    rw [this]
    exact hy
  have key : ∀ x ∈ closure gs, ∀ t ∈ T, t * x ∈ T := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem s hs =>
      rintro t ⟨i, hi, rfl⟩
      obtain ⟨j, hj, e⟩ := hmul i hi s hs
      exact ⟨j, hj, e⟩
    | one => intro t ht; simpa using ht
    | mul a b _ _ ha hb =>
      intro t ht
      rw [← mul_assoc]
      exact hb _ (ha t ht)
    | inv a _ ha => exact hstep a ha
  intro x hx
  obtain ⟨i, hi, he⟩ := h1
  have := key x hx 1 ⟨i, hi, he.symm⟩
  rw [one_mul] at this
  exact this

theorem mem_zpowers_of_prime {y z : M} (hp : (orderOf y).Prime) (hz : z ∈ zpowers y)
    (hz1 : z ≠ 1) : y ∈ zpowers z := by
  have hle : zpowers z ≤ zpowers y := zpowers_le.mpr hz
  have hdvd : orderOf z ∣ orderOf y := orderOf_dvd_of_mem_zpowers hz
  have hoz : orderOf z = orderOf y := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hfin : (orderOf y) ≠ 0 := hp.ne_zero
  have : Finite (zpowers y) := by
    have := Nat.card_zpowers y
    exact Nat.finite_of_card_ne_zero (by rw [this]; exact hfin)
  have heq : zpowers z = zpowers y := by
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Nat.card_zpowers, Nat.card_zpowers, hoz]
  rw [heq]
  exact mem_zpowers y

theorem pow_mod_three {y : M} (h : orderOf y = 3) (a : ℕ) : y ^ a = y ^ (a % 3) := by
  rw [← h, pow_mod_orderOf]

theorem closure_pair_nine [Finite M] {y₁ y₂ : M} (h₁ : orderOf y₁ = 3) (h₂ : orderOf y₂ = 3)
    (hc : Commute y₁ y₂) (hn : y₂ ∉ zpowers y₁) :
    Nat.card (closure ({y₁, y₂} : Set M)) = 9 ∧
      ∀ y ∈ closure ({y₁, y₂} : Set M), y ≠ 1 →
        ∃ x, (x = y₁ ∨ x = y₂ ∨ x = y₁ * y₂ ∨ x = y₁ * y₂ * y₂) ∧ x ∈ zpowers y := by
  set E : ℕ → M := fun i => y₁ ^ (i / 3) * y₂ ^ (i % 3) with hE
  have hmulE : ∀ a b c d : ℕ, y₁ ^ a * y₂ ^ b * (y₁ ^ c * y₂ ^ d) = y₁ ^ (a + c) * y₂ ^ (b + d) := by
    intro a b c d
    have : Commute (y₂ ^ b) (y₁ ^ c) := (hc.symm.pow_pow b c)
    rw [pow_add, pow_add, mul_assoc, ← mul_assoc (y₂ ^ b), this.eq, mul_assoc, mul_assoc]
  have hE_eq : ∀ a b : ℕ, y₁ ^ a * y₂ ^ b = E (3 * (a % 3) + b % 3) := by
    intro a b
    simp only [hE]
    rw [pow_mod_three h₁ a, pow_mod_three h₂ b]
    congr 2 <;> omega
  have hmem : ∀ i, E i ∈ closure ({y₁, y₂} : Set M) := fun i =>
    mul_mem (pow_mem (subset_closure (by simp)) _) (pow_mem (subset_closure (by simp)) _)
  have hall : ∀ x ∈ closure ({y₁, y₂} : Set M), ∃ i < 9, x = E i := by
    refine mem_of_enum ⟨0, by norm_num, by simp [hE]⟩ ?_
    intro i hi s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · refine ⟨3 * ((i / 3 + 1) % 3) + (i % 3) % 3, by omega, ?_⟩
      have := hmulE (i / 3) (i % 3) 1 0
      rw [pow_one, pow_zero, mul_one, add_zero] at this
      rw [hE] at *
      simp only at this ⊢
      rw [this, hE_eq]
    · refine ⟨3 * ((i / 3) % 3) + (i % 3 + 1) % 3, by omega, ?_⟩
      have := hmulE (i / 3) (i % 3) 0 1
      rw [pow_one, pow_zero, one_mul, add_zero] at this
      rw [hE] at *
      simp only at this ⊢
      rw [this, hE_eq]
  have hz1 : ∀ k < 3, y₂ ^ k ∈ zpowers y₁ → k = 0 := by
    intro k hk hmemk
    by_contra hk0
    apply hn
    have hk' : k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl
    · simpa using hmemk
    · have := pow_mem hmemk 2
      rw [← pow_mul, pow_mod_three h₂] at this
      simpa using this
  have hinj : ∀ i < 9, ∀ j < 9, E i = E j → i = j := by
    intro i hi j hj he
    simp only [hE] at he
    have h3 : y₂ ^ ((i % 3 + 2 * (j % 3)) % 3) ∈ zpowers y₁ := by
      have e1 : y₂ ^ (i % 3) * (y₂ ^ (j % 3))⁻¹ = (y₁ ^ (i / 3))⁻¹ * y₁ ^ (j / 3) := by
        rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← he, ← mul_assoc, inv_mul_cancel, one_mul]
      have e2 : y₂ ^ ((i % 3 + 2 * (j % 3)) % 3) = y₂ ^ (i % 3) * (y₂ ^ (j % 3))⁻¹ := by
        rw [← pow_mod_three h₂, pow_add, pow_mul]
        congr 1
        rw [inv_eq_of_mul_eq_one_right]
        rw [← pow_mul, ← pow_add]
        have : j % 3 + 2 * (j % 3) = 3 * (j % 3) := by ring
        rw [this, pow_mul, ← h₂, pow_orderOf_eq_one, one_pow]
      rw [e2, e1]
      exact mul_mem (inv_mem (pow_mem (mem_zpowers y₁) _)) (pow_mem (mem_zpowers y₁) _)
    have hb : i % 3 = j % 3 := by
      have := hz1 _ (Nat.mod_lt _ (by norm_num)) h3
      omega
    rw [hb, mul_left_inj] at he
    have ha : (i / 3) % 3 = (j / 3) % 3 := by
      rw [pow_mod_three h₁ (i / 3), pow_mod_three h₁ (j / 3)] at he
      exact pow_injOn_Iio_orderOf (by rw [h₁]; exact Nat.mod_lt _ (by norm_num))
        (by rw [h₁]; exact Nat.mod_lt _ (by norm_num)) he
    omega
  refine ⟨?_, ?_⟩
  · have hset : (closure ({y₁, y₂} : Set M) : Set M) =
        E '' ((Finset.range 9 : Finset ℕ) : Set ℕ) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, hi, rfl⟩ := hall x hx
        exact ⟨i, by simpa using hi, rfl⟩
      · rintro ⟨i, -, rfl⟩
        exact hmem i
    have hinj' : Set.InjOn E ((Finset.range 9 : Finset ℕ) : Set ℕ) := fun i hi j hj h =>
      hinj i (by simpa using hi) j (by simpa using hj) h
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, hinj'.ncard_image,
      Set.ncard_coe_finset, Finset.card_range]
  · intro y hy hy1
    obtain ⟨i, hi, rfl⟩ := hall y hy
    have hp : ∀ a b k : ℕ, (y₁ ^ a * y₂ ^ b) ^ k = y₁ ^ ((a * k) % 3) * y₂ ^ ((b * k) % 3) := by
      intro a b k
      rw [(hc.pow_pow a b).mul_pow, ← pow_mul, ← pow_mul, ← pow_mod_three h₁, ← pow_mod_three h₂]
    interval_cases i <;> simp only [hE, Nat.reduceDiv, Nat.reduceMod] at hy1 ⊢
    · simp at hy1
    · exact ⟨y₂, Or.inr (Or.inl rfl), ⟨1, by simp⟩⟩
    · refine ⟨y₂, Or.inr (Or.inl rfl), mem_zpowers_iff.mpr ⟨((2 : ℕ) : ℤ), ?_⟩⟩
      rw [zpow_natCast, hp 0 2 2]
      simp
    · exact ⟨y₁, Or.inl rfl, ⟨1, by simp⟩⟩
    · exact ⟨y₁ * y₂, Or.inr (Or.inr (Or.inl rfl)), ⟨1, by simp⟩⟩
    · exact ⟨y₁ * y₂ * y₂, Or.inr (Or.inr (Or.inr rfl)), ⟨1, by simp [sq, mul_assoc]⟩⟩
    · refine ⟨y₁, Or.inl rfl, mem_zpowers_iff.mpr ⟨((2 : ℕ) : ℤ), ?_⟩⟩
      rw [zpow_natCast, hp 2 0 2]
      simp
    · refine ⟨y₁ * y₂ * y₂, Or.inr (Or.inr (Or.inr rfl)), mem_zpowers_iff.mpr ⟨((2 : ℕ) : ℤ), ?_⟩⟩
      rw [zpow_natCast, hp 2 1 2]
      simp [sq, mul_assoc]
    · refine ⟨y₁ * y₂, Or.inr (Or.inr (Or.inl rfl)), mem_zpowers_iff.mpr ⟨((2 : ℕ) : ℤ), ?_⟩⟩
      rw [zpow_natCast, hp 2 2 2]
      simp

end CFSG.KS.HS2272

end
