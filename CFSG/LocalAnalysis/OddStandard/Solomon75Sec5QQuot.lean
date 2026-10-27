module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QLift
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5FinalGroup
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5BaseTools

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

theorem odd_card_of_forall_odd_orderOf {G : Type*} [Group G] [Finite G]
    (h : ∀ g : G, Odd (orderOf g)) : Odd (Nat.card G) := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  have h2 : 2 ∣ Nat.card G := by
    rcases Nat.even_or_odd (Nat.card G) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hcon
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have := h x
  rw [hx] at this
  exact absurd this (by decide)

theorem Qz_structure_abstract {X : Type} [Group X] [Finite X] (Q O : Subgroup X) (z : X)
    (hOQ : O ≤ Q) (hOn : ∀ q ∈ Q, q ∈ normalizer (O : Set X)) (hOodd : Odd (Nat.card O))
    (hzQ : z ∈ Q) (hz2 : orderOf z = 2) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hall : ∀ q ∈ Q, ∀ j : ℕ, q ^ (2 ^ j) ∈ O → q ∈ O ⊔ zpowers z)
    (hno : ∀ B : Subgroup X, B ≤ Q → (∀ q ∈ Q, q ∈ normalizer (B : Set X)) →
      Odd (Nat.card B) → B ≤ O) :
    Q = O ⊔ zpowers z ∧ Nat.card Q = 2 * Nat.card O := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N₀ : Subgroup ↥Q := O.subgroupOf Q with hN₀
  have hnorm : N₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOQ).2 hOn
  let f : ↥Q →* ↥Q ⧸ N₀ := QuotientGroup.mk' N₀
  let z' : ↥Q := ⟨z, hzQ⟩
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hf1 : ∀ q : ↥Q, f q = 1 ↔ (q : X) ∈ O := fun q => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hzO : z ∉ O := fun hz => by
    have := eq_one_of_sq_eq_one_of_mem_odd hOodd hz hzz
    rw [this, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hz'1 : f z' ≠ 1 := fun h1 => hzO ((hf1 z').1 h1)
  have hz'ord : orderOf (f z') = 2 := by
    refine orderOf_eq_prime ?_ hz'1
    rw [sq, ← map_mul]
    exact (hf1 _).2 (by simp [z', hzz])
  have hz'c : ∀ g : ↥Q ⧸ N₀, g * f z' = f z' * g := fun g => by
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
    show f q * f z' = f z' * f q
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc q q.2)
  have hnormZ : zpowers z ≤ normalizer (O : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hOn z hzQ
  have hallG : ∀ g : ↥Q ⧸ N₀, (∃ j : ℕ, g ^ (2 ^ j) = 1) → g ∈ zpowers (f z') := by
    intro g ⟨j, hj⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective g
    have hq : (q : X) ^ (2 ^ j) ∈ O := by
      have h1 : f (q ^ (2 ^ j)) = 1 := by rw [map_pow]; exact hj
      have := (hf1 _).1 h1
      simpa using this
    obtain ⟨o, ho, w, hw, hqow⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormZ
      (hall q q.2 j hq)
    obtain ⟨e, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hoQ : o ∈ Q := hOQ ho
    have hweQ : z ^ e ∈ Q := Subgroup.zpow_mem _ hzQ e
    have hqeq : q = ⟨o, hoQ⟩ * ⟨z ^ e, hweQ⟩ := Subtype.ext hqow
    have hfo : f ⟨o, hoQ⟩ = 1 := (hf1 _).2 ho
    have hfz : f ⟨z ^ e, hweQ⟩ = f z' ^ e := by
      rw [← map_zpow]
      congr 1
    show f q ∈ zpowers (f z')
    rw [hqeq, map_mul, hfo, one_mul, hfz]
    exact Subgroup.zpow_mem_zpowers _ _
  have hcard : (Nat.card (↥Q ⧸ N₀)).factorization 2 = 1 :=
    factorization_two_eq_one_of_hall hz'ord hallG
  obtain ⟨Ō, hŌn, hŌodd, hŌ⟩ := exists_normal_complement_of_central_involution hz'ord hz'c hcard
  have hŌbot : Ō = ⊥ := by
    set N : Subgroup ↥Q := Ō.comap f with hN
    set NX : Subgroup X := N.map Q.subtype with hNX
    have hNXQ : NX ≤ Q := Subgroup.map_subtype_le _
    have hNXn : ∀ q ∈ Q, q ∈ normalizer (NX : Set X) := by
      intro q hq
      have key : ∀ (q' : ↥Q) (y : X), y ∈ NX → (q' : X) * y * (q' : X)⁻¹ ∈ NX := by
        intro q' y hy
        obtain ⟨m, hm, rfl⟩ := hy
        refine ⟨q' * m * q'⁻¹, ?_, by simp⟩
        show f (q' * m * q'⁻¹) ∈ Ō
        rw [map_mul, map_mul, map_inv]
        exact hŌn.conj_mem _ hm _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact key ⟨q, hq⟩ y
      · intro hy
        have := key ⟨q, hq⟩⁻¹ _ hy
        simpa [mul_assoc] using this
    have hNXodd : Odd (Nat.card NX) := by
      refine odd_card_of_forall_odd_orderOf fun y => ?_
      obtain ⟨y, hy⟩ := y
      rw [Subgroup.orderOf_mk]
      obtain ⟨m, hm, rfl⟩ := hy
      show Odd (orderOf (m : X))
      have hm' : f m ∈ Ō := hm
      have hd : Odd (orderOf (f m)) := by
        have h1 : orderOf (⟨f m, hm'⟩ : Ō) ∣ Nat.card Ō := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hŌodd h1
      set d := orderOf (f m) with hd'
      have hmd : (m ^ d : ↥Q) ∈ N₀ := by
        have : f (m ^ d) = 1 := by rw [map_pow]; exact pow_orderOf_eq_one _
        exact (QuotientGroup.eq_one_iff _).1 this
      have hmdO : ((m : X) ^ d) ∈ O := by
        have := Subgroup.mem_subgroupOf.1 hmd
        simpa using this
      have he : Odd (orderOf ((m : X) ^ d)) := by
        have h1 : orderOf (⟨(m : X) ^ d, hmdO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Odd.of_dvd_nat hOodd h1
      have hdiv : orderOf (m : X) ∣ d * orderOf ((m : X) ^ d) := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [pow_mul, pow_orderOf_eq_one]
      have hodd : Odd (d * orderOf ((m : X) ^ d)) := hd.mul he
      exact Odd.of_dvd_nat hodd hdiv
    have hNXO : NX ≤ O := hno NX hNXQ hNXn hNXodd
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    have hmN : m ∈ N := hg
    have : ((m : ↥Q) : X) ∈ O := hNXO ⟨m, hmN, rfl⟩
    exact Subgroup.mem_bot.2 ((hf1 m).2 this)
  have hG2 : ∀ g : ↥Q ⧸ N₀, g = 1 ∨ g = f z' := by
    intro g
    rcases hŌ g with h1 | h1
    · left
      rw [hŌbot] at h1
      exact Subgroup.mem_bot.1 h1
    · right
      rw [hŌbot] at h1
      have h2 : g * f z' = 1 := Subgroup.mem_bot.1 h1
      have h3 : f z' * f z' = 1 := by
        rw [← map_mul]
        exact (hf1 _).2 (by simp [z', hzz])
      calc g = g * (f z' * f z') := by rw [h3, mul_one]
        _ = (g * f z') * f z' := by group
        _ = f z' := by rw [h2, one_mul]
  have hsup : Q = O ⊔ zpowers z := by
    apply le_antisymm
    · intro q hq
      rcases hG2 (f ⟨q, hq⟩) with h1 | h1
      · exact Subgroup.mem_sup_left ((hf1 _).1 h1)
      · have h2 : f (z'⁻¹ * ⟨q, hq⟩) = 1 := by rw [map_mul, map_inv, h1]; group
        have h3 : z⁻¹ * q ∈ O := by
          have := (hf1 _).1 h2
          simpa [z'] using this
        have : q = (z⁻¹ * q) * z := by
          have hc := hzc q hq
          calc q = z⁻¹ * (z * q) := by group
            _ = z⁻¹ * (q * z) := by rw [← hc]
            _ = (z⁻¹ * q) * z := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h3) (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers z))
    · exact sup_le hOQ ((Subgroup.zpowers_le).2 hzQ)
  refine ⟨hsup, ?_⟩
  have hc1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N₀
  have hc2 : Nat.card (↥Q ⧸ N₀) = 2 := by
    refine (Nat.card_eq_two_iff' (1 : ↥Q ⧸ N₀)).2 ⟨f z', hz'1, fun y hy => ?_⟩
    rcases hG2 y with h | h
    · exact absurd h hy
    · exact h
  have hc3 : Nat.card N₀ = Nat.card O := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOQ).toEquiv
  rw [hc1, hc2, hc3]

theorem exists_pow_mul_eq {X : Type*} [Group X] {O : Subgroup X} {q p : X}
    (hq : q ∈ normalizer (O : Set X)) (hp : p ∈ O) (k : ℕ) :
    ∃ o ∈ O, (q * p) ^ k = q ^ k * o := by
  induction k with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨o, ho, hk⟩ := ih
    have hq' : q⁻¹ ∈ normalizer (O : Set X) := Subgroup.inv_mem _ hq
    have h1 : q⁻¹ * o * q ∈ O := by
      have := (Subgroup.mem_normalizer_iff.1 hq' o).1 ho
      simpa using this
    refine ⟨(q⁻¹ * o * q) * p, Subgroup.mul_mem _ h1 hp, ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem hall_of_centralizer {X : Type} [Group X] [Finite X] (Q O : Subgroup X) (z s : X)
    (hOQ : O ≤ Q) (hOn : ∀ q ∈ Q, q ∈ normalizer (O : Set X)) (hOodd : Odd (Nat.card O))
    (hz : orderOf z = 2) (hs2 : s * s = 1) (hsO : s ∈ normalizer (O : Set X))
    (hcomm : ∀ q ∈ Q, q⁻¹ * (s * q * s⁻¹) ∈ O)
    (hP : ∀ x ∈ Q, x * s = s * x → ∀ j : ℕ, x ^ (2 ^ j) = 1 → x ∈ zpowers z) :
    ∀ q ∈ Q, ∀ j : ℕ, q ^ (2 ^ j) ∈ O → q ∈ O ⊔ zpowers z := by
  intro q hq j hqj
  have hs2' : s ^ (2 ^ 1) = 1 := by rw [pow_one, sq]; exact hs2
  obtain ⟨p, hp, hsp⟩ := exists_fixed_mem_coset hOodd hs2' hsO (hcomm q hq)
  have hpQ : p ∈ Q := hOQ hp
  have hxQ : q * p ∈ Q := Subgroup.mul_mem _ hq hpQ
  have hxs : (q * p) * s = s * (q * p) := by
    calc (q * p) * s = (s * (q * p) * s⁻¹) * s := by rw [hsp]
      _ = s * (q * p) := by group
  have hxj : (q * p) ^ (2 ^ (j + 1)) ∈ O := by
    obtain ⟨o, ho, hk⟩ := exists_pow_mul_eq (hOn q hq) hp (2 ^ (j + 1))
    have e : q ^ (2 ^ (j + 1)) = (q ^ (2 ^ j)) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [hk, e]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hqj 2) ho
  obtain ⟨u, v, hu, hv, huv, ⟨i, hi⟩, hvodd⟩ := exists_twoPart (q * p)
  have huQ : u ∈ Q := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact Subgroup.zpow_mem _ hxQ k
  have hus : u * s = s * u := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    exact (Commute.zpow_left (show Commute (q * p) s from hxs) k).eq
  have huz : u ∈ zpowers z := hP u huQ hus i hi
  have huu : u ^ (2 ^ (j + 1)) = 1 := by
    rcases (mem_zpowers_iff_of_orderOf_two hz).1 huz with h1 | h1
    · rw [h1, one_pow]
    · have hzsq : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      rw [h1, pow_succ', pow_mul, hzsq, one_pow]
  have huv' : u * v = v * u := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow_self (q * p) k l).eq
  have hvO : v ∈ O := by
    have h1 : v ^ (2 ^ (j + 1)) ∈ O := by
      have : (q * p) ^ (2 ^ (j + 1)) = v ^ (2 ^ (j + 1)) := by
        rw [huv, (Commute.mul_pow (show Commute u v from huv') _), huu, one_mul]
      rw [← this]
      exact hxj
    have hcop : Nat.Coprime (2 ^ (j + 1)) (orderOf v) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hvodd)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact Subgroup.pow_mem _ h1 m
  have hqx : q = u * v * p⁻¹ := by rw [← huv]; group
  rw [hqx]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right huz)
    (Subgroup.mem_sup_left hvO)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hp))

end CFSG.OddStandard.Solomon75
