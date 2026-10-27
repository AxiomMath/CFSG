module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions

public section

namespace CFSG.ComponentClassification.Foote5.L34Group

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open scoped commutatorElement

theorem commute_of_card_dvd_three {G : Type*} [Group G] {H : Subgroup G}
    (h : Nat.card H ∣ 3) {a b : G} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a := by
  rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h3
  · have : Subsingleton H := (Nat.card_eq_one_iff_unique.mp h1).1
    have := Subsingleton.elim (⟨a, ha⟩ : H) ⟨b, hb⟩
    rw [show a = b from congrArg Subtype.val this]
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := isCyclic_of_prime_card h3
    let := IsCyclic.commGroup (α := H)
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : H) ⟨b, hb⟩)

theorem dvd_of_odd_of_dvd_four_mul {n m : ℕ} (hn : Odd n) (h : n ∣ 4 * m) : n ∣ m := by
  have hcop : Nat.Coprime n (2 ^ 2) := Nat.Coprime.pow_right 2 (Nat.coprime_two_left.mpr hn).symm
  exact hcop.dvd_of_dvd_mul_left (by simpa using h)

theorem card_dvd_three_mul {A : Subgroup (Equiv.Perm (Fin 42))}
    (hAR : A ≤ R) (hodd : Odd (Nat.card A)) : Nat.card A ∣ 3 * Nat.card ↥(A ⊓ S) := by
  have := S_normal
  let φ : ↥(A.subgroupOf R) →* ↥R ⧸ S.subgroupOf R :=
    (QuotientGroup.mk' (S.subgroupOf R)).comp (A.subgroupOf R).subtype
  have hφ : ∀ x : ↥(A.subgroupOf R), φ x = 1 ↔ ((x : R) : Equiv.Perm (Fin 42)) ∈ S := fun x => by
    change (QuotientGroup.mk ((x : R)) : ↥R ⧸ S.subgroupOf R) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    rfl
  have hcard : Nat.card A = Nat.card (A.subgroupOf R) :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).symm
  have hker : Nat.card φ.ker = Nat.card ↥(A ⊓ S) := by
    refine Nat.card_congr ⟨fun x => ⟨((x : ↥(A.subgroupOf R)) : R),
      mem_inf.mpr ⟨(x : ↥(A.subgroupOf R)).2, (hφ _).mp x.2⟩⟩,
      fun x => ⟨⟨⟨x, hAR (mem_inf.mp x.2).1⟩, (mem_inf.mp x.2).1⟩, (hφ _).mpr (mem_inf.mp x.2).2⟩,
      fun x => rfl, fun x => rfl⟩
  have hR : Nat.card (↥R ⧸ S.subgroupOf R) = 12 := by
    have h := card_eq_card_quotient_mul_card_subgroup (S.subgroupOf R)
    rw [card_R, Nat.card_congr (subgroupOfEquivOfLe S_le_R).toEquiv, card_S] at h
    omega
  have hmul := card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker] at hmul
  have hrange : Nat.card φ.range ∣ 4 * 3 := by
    have h := card_subgroup_dvd_card φ.range
    rw [hR] at h
    exact h
  have hrodd : Odd (Nat.card φ.range) :=
    Odd.of_dvd_nat (hcard ▸ hodd) (by rw [hmul]; exact dvd_mul_right _ _)
  have h3 : Nat.card φ.range ∣ 3 := dvd_of_odd_of_dvd_four_mul hrodd hrange
  rw [hcard, hmul]
  exact mul_dvd_mul_right h3 _

theorem commute_of_mem_derived {a b : Equiv.Perm (Fin 42)}
    (ha : a ∈ ambientDerived C₄ 2) (hb : b ∈ ambientDerived C₄ 2) : a * b = b * a := by
  have h3 : ambientDerived C₄ 3 = ⊥ := by
    rw [← card_eq_one, ← card_derivedSeries]
    exact card_derivedSeries_C₄.2.2.2
  have hc : ⁅a, b⁆ ∈ ambientDerived C₄ 3 := commutator_mem_commutator ha hb
  rw [h3, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem le_derived_of_odd {P : Subgroup (Equiv.Perm (Fin 42))}
    (hP : P ≤ C₄) (hodd : Odd (Nat.card P)) : P ≤ ambientDerived C₄ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD9 : Nat.card (derivedSeries C₄ 2) = 9 := by
    rw [card_derivedSeries]
    rw [← card_derivedSeries]
    exact card_derivedSeries_C₄.2.2.1
  have hC72 : Nat.card C₄ = 4 * 18 := card_C₄
  have hpow : ∀ {n : ℕ}, Odd n → n ∣ 4 * 18 → ∃ i : ℕ, n = 3 ^ i := by
    intro n hn h
    have h18 : n ∣ 2 * 9 := dvd_of_odd_of_dvd_four_mul hn h
    have h9 : n ∣ 3 ^ 2 := by
      have hcop : Nat.Coprime n 2 := (Nat.coprime_two_left.mpr hn).symm
      simpa using hcop.dvd_of_dvd_mul_left h18
    obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
    exact ⟨i, he⟩
  set P' := P.subgroupOf C₄ with hP'
  have hP'card : Nat.card P' = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hP).toEquiv
  obtain ⟨i, hi⟩ := hpow (hP'card ▸ hodd) (hC72 ▸ card_subgroup_dvd_card P')
  have hPp : IsPGroup 3 P' := IsPGroup.of_card hi
  have hDp : IsPGroup 3 (derivedSeries C₄ 2) := IsPGroup.of_card (n := 2) (by rw [hD9]; rfl)
  have hsup := hPp.to_sup_of_normal_right hDp
  obtain ⟨k, hk⟩ := hsup.exists_card_eq
  have hodd' : Odd (Nat.card ↥(P' ⊔ derivedSeries C₄ 2)) := by
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨j, hj⟩ := hpow hodd' (hC72 ▸ card_subgroup_dvd_card _)
  have hle9 : Nat.card ↥(P' ⊔ derivedSeries C₄ 2) ≤ 9 := by
    have hdvd : Nat.card ↥(P' ⊔ derivedSeries C₄ 2) ∣ 72 :=
      (show Nat.card C₄ = 72 from card_C₄) ▸ card_subgroup_dvd_card _
    rw [hj] at hdvd ⊢
    have hj2 : j ≤ 2 := by
      by_contra hj2
      have h27 : 27 ∣ 72 := (pow_dvd_pow 3 (by omega : 3 ≤ j)).trans hdvd
      omega
    calc 3 ^ j ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hj2
      _ = 9 := by norm_num
  have heq : derivedSeries C₄ 2 = P' ⊔ derivedSeries C₄ 2 :=
    eq_of_le_of_card_ge le_sup_right (by rw [hD9]; exact hle9)
  intro x hx
  have hx' : (⟨x, hP hx⟩ : C₄) ∈ derivedSeries C₄ 2 := heq ▸ mem_sup_left hx
  rw [← map_derivedSeries]
  exact ⟨_, hx', rfl⟩

end CFSG.ComponentClassification.Foote5.L34Group
