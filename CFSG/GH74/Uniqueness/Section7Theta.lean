module

public import CFSG.GH74.Uniqueness.Section6Defs

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Section7Theta

omit [Finite X] in
theorem oPrimePrime_eq_corollary64Theta (p : ℕ) (D : Subgroup X) :
    oPrimePrime p D = CFSG.BenderSuzuki.corollary64Theta p D := rfl

omit [Finite X] in
theorem oPrimePrime_le_pPrimeCoreIn (p : ℕ) (D : Subgroup X) : oPrimePrime p D ≤ pPrimeCoreIn D :=
  Subgroup.map_subtype_le _

omit [Finite X] in
theorem oPrimePrime_le (p : ℕ) (D : Subgroup X) : oPrimePrime p D ≤ D :=
  (oPrimePrime_le_pPrimeCoreIn p D).trans (pPrimeCoreIn_le D)

theorem oPrimePrime_odd_card (p : ℕ) (D : Subgroup X) : Odd (Nat.card (oPrimePrime p D)) :=
  Odd.of_dvd_nat (odd_card_pPrimeCoreIn D)
    (Subgroup.card_dvd_of_le (oPrimePrime_le_pPrimeCoreIn p D))

theorem oPrimePrime_coprime_card {p : ℕ} (hp : p.Prime) (D : Subgroup X) :
    Nat.Coprime p (Nat.card (oPrimePrime p D)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [oPrimePrime, Subgroup.card_map_of_injective (pPrimeCoreIn D).subtype_injective]
  exact pPrimeCore_coprime_card

theorem mem_normalizer_oPrimePrime (p : ℕ) {D : Subgroup X} {g : X}
    (hg : g ∈ normalizer (D : Set X)) : g ∈ normalizer (oPrimePrime p D : Set X) :=
  CFSG.section8_normalizer_map_subtype_le_of_characteristic (H := pPrimeCoreIn D)
    (K := pPrimeCore p ↥(pPrimeCoreIn D)) (mem_normalizer_pPrimeCoreIn hg)

theorem le_normalizer_oPrimePrime (p : ℕ) (D : Subgroup X) :
    D ≤ normalizer (oPrimePrime p D : Set X) :=
  fun _ hg => mem_normalizer_oPrimePrime p (Subgroup.le_normalizer hg)

omit [Finite X] in
theorem le_oPrimePrime_of_le_pPrimeCoreIn {p : ℕ} {T D : Subgroup X} (hTD : T ≤ pPrimeCoreIn D)
    (hn : pPrimeCoreIn D ≤ normalizer (T : Set X)) (hcop : Nat.Coprime p (Nat.card T)) :
    T ≤ oPrimePrime p D := by
  have hN : (T.subgroupOf (pPrimeCoreIn D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTD).mpr hn
  have hc : Nat.Coprime p (Nat.card (T.subgroupOf (pPrimeCoreIn D))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTD).toEquiv]
    exact hcop
  have hle : T.subgroupOf (pPrimeCoreIn D) ≤ pPrimeCore p ↥(pPrimeCoreIn D) := le_sSup ⟨hN, hc⟩
  intro x hx
  exact ⟨⟨x, hTD hx⟩, hle hx, rfl⟩

theorem le_oPrimePrime_of_le_normalizer {p : ℕ} {T D : Subgroup X} (hTD : T ≤ D)
    (hn : D ≤ normalizer (T : Set X)) (hodd : Odd (Nat.card T))
    (hcop : Nat.Coprime p (Nat.card T)) : T ≤ oPrimePrime p D :=
  le_oPrimePrime_of_le_pPrimeCoreIn (le_pPrimeCoreIn hTD hn hodd)
    ((pPrimeCoreIn_le D).trans hn) hcop

omit [Finite X] in
theorem conjugate_pPrimeCoreIn (D : Subgroup X) (g : X) :
    conjugate (pPrimeCoreIn D) g = pPrimeCoreIn (conjugate D g) :=
  CFSG.BenderSuzuki.theorem4b_ambientPPrimeCore_conjBy 2 D g⁻¹

omit [Finite X] in
theorem conjugate_oPrimePrime (p : ℕ) (D : Subgroup X) (g : X) :
    conjugate (oPrimePrime p D) g = oPrimePrime p (conjugate D g) := by
  have h1 := CFSG.BenderSuzuki.theorem4b_ambientPPrimeCore_conjBy p (pPrimeCoreIn D) g⁻¹
  have h2 : (pPrimeCoreIn D).conjBy g⁻¹ = pPrimeCoreIn (conjugate D g) :=
    conjugate_pPrimeCoreIn D g
  rw [h2] at h1
  exact h1

omit [Finite X] in
theorem card_oPrimePrime_conjugate (p : ℕ) (D : Subgroup X) (g : X) :
    Nat.card (oPrimePrime p (conjugate D g)) = Nat.card (oPrimePrime p D) := by
  rw [← conjugate_oPrimePrime]
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem odd_card_sup_of_le_normalizer {A B : Subgroup X} (hAB : A ≤ normalizer (B : Set X))
    (hA : Odd (Nat.card A)) (hB : Odd (Nat.card B)) : Odd (Nat.card (A ⊔ B : Subgroup X)) := by
  by_contra hnot
  have h2 : 2 ∣ Nat.card ↥(A ⊔ B) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnot)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊔ B)) 2 h2
  have hxo : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxx : (x : X) * x = 1 := by rw [← sq, ← hxo, pow_orderOf_eq_one]
  have hxm : (x : X) ∈ ((A ⊔ B : Subgroup X) : Set X) := x.2
  rw [coe_mul_of_left_le_normalizer_right A B hAB] at hxm
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxm
  have hb' : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb
  have h3 : (a * b) * (a * b) = 1 := by rw [hab]; exact hxx
  have key : (a * b * a⁻¹) * (a * a) * b = 1 := by
    have : (a * b * a⁻¹) * (a * a) * b = (a * b) * (a * b) := by group
    rw [this]
    exact h3
  have ha2 : a * a ∈ B := by
    have e : a * a = (a * b * a⁻¹)⁻¹ * b⁻¹ := by
      calc a * a = (a * b * a⁻¹)⁻¹ * ((a * b * a⁻¹) * (a * a) * b) * b⁻¹ := by group
        _ = (a * b * a⁻¹)⁻¹ * b⁻¹ := by rw [key]; group
    rw [e]
    exact B.mul_mem (B.inv_mem hb') (B.inv_mem hb)
  have hao : Odd (orderOf a) := Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A ha)
  have haB : a ∈ B := mem_of_mul_self_mem_of_odd_orderOf hao ha2
  have hxB : (x : X) ∈ B := by rw [← hab]; exact B.mul_mem haB hb
  have : 2 ∣ Nat.card B := hxo ▸ Subgroup.orderOf_dvd_natCard B hxB
  exact hB.not_two_dvd_nat this

end Section7Theta

end CFSG.GH74.Uniqueness
