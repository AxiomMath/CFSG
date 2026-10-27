module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup
open scoped Pointwise

variable {X : Type} [Group X]

@[expose] def oddCoreIn (H : Subgroup X) : Subgroup X := (pPrimeCore 2 H).map H.subtype

theorem oddCoreIn_le (H : Subgroup X) : oddCoreIn H ≤ H := by
  rintro _ ⟨k, -, rfl⟩
  exact k.2

theorem mem_oddCoreIn_iff {H : Subgroup X} {x : X} :
    x ∈ oddCoreIn H ↔ ∃ h : H, h ∈ pPrimeCore 2 H ∧ (h : X) = x := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, hh, rfl⟩

theorem conj_mem_oddCoreIn {H : Subgroup X} {h : X} (hh : h ∈ H) {k : X} (hk : k ∈ oddCoreIn H) :
    h * k * h⁻¹ ∈ oddCoreIn H := by
  obtain ⟨k', hk', rfl⟩ := mem_oddCoreIn_iff.1 hk
  have := (pPrimeCore_normal (p := 2) (G := H)).conj_mem k' hk' ⟨h, hh⟩
  exact ⟨_, this, rfl⟩

theorem odd_orderOf_of_mem_oddCore [Finite X] {H : Subgroup X} {k : X} (hk : k ∈ oddCoreIn H) :
    Odd (orderOf k) := by
  obtain ⟨k', hk', rfl⟩ := mem_oddCoreIn_iff.1 hk
  have hdvd : orderOf k' ∣ Nat.card (pPrimeCore 2 H) := by
    rw [← Subgroup.orderOf_mk k' hk']
    exact orderOf_dvd_natCard _
  have hcop := Nat.Coprime.of_dvd_right hdvd (pPrimeCore_coprime_card (p := 2) (G := H))
  have : Odd (orderOf k') := Nat.coprime_two_left.mp hcop
  rwa [Subgroup.orderOf_coe]

theorem eq_one_of_mem_oddCore_of_two_power [Finite X] {H : Subgroup X} {k : X}
    (hk : k ∈ oddCoreIn H)
    {n : ℕ} (hn : k ^ (2 ^ n) = 1) : k = 1 := by
  have h1 : orderOf k ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 := odd_orderOf_of_mem_oddCore hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hi0 : i = 0 := by
    by_contra hne
    have : Even (orderOf k) := by
      rw [hi]
      exact Nat.even_pow.2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 h2) this
  rw [hi0, pow_zero] at hi
  exact orderOf_eq_one_iff.mp hi

theorem eq_one_of_mem_inf_oddCore [Finite X] {H P : Subgroup X} (hP : IsPGroup 2 P) {k : X}
    (hkP : k ∈ P)
    (hk : k ∈ oddCoreIn H) : k = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨k, hkP⟩
  have : k ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact eq_one_of_mem_oddCore_of_two_power hk this

theorem oddCoreIn_centralizes [Finite X] {H Q : Subgroup X} (hQ : IsPGroup 2 Q) (hQle : Q ≤ H)
    (hQH : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q) {k : X} (hk : k ∈ oddCoreIn H) {q : X}
    (hq : q ∈ Q) : k * q * k⁻¹ = q := by
  have hkH : k ∈ H := oddCoreIn_le H hk
  have h1 : k * q * k⁻¹ * q⁻¹ ∈ Q := Q.mul_mem (hQH k hkH q hq) (Q.inv_mem hq)
  have h2 : k * q * k⁻¹ * q⁻¹ ∈ oddCoreIn H := by
    have := (oddCoreIn H).mul_mem hk
      (conj_mem_oddCoreIn (hQle hq) ((oddCoreIn H).inv_mem hk))
    simpa [mul_assoc] using this
  have := eq_one_of_mem_inf_oddCore hQ h1 h2
  calc k * q * k⁻¹ = (k * q * k⁻¹ * q⁻¹) * q := by group
    _ = q := by rw [this, one_mul]

theorem mem_of_two_power_of_mem_sup {L K : Subgroup X} [L.Normal] (hK : ∀ k ∈ K, Odd (orderOf k))
    {y : X} (hy : y ∈ L ⊔ K) {n : ℕ} (hyn : y ^ (2 ^ n) = 1) : y ∈ L := by
  have hmul : ((L ⊔ K : Subgroup X) : Set X) = (L : Set X) * (K : Set X) := Subgroup.normal_mul L K
  obtain ⟨l, hl, k, hk, rfl⟩ : ∃ l ∈ L, ∃ k ∈ K, l * k = y := by
    have : y ∈ (L : Set X) * (K : Set X) := by rw [← hmul]; exact hy
    exact this
  set π := QuotientGroup.mk' L
  have hπl : π l = 1 := (QuotientGroup.eq_one_iff l).2 hl
  have hπk : π k = π (l * k) := by
    rw [map_mul, hπl, one_mul]
  have h1 : (π k) ^ (2 ^ n) = 1 := by
    have : π ((l * k) ^ (2 ^ n)) = 1 := by rw [hyn, map_one]
    rwa [map_pow, ← hπk] at this
  have h2 : orderOf (π k) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have h3 : Odd (orderOf (π k)) :=
    Odd.of_dvd_nat (hK k hk) (orderOf_map_dvd π k)
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
  have hi0 : i = 0 := by
    by_contra hne
    have : Even (orderOf (π k)) := by
      rw [hi]
      exact Nat.even_pow.2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 h3) this
  rw [hi0, pow_zero] at hi
  have hk1 : π k = 1 := orderOf_eq_one_iff.mp hi
  have hkL : k ∈ L := (QuotientGroup.eq_one_iff k).1 hk1
  exact L.mul_mem hl hkL

end CFSG.OddStandard.ThmC.Core
