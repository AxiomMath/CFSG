module

public import CFSG.ClassicalInvolution.Q3.TL4SepMin

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem T4Hyp.gen (h : T4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) :
    Subgroup.closure {x : G | x ∈ J ∧ IsPGroup 2 (Subgroup.zpowers x)} = J := by
  rcases h.hyp.omega2 J hJ with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨e⟩ := h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((h.twoGroup J hJ).of_equiv e)
    rw [natCard_sl2Three] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem mem_of_isPGroup_of_ne_bot {J P : Subgroup G} {u : G} (hu : IsUniqueInvolution J u)
    (hPJ : P ≤ J) (hP : IsPGroup 2 P) (hne : P ≠ ⊥) : u ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card P := by
    rcases hP.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hne
    · exact h
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hwo : orderOf w = 2 := by
    rw [← Subgroup.orderOf_mk w hw]
    exact hw2
  have hww : w * w = 1 := by rw [← pow_two, ← hwo, pow_orderOf_eq_one]
  have hw1 : w ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hwo
    omega
  rcases hu.unique w (hPJ hw) hww with h | h
  · exact absurd h hw1
  · exact h ▸ hw

theorem T4Hyp.le_centralizer_of_not_mem (h : T4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) {X : Subgroup G} (hX : X.Normal) (huX : u ∉ X) :
    J ≤ Subgroup.centralizer (X : Set G) := by
  have hOX : oddCoreOf X = ⊥ := by
    rw [oddCoreOf, oddCore_eq_bot_of_normal h.odd hX, Subgroup.map_bot]
  rw [← h.gen hJ, Subgroup.closure_le]
  rintro x ⟨hxJ, hx2⟩
  obtain ⟨T, hT, hTJ, hxT⟩ := exists_mem_RSet_ge hJ hx2 (Subgroup.zpowers_le.mpr hxJ)
  have hTX : T ⊓ X = ⊥ := by
    by_contra hne
    exact huX (mem_of_isPGroup_of_ne_bot hu (inf_le_left.trans hTJ.1)
      (hTJ.2.1.to_le inf_le_left) hne).2
  have hc := comm613Gen_normal h.hyp hT hX hTX
  rw [hOX, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  exact hc (hxT (Subgroup.mem_zpowers x))

variable {J L : Subgroup G}

end CFSG.ClassicalInvolution.Q3.TL4
