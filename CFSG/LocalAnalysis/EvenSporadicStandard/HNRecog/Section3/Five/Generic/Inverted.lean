module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

theorem orderOf_dvd_of_commute_of_inverted {a ρ : G} (ha : a * a = 1) (hinv : a * ρ * a = ρ⁻¹)
    (hodd : Odd (orderOf ρ)) {k : ℕ} (hk : a * ρ ^ k = ρ ^ k * a) : orderOf ρ ∣ k := by
  have hac : a * ρ = ρ⁻¹ * a := by
    have h := congrArg (· * a) hinv
    simpa [mul_assoc, ha] using h
  have hsc : a * ρ ^ k = (ρ⁻¹) ^ k * a := (SemiconjBy.pow_right hac k).eq
  have hcancel : (ρ⁻¹) ^ k = ρ ^ k := by
    have h : (ρ⁻¹) ^ k * a = ρ ^ k * a := by rw [← hsc, hk]
    exact mul_right_cancel h
  have h : (ρ ^ k)⁻¹ = ρ ^ k := by rw [← inv_pow, hcancel]
  have hsq : ρ ^ k * ρ ^ k = 1 := by
    rw [mul_eq_one_iff_eq_inv]
    exact h.symm
  have h2 : ρ ^ (2 * k) = 1 := by
    rw [two_mul, pow_add]
    exact hsq
  exact (hodd.coprime_two_right).dvd_of_dvd_mul_left (orderOf_dvd_of_pow_eq_one h2)

theorem card_sup_zpowers_of_inverted {L : Subgroup G} [Finite L] {a ρ : G} (ha : a * a = 1)
    (hinv : a * ρ * a = ρ⁻¹) (hodd : Odd (orderOf ρ)) (hρ : ∀ l ∈ L, l * ρ = ρ * l)
    (haL : ∀ l ∈ L, l * a = a * l) :
    Nat.card ↥(L ⊔ Subgroup.zpowers ρ) = Nat.card ↥L * orderOf ρ := by
  refine card_sup_zpowers_of_commute (g := ρ) hodd.pos hρ ?_
  intro k hk hmem
  exact hk (orderOf_dvd_of_commute_of_inverted ha hinv hodd (haL _ hmem).symm)

theorem mem_of_mul_self_eq_one_of_mem_sup {L : Subgroup G} {a ρ : G} (ha : a * a = 1)
    (hinv : a * ρ * a = ρ⁻¹) (hodd : Odd (orderOf ρ)) (hρ : ∀ l ∈ L, l * ρ = ρ * l)
    (haL : ∀ l ∈ L, l * a = a * l) {t : G} (ht : t ∈ L ⊔ Subgroup.zpowers ρ) (ht2 : t * t = 1) :
    t ∈ L := by
  classical
  have hpos : 0 < orderOf ρ := hodd.pos
  have hfin : IsOfFinOrder ρ := orderOf_pos_iff.mp hpos
  have hcomm : ∀ l ∈ L, ∀ w ∈ Subgroup.zpowers ρ, l * w = w * l := by
    intro l hl w hw
    obtain ⟨k, hkw⟩ :=
      (Submonoid.mem_powers_iff w ρ).mp ((hfin.mem_powers_iff_mem_zpowers).mpr hw)
    rw [← hkw]
    exact Commute.pow_right (hρ l hl) k
  have hcent : L ≤ Subgroup.centralizer (Subgroup.zpowers ρ : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (hcomm l hl w hw).symm
  have hnorm : L ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have ht' : t ∈ (↑(L ⊔ Subgroup.zpowers ρ) : Set G) := ht
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L (Subgroup.zpowers ρ) hnorm] at ht'
  obtain ⟨l, hl, w, hw, hlw⟩ := ht'
  obtain ⟨k, hkw⟩ :=
    (Submonoid.mem_powers_iff w ρ).mp ((hfin.mem_powers_iff_mem_zpowers).mpr hw)
  have hlw' : t = l * ρ ^ k := by rw [← hlw, hkw]
  have hcommk : l * ρ ^ k = ρ ^ k * l := by
    rw [hkw]
    exact hcomm l hl w hw
  have ht2' : l * ρ ^ k * (l * ρ ^ k) = 1 := by
    rw [← hlw']
    exact ht2
  have hsq : (l * l) * ρ ^ (2 * k) = 1 := by
    have hpow : (l * ρ ^ k) ^ 2 = (l * l) * ρ ^ (2 * k) := by
      rw [Commute.mul_pow hcommk 2, pow_two, pow_two, ← pow_add, two_mul]
    rw [← hpow, pow_two]
    exact ht2'
  have hρ2 : ρ ^ (2 * k) = (l * l)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have hmem2 : ρ ^ (2 * k) ∈ L := by
    rw [hρ2]
    exact L.inv_mem (L.mul_mem hl hl)
  have hdvd2 : orderOf ρ ∣ 2 * k :=
    orderOf_dvd_of_commute_of_inverted ha hinv hodd (haL _ hmem2).symm
  have hdvd : orderOf ρ ∣ k := (hodd.coprime_two_right).dvd_of_dvd_mul_left hdvd2
  have hρk : ρ ^ k = 1 := (orderOf_dvd_iff_pow_eq_one).mp hdvd
  rw [hlw', hρk, mul_one]
  exact hl

end CFSG.EvenSporadicStandard.HNRecog.Section3
