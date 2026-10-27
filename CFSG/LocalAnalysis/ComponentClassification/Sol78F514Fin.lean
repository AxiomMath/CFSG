module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicOddCoreBasic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F514Tight

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ABGLocalTools CFSG.Open CFSG.ComponentClassification.RankTwoSporadic

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem eq_one_of_mem_odd_of_pow {N : Subgroup Y} (hN : Odd (Nat.card N)) {x : Y} (hx : x ∈ N)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  have hodd := Odd.of_dvd_nat hN (Subgroup.orderOf_dvd_natCard N hx)
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  · rw [hj] at hodd
    exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, Nat.succ_ne_zero j⟩))

theorem false_of_mem_pCore {T R : Subgroup Y} {z d h u : Y} (hd2 : d * d = 1)
    (hdc : ∀ x : Y, x * d = d * x) (hT : IsSylowOf 2 T ⊤)
    (hzT : ∀ x ∈ T, x⁻¹ * z * x = z ∨ x⁻¹ * z * x = z * d) (hR : IsPGroup 2 R) (hdR : d ∉ R)
    (hyR : ∀ r ∈ R, (h⁻¹ * z * h) * r * (h⁻¹ * z * h)⁻¹ ∈ R)
    (hfix : ∀ r ∈ R, r * (h⁻¹ * z * h) = (h⁻¹ * z * h) * r → r * r = 1) (huR : u ∈ R)
    (hu : QuotientGroup.mk' (standardComponentOddCore Y) u ∈
      CFSG.Open.pCore 2 (Y ⧸ standardComponentOddCore Y)) (hu2 : u * u ≠ 1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := standardComponentOddCore Y with hO
  have hOodd : Odd (Nat.card O) := odd_card_standardComponentOddCore
  set π := QuotientGroup.mk' O with hπ
  set P := CFSG.Open.pCore 2 (Y ⧸ O) with hP
  have hPn : P.Normal := LieType.BorelTits.pCore_normal 2
  have hPp : IsPGroup 2 P := LieType.BorelTits.pCore_isPGroup 2
  set y := h⁻¹ * z * h with hy
  have hTb : IsSylowOf 2 (T.map π) ⊤ := by
    have h1 := isSylowOf_map_mk hOodd hT
    rwa [Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective O)] at h1
  have hPT : P ≤ T.map π := by
    have hsup : IsPGroup 2 ↥(T.map π ⊔ P) := IsPGroup.to_sup_of_normal_right' hTb.isPGroup hPp
      fun x _ => mem_normalizer_iff.mpr fun q => ⟨fun hq => hPn.conj_mem q hq x, fun hq => by
        have h1 := hPn.conj_mem _ hq x⁻¹
        rwa [show x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q by group] at h1⟩
    exact le_sup_right.trans (hTb.eq_of_le le_sup_left le_top hsup).le
  have hdc' : ∀ q : Y ⧸ O, q * π d = π d * q := by
    intro q
    obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective O q
    rw [← map_mul, ← map_mul, hdc]
  have hzP : ∀ p ∈ P, p⁻¹ * π z * p = π z ∨ p⁻¹ * π z * p = π z * π d := by
    intro p hp
    obtain ⟨x, hxT, rfl⟩ := hPT hp
    rcases hzT x hxT with h1 | h1
    · left
      rw [← map_inv, ← map_mul, ← map_mul, h1]
    · right
      rw [← map_inv, ← map_mul, ← map_mul, h1, map_mul]
  have hyP : ∀ p ∈ P, p⁻¹ * π y * p = π y ∨ p⁻¹ * π y * p = π y * π d := by
    intro p hp
    have hp' : π h * p * (π h)⁻¹ ∈ P := hPn.conj_mem p hp (π h)
    have he : p⁻¹ * π y * p =
        (π h)⁻¹ * ((π h * p * (π h)⁻¹)⁻¹ * π z * (π h * p * (π h)⁻¹)) * π h := by
      rw [hy, map_mul, map_mul, map_inv]
      group
    rcases hzP _ hp' with h1 | h1
    · left
      rw [he, h1, hy, map_mul, map_mul, map_inv]
    · right
      rw [he, h1, hy, map_mul, map_mul, map_inv]
      calc (π h)⁻¹ * (π z * π d) * π h = (π h)⁻¹ * π z * (π d * π h) := by group
        _ = (π h)⁻¹ * π z * (π h * π d) := by rw [hdc' (π h)]
        _ = (π h)⁻¹ * π z * π h * π d := by group
  set c := u⁻¹ * (y * u * y⁻¹) with hc
  have hcR : c ∈ R := mul_mem (inv_mem huR) (hyR u huR)
  have hc' : π c = 1 ∨ π c = π d := by
    have he : π c = (π u)⁻¹ * π y * π u * (π y)⁻¹ := by
      rw [hc, map_mul, map_inv, map_mul, map_mul, map_inv]
      group
    rcases hyP _ hu with h1 | h1
    · left
      rw [he, h1, mul_inv_cancel]
    · right
      rw [he, h1, mul_assoc (π y), ← hdc' (π y)⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
  obtain ⟨k, hk⟩ := hR ⟨c, hcR⟩
  have hck : c ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h1
  have hc1 : c = 1 := by
    rcases hc' with h1 | h1
    · exact eq_one_of_mem_odd_of_pow hOodd ((QuotientGroup.eq_one_iff c).mp h1) hck
    · exfalso
      have h2 : c⁻¹ * d ∈ O := QuotientGroup.eq.mp h1
      have h3 : (c⁻¹ * d) ^ 2 ^ (k + 1) = 1 := by
        have hcd : Commute c⁻¹ d := hdc c⁻¹
        have hdk : d ^ 2 ^ (k + 1) = 1 := by rw [pow_succ', pow_mul, sq, hd2, one_pow]
        have hck' : c⁻¹ ^ 2 ^ (k + 1) = 1 := by
          rw [pow_succ, pow_mul, inv_pow, hck, inv_one, one_pow]
        rw [hcd.mul_pow, hck', hdk, one_mul]
      have h4 := eq_one_of_mem_odd_of_pow hOodd h2 h3
      apply hdR
      rw [show d = c * (c⁻¹ * d) by group, h4, mul_one]
      exact hcR
  apply hu2
  apply hfix u huR
  have h1 : y * u * y⁻¹ = u := by
    calc y * u * y⁻¹ = u * c := by rw [hc]; group
      _ = u := by rw [hc1, mul_one]
  calc u * y = y * u * y⁻¹ * y := by rw [h1]
    _ = y * u := by group

end CFSG.ComponentClassification.Sol78.F514
