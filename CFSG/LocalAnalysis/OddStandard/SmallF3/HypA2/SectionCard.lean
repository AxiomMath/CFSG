module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueBasic
public import CFSG.Milestones.ASVolI.I2Covers

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.ComponentClassification

theorem card_quot_fusionZStar_dvd {H : Type} [Group H] [Finite H] {T M : Subgroup H}
    (hTM : T ≤ M) (hT : HarrisLit.IsTwoQuasisimple ↥T) :
    Nat.card (↥T ⧸ Open.fusionZStar ↥T) ∣ Nat.card (↥M ⧸ Open.fusionZStar ↥M) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥T →* ↥M := Subgroup.inclusion hTM
  have hO : (pPrimeCore 2 ↥M).comap f ≤ pPrimeCore 2 ↥T := by
    refine le_sSup ⟨inferInstance, ?_⟩
    exact (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥M)).coprime_dvd_right
      (Subgroup.card_comap_dvd_of_injective (pPrimeCore 2 ↥M) f
        (Subgroup.inclusion_injective hTM))
  have hS : (Open.fusionZStar ↥M).comap f ≤ Open.fusionZStar ↥T := by
    rw [Sol78.fusionZStar_eq_comap ↥T]
    intro s hs
    rw [Subgroup.mem_comap] at hs ⊢
    rw [Sol78.fusionZStar_eq_comap ↥M] at hs
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥T) y
    rw [← map_mul, ← map_mul]
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_iff_div_mem]
    have hcomm : (g * s) / (s * g) = g * s * g⁻¹ * s⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev]
      simp only [mul_assoc]
    rw [hcomm]
    apply hO
    rw [Subgroup.mem_comap]
    refine (QuotientGroup.eq_one_iff (f (g * s * g⁻¹ * s⁻¹))).mp ?_
    change (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (f (g * s * g⁻¹ * s⁻¹)) = 1
    have hz := Subgroup.mem_center_iff.mp hs
    rw [show (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (f (g * s * g⁻¹ * s⁻¹)) =
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (f g) *
        (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (f s) *
        ((QuotientGroup.mk' (pPrimeCore 2 ↥M)) (f g))⁻¹ *
        ((QuotientGroup.mk' (pPrimeCore 2 ↥M)) (f s))⁻¹ by
      simp only [map_mul, map_inv]]
    rw [hz]
    group
  let φ : ↥T →* ↥M ⧸ Open.fusionZStar ↥M :=
    (QuotientGroup.mk' (Open.fusionZStar ↥M)).comp f
  have hk : φ.ker = (Open.fusionZStar ↥M).comap f := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_comap]
  have hker : φ.ker ≤ Open.fusionZStar ↥T := by rw [hk]; exact hS
  calc Nat.card (↥T ⧸ Open.fusionZStar ↥T) = (Open.fusionZStar ↥T).index :=
        (Subgroup.index_eq_card _).symm
    _ ∣ φ.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card φ.range := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    _ ∣ Nat.card (↥M ⧸ Open.fusionZStar ↥M) := Subgroup.card_subgroup_dvd_card _

theorem isPrimePow_of_isSLTwoOver {q : ℕ} {A : Type} [Group A] (h : HarrisLit.IsSLTwoOver q A) :
    IsPrimePow q := by
  obtain ⟨F, hF, hFt, hq, ⟨e⟩⟩ := h
  rw [← hq]
  exact Fintype.isPrimePow_card_of_field

theorem card_quot_fusionZStar_of_isSLTwoOver {q : ℕ} (hq : Odd q) {T : Type} [Group T]
    [Finite T] (h : HarrisLit.IsSLTwoOver q (T ⧸ pPrimeCore 2 T)) :
    Nat.card (T ⧸ Open.fusionZStar T) * 2 = q * (q ^ 2 - 1) := by
  have hQ : Nat.card (T ⧸ pPrimeCore 2 T) = q * (q ^ 2 - 1) :=
    GS82PumpInputs.Residue.card_of_isSLTwoOver h
  obtain ⟨F, hF, hFt, hqF, ⟨e⟩⟩ := h
  have h2 : (2 : F) ≠ 0 := by
    apply Ring.two_ne_zero
    intro hchar
    have hq_nat : Nat.card F = q := by rw [Nat.card_eq_fintype_card, hqF]
    have hmod : Nat.card F % 2 = 0 := by
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.even_card_of_char_two hchar
    rw [hq_nat] at hmod
    obtain ⟨k, hk⟩ := hq
    omega
  have hcenter : Nat.card (center (T ⧸ pPrimeCore 2 T)) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.ASVolI.burnsideI2a_natCard_center_sl2 h2
  have hcard : Nat.card (T ⧸ Open.fusionZStar T) =
      Nat.card ((T ⧸ pPrimeCore 2 T) ⧸ center (T ⧸ pPrimeCore 2 T)) :=
    (Nat.card_congr (Sol78.coreQuotientCenterEquiv T).toEquiv).symm
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (T ⧸ pPrimeCore 2 T))
  rw [hQ, hcenter] at hsplit
  rw [hcard]
  exact hsplit.symm

theorem card_lieModel_psl_two_three_two {S : Type} [Group S] (h : LieModel S .PSL 2 3 2) :
    Nat.card S = 360 := by
  rw [GH74.card_of_lieModel_PSL (by norm_num : (2 : ℕ) ≠ 0) h]
  decide

theorem card_lieModel_psp_two_three_one {S : Type} [Group S] (h : LieModel S .PSp 2 3 1) :
    Nat.card S = 25920 := by
  rw [GH74.card_of_lieModel_PSp (by norm_num : (2 : ℕ) ≠ 0) (by norm_num : (3 : ℕ) ≠ 2) h]
  decide

theorem card_lieModel_psl_three_two_two {S : Type} [Group S] (h : LieModel S .PSL 3 2 2) :
    Nat.card S = 20160 := by
  rw [GH74.card_of_lieModel_PSL (by norm_num : (3 : ℕ) ≠ 0) h]
  decide

private theorem not_isPrimePow_fifteen : ¬ IsPrimePow 15 := by
  rw [isPrimePow_iff_unique_prime_dvd]
  rintro ⟨p, hp, huniq⟩
  have h3 : (3 : ℕ).Prime ∧ 3 ∣ 15 := by norm_num
  have h5 : (5 : ℕ).Prime ∧ 5 ∣ 15 := by norm_num
  have h3p : (3 : ℕ) = p := huniq 3 h3
  have h5p : (5 : ℕ) = p := huniq 5 h5
  omega

theorem not_dvd_of_psl_card {q m n : ℕ} (hq : Odd q) (h9 : 9 ≤ q) (hm : m * 2 = q * (q ^ 2 - 1))
    (hn : n = 60 ∨ n = 168 ∨ n = 6048) : ¬ m ∣ n := by
  intro hdvd
  have hnpos : 0 < n := by rcases hn with rfl | rfl | rfl <;> norm_num
  have hmle : m ≤ n := Nat.le_of_dvd hnpos hdvd
  have hnle : n ≤ 6048 := by rcases hn with rfl | rfl | rfl <;> norm_num
  have hqle : q ≤ 23 := by
    by_contra h
    push Not at h
    have hq25 : 25 ≤ q := by
      obtain ⟨k, hk⟩ := hq
      omega
    have hq2 : 25 ^ 2 ≤ q ^ 2 := pow_le_pow_left' hq25 2
    have hsub : 624 ≤ q ^ 2 - 1 := by norm_num at hq2; omega
    have hbig : 25 * 624 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq25 hsub
    have h2m : q * (q ^ 2 - 1) = 2 * m := by rw [← hm]; ring
    omega
  have hqcases : q = 9 ∨ q = 11 ∨ q = 13 ∨ q = 15 ∨ q = 17 ∨ q = 19 ∨ q = 21 ∨ q = 23 := by
    obtain ⟨k, hk⟩ := hq
    omega
  rcases hqcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hmv : m = 360 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 660 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 1092 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 1680 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 2448 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 3420 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 4620 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)
  · have hmv : m = 6072 := by norm_num at hm; omega
    rcases hn with rfl | rfl | rfl <;> (rw [hmv] at hdvd <;> norm_num at hdvd)

theorem not_dvd_l34_of_psl_card {q m : ℕ} (hq : IsPrimePow q) (hodd : Odd q) (h11 : 11 ≤ q)
    (hm : m * 2 = q * (q ^ 2 - 1)) : ¬ m ∣ 20160 := by
  intro hdvd
  have hmle : m ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
  have hqle : q ≤ 34 := by
    by_contra h
    push Not at h
    have hq35 : 35 ≤ q := by
      obtain ⟨k, hk⟩ := hodd
      omega
    have hq2 : 35 ^ 2 ≤ q ^ 2 := pow_le_pow_left' hq35 2
    have hsub : 1224 ≤ q ^ 2 - 1 := by norm_num at hq2; omega
    have hbig : 35 * 1224 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul hq35 hsub
    have h2m : q * (q ^ 2 - 1) = 2 * m := by rw [← hm]; ring
    omega
  have hqcases : q = 11 ∨ q = 13 ∨ q = 15 ∨ q = 17 ∨ q = 19 ∨ q = 21 ∨ q = 23 ∨
      q = 25 ∨ q = 27 ∨ q = 29 ∨ q = 31 ∨ q = 33 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hqcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hmv : m = 660 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 1092 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · exact absurd hq not_isPrimePow_fifteen
  · have hmv : m = 2448 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 3420 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 4620 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 6072 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 7800 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 9828 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 12180 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 14880 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd
  · have hmv : m = 17952 := by norm_num at hm; omega
    rw [hmv] at hdvd; norm_num at hdvd

theorem not_dvd_of_psp_card {n : ℕ} (hn : n = 60 ∨ n = 168 ∨ n = 360 ∨ n = 6048) :
    ¬ 25920 ∣ n := by
  rcases hn with rfl | rfl | rfl | rfl <;> norm_num

end CFSG.OddStandard.SmallF3.HypA2
