module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.LocalQuotient
public import CFSG.LocalAnalysis.LyonsUnitaryFour.FiveColumns.FourierIntegrality
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum

public section

open scoped BigOperators Classical

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers CFSG.Wreathed

@[expose] noncomputable def fiveFourier {X : Type*} [Monoid X] (f : X → ℂ) (ζ : ℂ) (u v : X)
    (i : ℕ) : ℂ :=
  (5 : ℂ)⁻¹ * ∑ j ∈ Finset.range 5, ζ ^ (4 * i * j) * f (u * v ^ j)

theorem sum_range_five_pow_mul {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (m : ℕ) :
    ∑ j ∈ Finset.range 5, ζ ^ (m * j) = if 5 ∣ m then 5 else 0 := by
  by_cases hm : 5 ∣ m
  · rw [ite_eq_left hm]
    obtain ⟨k, rfl⟩ := hm
    have : ∀ j, ζ ^ (5 * k * j) = 1 := fun j => by
      rw [mul_assoc, pow_mul, hζ.pow_eq_one, one_pow]
    simp only [this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    norm_num
  · rw [ite_eq_right hm]
    have hne : ζ ^ m ≠ 1 := fun h => hm (hζ.dvd_of_pow_eq_one m h)
    have h5 : (ζ ^ m) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hgeom := geom_sum_mul (ζ ^ m) 5
    rw [h5, sub_self] at hgeom
    have hsum := (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)
    rw [← hsum]
    exact Finset.sum_congr rfl fun j _ => by rw [pow_mul]

theorem conj_pow_of_pow_five {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) (n : ℕ) :
    starRingEnd ℂ (ζ ^ n) = ζ ^ (4 * n) := by
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one (by norm_num)
  have hinv : starRingEnd ℂ ζ = ζ ^ 4 := by
    have h1 : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have h2 : ζ * ζ ^ 4 = 1 := by rw [← pow_succ', hζ.pow_eq_one]
    exact mul_left_cancel₀ (hζ.ne_zero (by norm_num)) (h1.trans h2.symm)
  rw [map_pow, hinv, ← pow_mul]

namespace UnitaryFourByFive

variable {L : Type} [Group L] [Fintype L] {S₀ : Subgroup L} {h : L}
  (hL : UnitaryFourByFive S₀ h)
include hL

theorem fiveFourier_integer (basis : FiniteIrreducibleCharacterBasis L) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {z₀ : L} (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    (hz₀2 : z₀ ^ 2 = 1) (θ : basis.index) (i : ℕ) :
    ∃ n : ℤ, fiveFourier (basis.representation θ).character ζ z₀ h i = n := by
  have hcentral := hL.center_le_center hz₀
  obtain ⟨parity, hsign, -, hvalues⟩ := irreducible_character_central_involution_parity
    (basis.representation θ) (basis.irreducible θ) z₀ hcentral hz₀2
  have hζu : IsUnit ζ := (hζ.isUnit (by norm_num))
  let u : ℂˣ := hζu.unit ^ i
  have hu5 : u ^ 5 = 1 := by
    apply Units.ext
    simp only [u, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hrep : (basis.representation θ).representation h ^ 5 = 1 := by
    rw [← map_pow, hL.pow_five, map_one]
  obtain ⟨m, hm⟩ := character_fourier_natural (basis.representation θ) h 5 (by norm_num) hrep u hu5
  have hζinv : ζ⁻¹ = ζ ^ 4 := by
    have h4 : ζ * ζ ^ 4 = 1 := by rw [← pow_succ', hζ.pow_eq_one]
    exact (eq_inv_of_mul_eq_one_right h4).symm
  have hpow : ∀ j : ℕ, ((u⁻¹ : ℂˣ) : ℂ) ^ j = ζ ^ (4 * i * j) := by
    intro j
    have hval : ((u⁻¹ : ℂˣ) : ℂ) = ζ ^ (4 * i) := by
      rw [Units.val_inv_eq_inv_val]
      simp only [u, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
      rw [← inv_pow, hζinv, ← pow_mul]
    rw [hval, ← pow_mul]
  have hsum : fiveFourier (basis.representation θ).character ζ z₀ h i = parity * (m : ℂ) := by
    rw [← hm, fiveFourier, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hpow j, (Subgroup.mem_center_iff.mp hcentral (h ^ j)).symm, hvalues]
    ring
  rcases hsign with rfl | rfl
  · exact ⟨m, by rw [hsum, one_mul]; push_cast; rfl⟩
  · exact ⟨-m, by rw [hsum]; push_cast; ring⟩

theorem column_sum_mul_pow (basis : FiniteIrreducibleCharacterBasis L) {z₀ : L}
    (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype) {j l : ℕ} (hj : j < 5) (hl : l < 5) :
    ∑ θ, (basis.representation θ).character (z₀ * h ^ j) *
        starRingEnd ℂ ((basis.representation θ).character (z₀ * h ^ l)) =
      if j = l then (if j = 0 then 320 else 20) else 0 := by
  rw [complete_complex_character_column_sum]
  by_cases hjl : j = l
  · subst hjl
    rw [ite_eq_left rfl, conjugatorCount_self]
    by_cases hj0 : j = 0
    · subst hj0
      rw [ite_eq_left rfl, pow_zero, mul_one]
      have htop : Subgroup.centralizer ({z₀} : Set L) = ⊤ := by
        rw [eq_top_iff]
        intro g _
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp (hL.center_le_center hz₀) g)
      rw [htop, Subgroup.card_top, hL.card_eq]
      norm_num
    · rw [ite_eq_right hj0, hL.card_centralizer_mul_pow hz₀ (fun hd => hj0
        (Nat.eq_zero_of_dvd_of_lt hd hj))]
      norm_num
  · rw [ite_eq_right hjl]
    unfold conjugatorCount
    refine Finset.sum_eq_zero fun g _ => ?_
    rw [ite_eq_right]
    intro hg
    exact hL.not_isConj hz₀ hz₀ hl hj (Ne.symm hjl) (isConj_iff.mpr ⟨g, hg⟩)

theorem fiveFourier_gram (basis : FiniteIrreducibleCharacterBasis L) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ 5) {z₀ : L} (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype)
    {i k : ℕ} (hi : i < 5) (hk : k < 5) :
    ∑ θ, fiveFourier (basis.representation θ).character ζ z₀ h i *
        starRingEnd ℂ (fiveFourier (basis.representation θ).character ζ z₀ h k) =
      if i = k then 16 else 12 := by
  set χ := fun θ => (basis.representation θ).character with hχ
  have hexp : ∀ θ, fiveFourier (χ θ) ζ z₀ h i * starRingEnd ℂ (fiveFourier (χ θ) ζ z₀ h k) =
      (25 : ℂ)⁻¹ * ∑ j ∈ Finset.range 5, ∑ l ∈ Finset.range 5,
        ζ ^ (4 * i * j) * ζ ^ (16 * k * l) *
          (χ θ (z₀ * h ^ j) * starRingEnd ℂ (χ θ (z₀ * h ^ l))) := by
    intro θ
    simp only [fiveFourier, map_mul, map_sum, map_inv₀, conj_pow_of_pow_five hζ]
    have h5 : starRingEnd ℂ (5 : ℂ) = 5 := by
      rw [show (5 : ℂ) = ((5 : ℕ) : ℂ) by norm_num, Complex.conj_natCast]
    rw [h5, mul_mul_mul_comm, Finset.sum_mul_sum, show (5 : ℂ)⁻¹ * 5⁻¹ = 25⁻¹ by norm_num]
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [show 4 * (4 * k * l) = 16 * k * l by ring]
    ring
  simp only [hχ] at hexp ⊢
  rw [Finset.sum_congr rfl fun θ _ => hexp θ, ← Finset.mul_sum, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
  have hinner : ∀ j ∈ Finset.range 5, ∀ l ∈ Finset.range 5,
      ∑ θ, ζ ^ (4 * i * j) * ζ ^ (16 * k * l) *
        ((basis.representation θ).character (z₀ * h ^ j) *
          starRingEnd ℂ ((basis.representation θ).character (z₀ * h ^ l))) =
      ζ ^ (4 * i * j) * ζ ^ (16 * k * l) *
        (if j = l then (if j = 0 then 320 else 20) else 0) := by
    intro j hj l hl
    rw [← Finset.mul_sum,
      hL.column_sum_mul_pow basis hz₀ (Finset.mem_range.mp hj) (Finset.mem_range.mp hl)]
  rw [Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => hinner j hj l hl]
  have hdiag : ∀ j ∈ Finset.range 5, ∑ l ∈ Finset.range 5,
      ζ ^ (4 * i * j) * ζ ^ (16 * k * l) * (if j = l then (if j = 0 then 320 else 20) else 0) =
      ζ ^ ((4 * i + 16 * k) * j) * 20 + (if j = 0 then 300 else 0) := by
    intro j hj
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left rfl, add_mul, pow_add, mul_assoc 4 i j, mul_assoc 16 k j]
      by_cases hj0 : j = 0
      · subst hj0
        norm_num
      · rw [ite_eq_right hj0, ite_eq_right hj0, add_zero]
    · intro l _ hlj
      rw [ite_eq_right (Ne.symm hlj), mul_zero]
    · intro h
      exact absurd hj h
  rw [Finset.sum_congr rfl hdiag, Finset.sum_add_distrib, ← Finset.sum_mul,
    sum_range_five_pow_mul hζ, Finset.sum_ite_eq' (Finset.range 5) 0, ite_eq_left
      (Finset.mem_range.mpr (by norm_num))]
  have hiff : 5 ∣ 4 * i + 16 * k ↔ i = k := by omega
  by_cases hik : i = k
  · rw [ite_eq_left (hiff.mpr hik), ite_eq_left hik]
    norm_num
  · rw [ite_eq_right (fun h => hik (hiff.mp h)), ite_eq_right hik]
    norm_num

theorem fiveFourier_degree (basis : FiniteIrreducibleCharacterBasis L) {ζ : ℂ}
    {z₀ : L} (hz₀ : z₀ ∈ (Subgroup.center S₀).map S₀.subtype) (hz₀1 : z₀ ≠ 1) (i : ℕ) :
    ∑ θ, (basis.representation θ).character 1 *
        fiveFourier (basis.representation θ).character ζ z₀ h i = 0 := by
  have hz₀S : z₀ ∈ S₀ := (mem_map_center_iff.mp hz₀).1
  have hcol : ∀ j ∈ Finset.range 5,
      ∑ θ, (basis.representation θ).character 1 *
        (basis.representation θ).character (z₀ * h ^ j) = 0 := by
    intro j hj
    have hne : z₀ * h ^ j ≠ 1 := by
      intro h1
      have hhj : h ^ j ∈ S₀ := by
        have : h ^ j = z₀⁻¹ := eq_inv_of_mul_eq_one_right h1
        rw [this]
        exact S₀.inv_mem hz₀S
      have hd := (hL.pow_mem_iff j).mp hhj
      have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt hd (Finset.mem_range.mp hj)
      subst hj0
      rw [pow_zero, mul_one] at h1
      exact hz₀1 h1
    have hcs := complete_complex_character_column_sum basis 1 (z₀ * h ^ j)
    have hzero : conjugatorCount (1 : L) (z₀ * h ^ j) = 0 := by
      unfold conjugatorCount
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [ite_eq_right]
      intro hg
      apply hne
      rw [← hg]
      group
    rw [hzero] at hcs
    rw [← hcs]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [mul_comm]
    congr 1
    rw [FiniteComplexRepresentation.character, Representation.char_one, Complex.conj_natCast]
  simp only [fiveFourier, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j hj => ?_
  have := hcol j hj
  calc ∑ θ, (basis.representation θ).character 1 * ((5 : ℂ)⁻¹ * (ζ ^ (4 * i * j) *
        (basis.representation θ).character (z₀ * h ^ j)))
      = (5 : ℂ)⁻¹ * ζ ^ (4 * i * j) * ∑ θ, (basis.representation θ).character 1 *
        (basis.representation θ).character (z₀ * h ^ j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun θ _ => ?_
        ring
    _ = 0 := by rw [this, mul_zero]

end UnitaryFourByFive

end CFSG.LyonsUnitaryFour
