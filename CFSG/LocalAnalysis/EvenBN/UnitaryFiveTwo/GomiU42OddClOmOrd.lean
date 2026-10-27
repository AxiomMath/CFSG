module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClOmegaSmallCent
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Fi.Prelim

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Module CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.ComponentInitial

section Orders

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem u42_ringChar_ne_two {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f) : ringChar K ≠ 2 := by
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three hf hK
  rw [ringChar.eq K 3]
  norm_num

theorem u42_sq_div_four_even (n : ℕ) : (2 * n) ^ 2 / 4 = n ^ 2 := by
  rw [show (2 * n) ^ 2 = 4 * n ^ 2 by ring]
  omega

theorem u42_sq_div_four_odd (n : ℕ) : (2 * n + 1) ^ 2 / 4 = n * (n + 1) := by
  rw [show (2 * n + 1) ^ 2 = 4 * (n * (n + 1)) + 1 by ring]
  omega

theorem u42_three_pow_dvd_card_orthogonalGroup {f m : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    {Q : QuadraticForm K W} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hm : finrank K W = m) (hm1 : 1 ≤ m) :
    3 ^ (f * ((m - 1) ^ 2 / 4)) ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hchar := u42_ringChar_ne_two hf hK
  rcases Nat.even_or_odd' m with ⟨n, rfl | rfl⟩
  · obtain ⟨m', rfl⟩ : ∃ m', n = m' + 1 := ⟨n - 1, by omega⟩
    have hsq : (2 * (m' + 1) - 1) ^ 2 / 4 = m' * (m' + 1) := by
      rw [show 2 * (m' + 1) - 1 = 2 * m' + 1 by omega]
      exact u42_sq_div_four_odd m'
    rw [hsq]
    obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (ε = 1 ∧ IsPlusType Q) ∨ (ε = -1 ∧ ¬ IsPlusType Q) := by
      by_cases hp : IsPlusType Q
      · exact ⟨1, Or.inl ⟨rfl, hp⟩⟩
      · exact ⟨-1, Or.inr ⟨rfl, hp⟩⟩
    have hcard := natCard_orthogonalGroup_of_type hQ hm hε
    have h1 : ((3 ^ (f * (m' * (m' + 1))) : ℕ) : ℤ) ∣
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
      rw [hcard, hK]
      push_cast
      have hX : (3 : ℤ) ^ (f * (m' * (m' + 1))) ∣ ((3 : ℤ) ^ f) ^ (m' * (m' + 1)) := by
        rw [← pow_mul]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_left hX 2) _) _
    exact Int.natCast_dvd_natCast.mp h1
  · have hsq : (2 * n + 1 - 1) ^ 2 / 4 = n ^ 2 := by
      rw [Nat.add_sub_cancel]
      exact u42_sq_div_four_even n
    rw [hsq]
    have hcard := natCard_orthogonalGroup_odd hchar hQ hm
    have h1 : ((3 ^ (f * n ^ 2) : ℕ) : ℤ) ∣
        (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) := by
      rw [hcard, hK]
      push_cast
      have hX : (3 : ℤ) ^ (f * n ^ 2) ∣ ((3 : ℤ) ^ f) ^ (n ^ 2) := by
        rw [← pow_mul]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hX 2) _
    exact Int.natCast_dvd_natCast.mp h1

theorem u42_card_orthogonalGroup_three (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {m : ℕ} (hm : finrank K W = m) (hm1 : 1 ≤ m)
    (hm5 : m ≤ 5) :
    (m = 1 ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2) ∨
    (m = 2 ∧ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 4 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 8)) ∨
    (m = 3 ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 48) ∨
    (m = 4 ∧ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 1152 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 1440)) ∨
    (m = 5 ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 103680) := by
  have hchar := u42_ringChar_ne_two (f := 1) le_rfl (by rw [hK]; norm_num)
  have hevens : ∀ (m' : ℕ) (hm' : finrank K W = 2 * (m' + 1)),
      ∃ ε : ℤ, (Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) : ℤ) =
        2 * (3 : ℤ) ^ (m' * (m' + 1)) * ((3 : ℤ) ^ (m' + 1) - ε) *
          ∏ i ∈ Finset.Icc 1 m', (((3 : ℤ) ^ 2) ^ i - 1) ∧ (ε = 1 ∨ ε = -1) := by
    intro m' hm'
    by_cases hp : IsPlusType Q
    · refine ⟨1, ?_, Or.inl rfl⟩
      have := natCard_orthogonalGroup_of_type hQ hm' (ε := 1) (Or.inl ⟨rfl, hp⟩)
      rw [this, hK]
      norm_num
    · refine ⟨-1, ?_, Or.inr rfl⟩
      have := natCard_orthogonalGroup_of_type hQ hm' (ε := -1) (Or.inr ⟨rfl, hp⟩)
      rw [this, hK]
      norm_num
  interval_cases m
  · left
    refine ⟨rfl, ?_⟩
    have := natCard_orthogonalGroup_odd hchar hQ (n := 0) hm
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num at this
    exact_mod_cast this
  · right; left
    refine ⟨rfl, ?_⟩
    obtain ⟨ε, h, hε⟩ := hevens 0 hm
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε with rfl | rfl
    · left; norm_num at h; exact_mod_cast h
    · right; norm_num at h; exact_mod_cast h
  · right; right; left
    refine ⟨rfl, ?_⟩
    have := natCard_orthogonalGroup_odd hchar hQ (n := 1) hm
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num [Finset.prod_Icc_succ_top] at this
    exact_mod_cast this
  · right; right; right; left
    refine ⟨rfl, ?_⟩
    obtain ⟨ε, h, hε⟩ := hevens 1 hm
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at h ⊢
    rcases hε with rfl | rfl
    · left; norm_num [Finset.prod_Icc_succ_top] at h; exact_mod_cast h
    · right; norm_num [Finset.prod_Icc_succ_top] at h; exact_mod_cast h
  · right; right; right; right
    refine ⟨rfl, ?_⟩
    have := natCard_orthogonalGroup_odd hchar hQ (n := 2) hm
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num [Finset.prod_Icc_succ_top] at this
    exact_mod_cast this

theorem u42_card_orthogonalGroup_three_two (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 2) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 4 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 8 := by
  rcases u42_card_orthogonalGroup_three hK hQ hm (by norm_num) (by norm_num) with
    ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | omega

theorem u42_card_orthogonalGroup_three_three (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 3) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 48 := by
  rcases u42_card_orthogonalGroup_three hK hQ hm (by norm_num) (by norm_num) with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | omega

theorem u42_card_orthogonalGroup_three_four (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 4) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 1152 ∨
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 1440 := by
  rcases u42_card_orthogonalGroup_three hK hQ hm (by norm_num) (by norm_num) with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;> first | exact h | omega

theorem u42_card_orthogonalGroup_three_five (hK : Nat.card K = 3) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 5) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 103680 := by
  rcases u42_card_orthogonalGroup_three hK hQ hm (by norm_num) (by norm_num) with
    ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ <;> first | exact h | omega

theorem u42_card_orthogonalGroup_nine_four (hK : Nat.card K = 9) {Q : QuadraticForm K W}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hm : finrank K W = 4) :
    414720 < Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have hm' : finrank K W = 2 * (1 + 1) := hm
  by_cases hp : IsPlusType Q
  · have := natCard_orthogonalGroup_of_type hQ hm' (ε := 1) (Or.inl ⟨rfl, hp⟩)
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num [Finset.prod_Icc_succ_top] at this
    omega
  · have := natCard_orthogonalGroup_of_type hQ hm' (ε := -1) (Or.inr ⟨rfl, hp⟩)
    generalize Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = c at this ⊢
    rw [hK] at this
    norm_num [Finset.prod_Icc_succ_top] at this
    omega

end Orders

section Unitary

open CFSG.ComponentClassification.CatalogueBUnitaryIsometry

variable {E W : Type} [Field E] [Finite E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem u42_three_pow_dvd_card_unitary {sigma : E ≃+* E} {f m : ℕ} (hf : 1 ≤ f)
    (hE : Nat.card E = (3 ^ f) ^ 2) (hm : finrank E W = m) (hm1 : 1 ≤ m)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsig : ∀ z, sigma z = z ^ (3 ^ f)) :
    3 ^ (f * (m * (m - 1) / 2)) ∣ Nat.card (isometryGroup h) := by
  have hcard := CFSG.ComponentClassification.CatFC.OmegaSmall.card_isometryGroup_unitary
    (ℓ := 3) (e := f) Nat.prime_three hf hE h hsym hnd hsig hm hm1
  have hd : ((3 ^ (f * (m * (m - 1) / 2)) : ℕ) : ℤ) ∣ (Nat.card (isometryGroup h) : ℤ) := by
    rw [hcard]
    refine Dvd.dvd.mul_right ?_ _
    push_cast
    rw [← pow_mul]
  exact Int.natCast_dvd_natCast.mp hd

end Unitary

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
