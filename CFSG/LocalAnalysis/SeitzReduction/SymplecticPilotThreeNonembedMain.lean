module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNonembedCore
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeNonembedModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeOmegaUniqueTorusMinus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadMinus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateMinusIsometry coordinateMinusWitnessEquiv)
open CFSG.SeitzReduction.OmegaPilot (orthDerivedProjEquiv orthDerivedCongr
  isHypCoord_coordinateQuadMinus)

section Arith

theorem not_nine_dvd_sq_add_add_one (r : ℕ) : ¬ 9 ∣ r ^ 2 + r + 1 := by
  intro h
  have h' : ((r ^ 2 + r + 1 : ℕ) : ZMod 9) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at h'
  have key : ∀ x : ZMod 9, x ^ 2 + x + 1 ≠ 0 := by decide
  exact key _ h'

theorem exists_prime_dvd_sq_add_add_one {r : ℕ} (hr : 2 ≤ r) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ∣ r ^ 2 + r + 1 ∧ ℓ ≠ 3 := by
  have hm : 7 ≤ r ^ 2 + r + 1 := by nlinarith
  by_cases h3 : 3 ∣ r ^ 2 + r + 1
  · obtain ⟨m', hm'⟩ := h3
    have h3' : ¬ 3 ∣ m' := fun ⟨k, hk⟩ =>
      not_nine_dvd_sq_add_add_one r ⟨k, by rw [hm', hk]; ring⟩
    have hm'1 : m' ≠ 1 := by
      rintro rfl
      omega
    refine ⟨m'.minFac, Nat.minFac_prime hm'1, ?_, fun h => h3' (h ▸ Nat.minFac_dvd m')⟩
    rw [hm']
    exact Dvd.dvd.mul_left (Nat.minFac_dvd m') 3
  · have hm1 : r ^ 2 + r + 1 ≠ 1 := by omega
    exact ⟨_, Nat.minFac_prime hm1, Nat.minFac_dvd _, fun h => h3 (h ▸ Nat.minFac_dvd _)⟩

theorem three_dvd_of_dvd_pow_sub_one {r ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3)
    (hdvd : ℓ ∣ r ^ 2 + r + 1) {k : ℕ} (hk : ℓ ∣ r ^ k - 1) : 3 ∣ k := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hx : ((r : ZMod ℓ)) ^ 2 + r + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at this
    exact this
  have hx3 : ((r : ZMod ℓ)) ^ 3 = 1 := by
    have : ((r : ZMod ℓ)) ^ 3 - 1 = ((r : ZMod ℓ) - 1) * (((r : ZMod ℓ)) ^ 2 + r + 1) := by ring
    rw [hx, mul_zero, sub_eq_zero] at this
    exact this
  have hx1 : (r : ZMod ℓ) ≠ 1 := by
    intro h
    rw [h] at hx
    have h3 : ((3 : ℕ) : ZMod ℓ) = 0 := by
      push_cast
      linear_combination hx
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (r : ZMod ℓ) = 3 := orderOf_eq_prime hx3 hx1
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hx
  have hrk : 1 ≤ r ^ k := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hr0)
  have hk' : ((r ^ k - 1 : ℕ) : ZMod ℓ) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hk
  rw [Nat.cast_sub hrk, Nat.cast_pow, Nat.cast_one, sub_eq_zero] at hk'
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hk'

theorem ne_two_of_dvd_sq_add_add_one {r ℓ : ℕ} (hdvd : ℓ ∣ r ^ 2 + r + 1) : ℓ ≠ 2 := by
  rintro rfl
  have h2 : 2 ∣ r * (r + 1) := even_iff_two_dvd.1 (Nat.even_mul_succ_self r)
  have : 2 ∣ (r ^ 2 + r + 1) - r * (r + 1) := Nat.dvd_sub hdvd h2
  have e : r ^ 2 + r + 1 - r * (r + 1) = 1 := by
    have : r ^ 2 + r + 1 = r * (r + 1) + 1 := by ring
    omega
  rw [e] at this
  omega

theorem dvd_cube_sub_one_of_dvd {r ℓ : ℕ} (hr : 1 ≤ r) (hdvd : ℓ ∣ r ^ 2 + r + 1) :
    ℓ ∣ r ^ 3 - 1 := by
  have : r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) := by
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : (s + 1) ^ 3 = s * ((s + 1) ^ 2 + (s + 1) + 1) + 1 := by ring
    omega
  rw [this]
  exact Dvd.dvd.mul_left hdvd _

end Arith

theorem omegaMinusEightSpSixNonembeddingInput_holds : OmegaMinusEightSpSixNonembeddingInput := by
  intro Y _ g hg hY K _ _ hK φ hφ
  have : CharP K 2 := LinearPilot.charP_two_of_card_eq_two_pow hK
  obtain ⟨-, F, _, _, hF, b, c, hirr, ⟨eE⟩⟩ :=
    CFSG.ComponentClassification.EvenOrthSelector.statedModel_of_lieModel (by decide) hY
  have : CharP F 2 := LinearPilot.charP_two_of_card_eq_two_pow hF
  have hr2 : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  obtain ⟨ℓ, hℓ, hℓdvd, hℓ3⟩ := exists_prime_dvd_sq_add_add_one hr2
  have hℓ2 : ℓ ≠ 2 := ne_two_of_dvd_sq_add_add_one hℓdvd
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard : ℓ ∣ Nat.card (GL (Fin (4 - 1)) F) := by
    have := Fintype.ofFinite F
    rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hF]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (0 : Fin (4 - 1))))
    simpa using dvd_cube_sub_one_of_dvd (by omega) hℓdvd
  obtain ⟨A, hAord⟩ := exists_prime_orderOf_dvd_card' ℓ hcard
  have hA : A ^ ℓ = 1 := by
    rw [← hAord]
    exact pow_orderOf_eq_one A
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hAord
    exact hℓ.one_lt.ne hAord
  have h1 : 1 ≤ 4 := by norm_num
  have hne := (isHypCoord_coordinateQuadMinus (K := F) h1 b c ⟨0, by norm_num⟩).exists_ne_zero
  let εY : Y ≃* orthDerived (quadMinus 4 F b c) :=
    (coordinateMinusWitnessEquiv F h1 b c eE).trans ((orthDerivedProjEquiv _ hne).symm.trans
      (orthDerivedCongr (coordinateMinusIsometry 4 F h1 b c)).symm)
  set ψ : orthDerived (quadMinus 4 F b c) →* StatedSp 3 K := φ.comp εY.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := hφ.comp εY.symm.injective
  obtain ⟨R, x, hR, hxN, hxℓ, hx1, a, ha, a', ha', hne'⟩ :=
    exists_nonabelian_radical_quadMinus (n := 4) (by norm_num) hirr (hℓ.odd_of_ne_two hℓ2) hA
      hA1
  apply hne'
  refine commute_of_isPGroup_of_mem_normalizer ψ hψinj R hR hxN hℓ hxℓ hx1 ?_ ?_ ?_ ?_ ha ha'
  · intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ).1 h0).symm
  · rw [hK]
    intro hd
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow hd))
  · intro j hj hj3 hd
    rw [hK, ← pow_mul, show 2 * g * (2 * j) = g * (4 * j) by ring, pow_mul] at hd
    have := three_dvd_of_dvd_pow_sub_one hℓ hℓ3 hℓdvd hd
    omega
  · intro i hi hi3 hd
    rw [hK, ← pow_mul, show 2 * g * i = g * (2 * i) by ring, pow_mul] at hd
    have := three_dvd_of_dvd_pow_sub_one hℓ hℓ3 hℓdvd hd
    omega

section GraphRows

theorem spThreeGraphRowsInput_of_recognitionInputs (hLE : SpThreeLinearEvenRecognitionInput)
    (hUE : SpThreeUnitaryEvenRecognitionInput) (hLO : SpThreeKindCoverInput .linearOdd)
    (hUO : SpThreeKindCoverInput .unitaryOdd) : SpThreeGraphRowsInput :=
  spThreeGraphRowsInput_of_recognition hLE hUE hLO hUO omegaMinusEightSpSixNonembeddingInput_holds

end GraphRows

end CFSG.SeitzReduction.SymplecticPilot
