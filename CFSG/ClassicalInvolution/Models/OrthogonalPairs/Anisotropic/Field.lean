module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryField

public section

namespace CFSG.ClassicalInvolution.Models.OrthogonalPairs

open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

structure QuadExt (K K' : Type) [Field K] [Field K'] [Algebra K K'] (σ : K' ≃+* K') : Prop where
  isUnitary : IsUnitaryInvolution σ
  fix : ∀ a : K, σ (algebraMap K K' a) = algebraMap K K' a
  exists_of_fix : ∀ x : K', σ x = x → ∃ a : K, algebraMap K K' a = x
  isSquare : ∀ a : K, IsSquare (algebraMap K K' a)
  finrank_eq : Module.finrank K K' = 2

section Card

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
  {K' : Type} [Field K'] [Finite K'] [CharP K' p] [Algebra K K']

namespace Aniso

theorem sigma_algebraMap (hK : Nat.card K = p ^ f) (a : K) :
    unitaryInvolution K' p f (algebraMap K K' a) = algebraMap K K' a := by
  have := Fintype.ofFinite K
  rw [unitaryInvolution_apply, ← map_pow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_algebraMap_of_fixed (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    {x : K'} (hx : unitaryInvolution K' p f x = x) : ∃ a : K, algebraMap K K' a = x := by
  have hcard := card_fixedSubfield (F := K') (p := p) (f := f) hK'
  have hsub : Set.range (algebraMap K K') ⊆ ((fixedSubfield K' p f : Subfield K') : Set K') := by
    rintro _ ⟨a, rfl⟩
    exact sigma_algebraMap hK a
  have hfin : (((fixedSubfield K' p f : Subfield K') : Set K')).Finite := Set.toFinite _
  have hle : (((fixedSubfield K' p f : Subfield K') : Set K')).ncard ≤
      (Set.range (algebraMap K K')).ncard := by
    rw [Set.ncard_range_of_injective (algebraMap K K').injective, ← Nat.card_coe_set_eq]
    exact (hcard.trans hK.symm).le
  have := Set.eq_of_subset_of_ncard_le hsub hle hfin
  have hx' : x ∈ ((fixedSubfield K' p f : Subfield K') : Set K') := hx
  rw [← this] at hx'
  exact hx'

omit [Fact p.Prime] in
theorem two_le_card (hK : Nat.card K = p ^ f) : 2 ≤ p ^ f := by
  rw [← hK]
  exact Finite.one_lt_card

omit [CharP K' p] [Fact p.Prime] in
theorem finrank_eq_two (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2) :
    Module.finrank K K' = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := K) (V := K')
  rw [hK', hK] at h
  exact (Nat.pow_right_injective (two_le_card hK) h).symm

omit [Finite K'] [Algebra K K'] in
theorem ringChar_ne_two_of_odd (hK : Nat.card K = p ^ f) (hodd : Odd (Nat.card K)) :
    ringChar K' ≠ 2 := by
  rw [ringChar.eq K' p]
  rintro rfl
  rw [hK] at hodd
  have hf : f ≠ 0 := by
    rintro rfl
    have := two_le_card hK
    simp at this
  exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hf⟩)) hodd

theorem isSquare_algebraMap (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (a : K) : IsSquare (algebraMap K K' a) := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  by_cases ha : a = 0
  · rw [ha, map_zero]
    exact ⟨0, by simp⟩
  have ha' : algebraMap K K' a ≠ 0 := by simpa using ha
  rw [FiniteField.isSquare_iff (ringChar_ne_two_of_odd hK hodd) ha']
  have hq : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card, hK]
  have hq' : Fintype.card K' = Fintype.card K ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hK', hq]
  have hqodd : Odd (Fintype.card K) := by rw [hq, ← hK]; exact hodd
  obtain ⟨m, hm⟩ := hqodd
  have h1 : Fintype.card K' / 2 = (Fintype.card K - 1) * (m + 1) := by
    have h2 : (2 * m + 1) ^ 2 = 2 * (2 * m * (m + 1)) + 1 := by ring
    rw [hq', hm, h2, Nat.mul_add_div (by norm_num)]
    simp
  rw [h1, pow_mul, ← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one, one_pow]

end Aniso

theorem QuadExt.of_card (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) : QuadExt K K' (unitaryInvolution K' p f) where
  isUnitary := isUnitaryInvolution_unitaryInvolution hK'
  fix := Aniso.sigma_algebraMap hK
  exists_of_fix _ hx := Aniso.exists_algebraMap_of_fixed hK hK' hx
  isSquare := Aniso.isSquare_algebraMap hK hK' hodd
  finrank_eq := Aniso.finrank_eq_two hK hK'

end Card

section Basic

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'}

theorem QuadExt.sigma_eq_neg (E : QuadExt K K' σ) {δ : K} (hδ : ¬ IsSquare δ) {r : K'}
    (hr : r * r = algebraMap K K' δ) : σ r = -r := by
  have h1 : (σ r - r) * (σ r + r) = 0 := by
    have : σ r * σ r = r * r := by rw [← map_mul, hr, E.fix]
    linear_combination this
  rcases mul_eq_zero.mp h1 with h | h
  · exfalso
    obtain ⟨a, ha⟩ := E.exists_of_fix r (sub_eq_zero.mp h)
    apply hδ
    refine ⟨a, ?_⟩
    apply (algebraMap K K').injective
    rw [map_mul, ha, hr]
  · linear_combination h

theorem not_mem_range_of_sq {δ : K} (hδ : ¬ IsSquare δ) {r : K'}
    (hr : r * r = algebraMap K K' δ) (a : K) : algebraMap K K' a ≠ r := by
  rintro rfl
  apply hδ
  refine ⟨a, ?_⟩
  apply (algebraMap K K').injective
  rw [map_mul, hr]

theorem linearIndependent_one_r {r : K'} (hr : ∀ a : K, algebraMap K K' a ≠ r) :
    LinearIndependent K ![(1 : K'), r] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  simp only [Algebra.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [map_zero, zero_mul, add_zero] at hst
    exact ⟨(map_eq_zero_iff _ (algebraMap K K').injective).mp hst, rfl⟩
  · exfalso
    apply hr (-(s / t))
    have ht' : algebraMap K K' t ≠ 0 := by simpa using ht
    rw [map_neg, map_div₀]
    field_simp
    linear_combination (-1 : K') * hst

@[expose] noncomputable def QuadExt.basisOneR (E : QuadExt K K' σ) {r : K'}
    (hr : ∀ a : K, algebraMap K K' a ≠ r) : Module.Basis (Fin 2) K K' :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_r hr)
    (by rw [E.finrank_eq]; simp)

theorem QuadExt.basisOneR_apply (E : QuadExt K K' σ) {r : K'}
    (hr : ∀ a : K, algebraMap K K' a ≠ r) (i : Fin 2) :
    E.basisOneR hr i = ![(1 : K'), r] i := by
  simp [basisOneR]

end Basic

section Algebra

variable {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime]

theorem Aniso.nonempty_algebra (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2) :
    Nonempty (Algebra K K') := by
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  have hcK : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hK])
  have hcK' : CharP K' p :=
    charP_of_card_eq_prime_pow (f := f * 2) (by rw [← Nat.card_eq_fintype_card, hK', pow_mul])
  let : Algebra (ZMod p) K := ZMod.algebra _ _
  let : Algebra (ZMod p) K' := ZMod.algebra _ _
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hK'' : Nat.card K' = p ^ (f * 2) := by rw [hK', pow_mul]
  have h1 : Module.finrank (ZMod p) K = f :=
    Nat.pow_right_injective hp ((FiniteField.pow_finrank_eq_natCard p K).trans hK)
  have h2 : Module.finrank (ZMod p) K' = f * 2 :=
    Nat.pow_right_injective hp ((FiniteField.pow_finrank_eq_natCard p K').trans hK'')
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := K) (L := K')
    (by rw [h1, h2]; exact dvd_mul_right f 2)
  exact ⟨φ.toRingHom.toAlgebra⟩

end Algebra

end CFSG.ClassicalInvolution.Models.OrthogonalPairs
