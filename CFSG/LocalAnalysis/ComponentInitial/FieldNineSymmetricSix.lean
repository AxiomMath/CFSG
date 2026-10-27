module

public import CFSG.LocalAnalysis.ComponentInitial.FieldNineSymmetricSixTransport
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjective

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace FieldNine

open Equiv Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped Pointwise

section Normalizer

variable {K : Type*} [Field K]

theorem fieldExtension_mul_translation (σ : K ≃+* K) (b : K) :
    fieldExtension K σ * translation K b = translation K (σ b) * fieldExtension K σ := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rfl
  | some y =>
    simp only [Perm.mul_apply, translation_some, fieldExtension_some, map_add]

theorem fieldExtension_mul_inversion (σ : K ≃+* K) :
    fieldExtension K σ * inversion K = inversion K * fieldExtension K σ := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none =>
    simp only [Perm.mul_apply, inversion_none, fieldExtension_none, fieldExtension_some, map_zero]
  | some y =>
    by_cases hy : y = 0
    · subst hy
      simp only [Perm.mul_apply, inversion_zero, fieldExtension_none, fieldExtension_some,
        map_zero]
    · have hσy : σ y ≠ 0 := (map_ne_zero σ).2 hy
      simp only [Perm.mul_apply, inversion_nonzero K y hy, inversion_nonzero K (σ y) hσy,
        fieldExtension_some, map_neg, map_inv₀]

theorem fieldExtension_mul_self {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) :
    fieldExtension K σ * fieldExtension K σ = 1 := by
  refine Equiv.ext fun x => ?_
  cases x with
  | none => rfl
  | some y => simp only [Perm.mul_apply, fieldExtension_some, hσ, Perm.one_apply]

theorem conj_mem_coordinateG (σ : K ≃+* K) {x : Perm (Omega K)} (hx : x ∈ coordinateG K) :
    fieldExtension K σ * x * (fieldExtension K σ)⁻¹ ∈ coordinateG K := by
  have hle : coordinateG K ≤
      (coordinateG K).comap (MulAut.conj (fieldExtension K σ)).toMonoidHom := by
    refine (closure_le _).2 fun y hy => ?_
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rcases hy with ⟨b, rfl⟩ | hy
    · rw [fieldExtension_mul_translation, mul_inv_cancel_right]
      exact subset_closure (Or.inl ⟨σ b, rfl⟩)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [fieldExtension_mul_inversion, mul_inv_cancel_right]
      exact subset_closure (Or.inr rfl)
  exact hle hx

theorem fieldExtension_mem_normalizer {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) :
    fieldExtension K σ ∈ normalizer (coordinateG K : Set (Perm (Omega K))) := by
  have hs := fieldExtension_mul_self hσ
  have hinv : (fieldExtension K σ)⁻¹ = fieldExtension K σ := inv_eq_of_mul_eq_one_right hs
  rw [mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_coordinateG σ, fun hh => ?_⟩
  have h1 := conj_mem_coordinateG σ hh
  rwa [hinv, ← mul_assoc, ← mul_assoc, hs, one_mul, mul_assoc, hs, mul_one] at h1

theorem card_closure_le [Finite K] {σ : K ≃+* K} (hσ : ∀ x, σ (σ x) = x) :
    Nat.card (closure ((coordinateG K : Set (Perm (Omega K))) ∪ {fieldExtension K σ})) ≤
      2 * Nat.card (coordinateG K) := by
  have hclos : closure ((coordinateG K : Set (Perm (Omega K))) ∪ {fieldExtension K σ}) =
      coordinateG K ⊔ zpowers (fieldExtension K σ) := by
    rw [Subgroup.closure_union, closure_eq, zpowers_eq_closure]
  have hle : zpowers (fieldExtension K σ) ≤ normalizer (coordinateG K : Set (Perm (Omega K))) :=
    zpowers_le.2 (fieldExtension_mem_normalizer hσ)
  have hcoe := coe_mul_of_right_le_normalizer_left (coordinateG K) _ hle
  have hzp : Nat.card (zpowers (fieldExtension K σ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one two_pos (by rw [sq, fieldExtension_mul_self hσ])
  rw [hclos]
  calc Nat.card (coordinateG K ⊔ zpowers (fieldExtension K σ) : Subgroup (Perm (Omega K)))
      = Nat.card ((coordinateG K : Set (Perm (Omega K))) *
          (zpowers (fieldExtension K σ) : Set (Perm (Omega K)))) := by
        rw [← hcoe]
        rfl
    _ ≤ Nat.card (coordinateG K) * Nat.card (zpowers (fieldExtension K σ)) := Set.natCard_mul_le
    _ ≤ Nat.card (coordinateG K) * 2 := Nat.mul_le_mul_left _ hzp
    _ = 2 * Nat.card (coordinateG K) := mul_comm _ _

end Normalizer

theorem card_coordinateG_of_card_eq_nine {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 9) :
    Nat.card (coordinateG K) = 360 := by
  rw [← Nat.card_congr (pslEquivCoordinateG K).toEquiv,
    CFSG.GorensteinWalter.psl2_card_formula K
      ⟨3, 2, Nat.prime_three, by decide, by norm_num, by rw [hK]; norm_num⟩, hK]
  norm_num

end FieldNine

open FieldNine Equiv Subgroup CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped Pointwise

theorem unique_field_nine_semilinear_symmetric_six_isomorphism (K : Type*) [Field K] [Fintype K]
    (hK : Fintype.card K = 9) :
    (∃ σ : K ≃+* K, ∀ x, σ x = x ^ 3) ∧
      ∀ σ : K ≃+* K, (∀ x, σ x = x ^ 3) →
        ∃ Φ : closure ((coordinateG K : Set (Perm (Omega K))) ∪ {fieldExtension K σ}) ≃*
            Perm (Fin 6),
          (Φ ⟨fieldExtension K σ, subset_closure (Or.inr rfl)⟩).IsSwap := by
  have hK' : Nat.card K = 3 ^ 2 := by rw [Nat.card_eq_fintype_card, hK]; norm_num
  have : CharP K 3 := finite_field_prime_power_characteristic Nat.prime_three (by norm_num) hK'
  refine ⟨?_, fun σ hσ => ?_⟩
  ·
    have : ExpChar K 3 := ExpChar.prime Nat.prime_three
    have hinj : Function.Injective (frobenius K 3) := (frobenius K 3).injective
    exact ⟨RingEquiv.ofBijective (frobenius K 3) ⟨hinj, Finite.surjective_of_injective hinj⟩,
      fun x => frobenius_def 3 x⟩
  obtain ⟨i, hi⟩ : ∃ i : K, i * i = -1 := by
    obtain ⟨r, hr⟩ := FiniteField.isSquare_neg_one_iff.2 (by rw [hK]; decide)
    exact ⟨r, hr.symm⟩
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [hσ, hσ, ← pow_mul, show 3 * 3 = Fintype.card K by rw [hK], FiniteField.pow_card]
  set s := fieldExtension K σ
  set J := closure ((coordinateG K : Set (Perm (Omega K))) ∪ {s})
  set φ := (pointEquiv hi hK).permCongrHom
  have hφτ : ∀ b, φ (translation K b) = translationLabel ((coordEquiv hi hK).symm b) :=
    permCongr_translation hi hK
  have hφι : φ (inversion K) = inversionLabel := permCongr_inversion hi hK
  have hφs : φ s = frobeniusLabel := permCongr_fieldExtension hi hK hσ
  have hG : coordinateG K ≤ blockStabilizer.comap φ.toMonoidHom := by
    rw [coordinateG, closure_le]
    rintro x (⟨b, rfl⟩ | hx)
    · change φ (translation K b) ∈ blockStabilizer
      rw [hφτ]
      exact translationLabel_mem _
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      change φ (inversion K) ∈ blockStabilizer
      rw [hφι]
      exact inversionLabel_mem
  have hJ : J ≤ blockStabilizer.comap φ.toMonoidHom := by
    rw [closure_le]
    rintro x (hx | hx)
    · exact hG hx
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      change φ s ∈ blockStabilizer
      rw [hφs]
      exact frobeniusLabel_mem
  let Φ₀ : J →* Perm (Fin 6) := blockHom.comp
    ((φ.toMonoidHom.comp J.subtype).codRestrict blockStabilizer fun x => hJ x.2)
  have hΦ₀ : ∀ (x : J) (π : Perm (Fin 6)), (∀ j, φ x • block j = block (π j)) → Φ₀ x = π :=
    fun _ _ h => blockHom_eq h
  have hsJ : s ∈ J := subset_closure (Or.inr rfl)
  have hGJ : ∀ x ∈ coordinateG K, x ∈ J := fun x hx => subset_closure (Or.inl hx)
  have hτJ : ∀ b, translation K b ∈ J := fun b => hGJ _ (subset_closure (Or.inl ⟨b, rfl⟩))
  have hιJ : inversion K ∈ J := hGJ _ (subset_closure (Or.inr rfl))
  have hΦs : Φ₀ ⟨s, hsJ⟩ = swap 0 1 := hΦ₀ _ _ fun j => by
    change φ s • block j = _
    rw [hφs]
    exact frobeniusLabel_smul_block j
  have hΦτ : ∀ p : ZMod 3 × ZMod 3, Φ₀ ⟨translation K (coord i p), hτJ _⟩ =
      blockImageOne ^ p.1.val * blockImageI ^ p.2.val := fun p => hΦ₀ _ _ fun j => by
    change φ (translation K (coord i p)) • block j = _
    rw [hφτ, coordEquiv_symm_coord hi hK]
    exact translationLabel_smul_block p j
  have hΦι : Φ₀ ⟨inversion K, hιJ⟩ = blockImageInversion := hΦ₀ _ _ fun j => by
    change φ (inversion K) • block j = _
    rw [hφι]
    exact inversionLabel_smul_block j
  have hsurj : Function.Surjective Φ₀ := MonoidHom.range_eq_top.1
    (closure_blockImages_eq_top ⟨_, (hΦτ (1, 0)).trans (by decide)⟩
      ⟨_, (hΦτ (0, 1)).trans (by decide)⟩ ⟨_, hΦι⟩ ⟨_, hΦs⟩)
  have hcard : Nat.card J ≤ Nat.card (Perm (Fin 6)) := by
    rw [Nat.card_perm, Nat.card_fin]
    calc Nat.card J ≤ 2 * Nat.card (coordinateG K) := card_closure_le hσσ
      _ = Nat.factorial 6 := by
        rw [card_coordinateG_of_card_eq_nine (by rw [Nat.card_eq_fintype_card, hK])]
        rfl
  refine ⟨MulEquiv.ofBijective Φ₀ (hsurj.bijective_of_nat_card_le hcard), ?_⟩
  rw [MulEquiv.ofBijective_apply, hΦs]
  exact ⟨0, 1, by decide, rfl⟩

end CFSG.LocalAnalysis.ComponentInitial
