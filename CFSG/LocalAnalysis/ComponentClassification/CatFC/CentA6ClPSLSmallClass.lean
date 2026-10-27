module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallField
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallComp
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6Transport

public noncomputable section

namespace CFSG.ComponentClassification.CatFC.PSLSmall

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank Matrix
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField (fixedField pslFieldAut)

theorem exists_innerDiagonal_of_mem_range {n : ℕ} {K : Type} [Field K]
    {σ : MulAut (ProjectiveSpecialLinearGroup (Fin n) K)}
    (h : σ ∈ (MulAut.conj : ProjectiveSpecialLinearGroup (Fin n) K →*
      MulAut (ProjectiveSpecialLinearGroup (Fin n) K)).range) :
    ∃ B : GL (Fin n) K, σ = innerDiagonalAction n K B := by
  obtain ⟨g, rfl⟩ := h
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨SpecialLinearGroup.toGL h, ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : (innerDiagonalAction n K (SpecialLinearGroup.toGL h))
      (QuotientGroup.mk k : ProjectiveSpecialLinearGroup (Fin n) K) =
        QuotientGroup.mk (slConjugation n K (SpecialLinearGroup.toGL h) k) :=
    innerDiagonalAction_mk n K _ k
  rw [h1]
  change (QuotientGroup.mk h : ProjectiveSpecialLinearGroup (Fin n) K) * (QuotientGroup.mk k) *
    (QuotientGroup.mk h)⁻¹ = _
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [toGL_slConjugation]
  simp

@[expose] def NoA6 {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ D : Subgroup ↥(fixedSubgroup σ), ¬ A6Hyp σ D

theorem NoA6.of_congr {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (σ : MulAut S)
    (h : NoA6 (MulAut.congr e σ)) : NoA6 σ :=
  fun D hD => h _ (a6Hyp_congr e σ D hD)

theorem NoA6.congr' {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {σ : MulAut S}
    (h : NoA6 σ) : NoA6 (MulAut.congr e σ) := by
  apply NoA6.of_congr e.symm
  have : MulAut.congr e.symm (MulAut.congr e σ) = σ := by
    ext x
    simp [MulAut.congr_apply]
  rw [this]
  exact h

theorem OuterEvidence.of_congr {S S' : Type} [Group S] [Finite S] [Group S'] [Finite S']
    (e : S ≃* S') {σ : MulAut S} (h : OuterEvidence σ) : OuterEvidence (MulAut.congr e σ) := by
  obtain ⟨x, A, _, ψ, hx2, hψ⟩ := h
  refine ⟨fixedEquiv e σ x, A, inferInstance, ψ.comp (fixedEquiv e σ).symm.toMonoidHom, ?_, ?_⟩
  · rw [← hx2]
    exact orderOf_injective (fixedEquiv e σ).toMonoidHom (fixedEquiv e σ).injective x
  · simpa using hψ

theorem frobenius_sq_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ} (hK : Nat.card K = p ^ f)
    (heven : Even f) {τ : K ≃+* K} (hτc : ∀ x : K, τ x = x ^ (p ^ (f / 2))) : τ ^ 2 = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine RingEquiv.ext fun x => ?_
  rw [sq, RingAut.mul_apply, hτc, hτc, ← pow_mul, ← sq, ← pow_mul,
    Nat.div_mul_cancel (even_iff_two_dvd.1 heven), ← hK, Nat.card_eq_fintype_card,
    FiniteField.pow_card]
  rfl

theorem evidence_semilinear_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 81)
    (A : GL (Fin 2) K) {τ : K ≃+* K} (hτ : τ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction 2 K A τ ^ 2 = 1) :
    OuterEvidence (CatalogueBLinearSemilinear.semilinearAction 2 K A τ) := by
  have hK' : Nat.card K = 3 ^ 4 := by rw [hK]; norm_num
  obtain ⟨heven, hτc, H, hα⟩ :=
    CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy 2 K 3 4 Nat.prime_three
      (by decide) (by norm_num) hK' le_rfl (Or.inr (by rw [hK]; norm_num)) A τ hτ hsq
  have hτ2 : τ ^ 2 = 1 := frobenius_sq_eq_one hK' heven hτc
  have hev := (field_two_evidence hK hτ2 hτ).of_congr (innerDiagonalAction 2 K H)
  have hc : MulAut.congr (innerDiagonalAction 2 K H) (pslFieldAut (Fin 2) K τ) =
      CatalogueBLinearSemilinear.semilinearAction 2 K A τ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (innerDiagonalAction 2 K H)
      (pslFieldAut (Fin 2) K τ) = _).trans hα.symm
  rwa [hc] at hev

theorem noA6_semilinear_three (hO : LieOrderFormulasInput) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 9) (A : GL (Fin 3) K) {τ : K ≃+* K} (hτ : τ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction 3 K A τ ^ 2 = 1) :
    NoA6 (CatalogueBLinearSemilinear.semilinearAction 3 K A τ) := by
  have hK' : Nat.card K = 3 ^ 2 := by rw [hK]; norm_num
  obtain ⟨heven, hτc, H, hα⟩ :=
    CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy 3 K 3 2 Nat.prime_three
      (by decide) (by norm_num) hK' (by norm_num) (Or.inl le_rfl) A τ hτ hsq
  have hτ2 : τ ^ 2 = 1 := frobenius_sq_eq_one hK' heven hτc
  have h0 : NoA6 (pslFieldAut (Fin 3) K τ) := fun D hD => field_three_false hO hK hτ2 hτ hD
  have hc : MulAut.congr (innerDiagonalAction 3 K H) (pslFieldAut (Fin 3) K τ) =
      CatalogueBLinearSemilinear.semilinearAction 3 K A τ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (innerDiagonalAction 3 K H)
      (pslFieldAut (Fin 3) K τ) = _).trans hα.symm
  have := h0.congr' (innerDiagonalAction 3 K H)
  rwa [hc] at this

theorem eq_one_of_card_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    (τ : K ≃+* K) : τ = 1 := by
  by_contra hτ
  have := two_le_of_ringEquiv_ne_one (p := 3) (f := 1) Nat.prime_three le_rfl (by rw [hK]; norm_num)
    hτ
  omega

end CFSG.ComponentClassification.CatFC.PSLSmall
