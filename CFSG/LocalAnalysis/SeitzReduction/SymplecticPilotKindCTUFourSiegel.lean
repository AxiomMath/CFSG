module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignTwist
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryRoots

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open scoped MatrixGroups

section Mat

variable {F : Type} [Field F] {σ : F ≃+* F} {N : ℕ}

theorem ctuf_map_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) F) :
    (A * B).map σ = A.map σ * B.map σ :=
  Matrix.map_mul (f := (σ : F →+* F))

theorem ctuf_coe_inv_mul (A : SL(N, F)) :
    ((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F) * (A : Matrix (Fin N) (Fin N) F) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

variable (σ) in
@[expose] noncomputable def ctufSiegelMat (A : SL(N, F)) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) F :=
  fromBlocks (A : Matrix (Fin N) (Fin N) F) 0 0
    (((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F).map σ)ᵀ

theorem ctufSiegelMat_one : ctufSiegelMat σ (1 : SL(N, F)) = 1 := by
  rw [ctufSiegelMat, inv_one, Matrix.SpecialLinearGroup.coe_one,
    Matrix.map_one _ (map_zero σ) (map_one σ),
    transpose_one, fromBlocks_one]

theorem ctufSiegelMat_mul (A B : SL(N, F)) :
    ctufSiegelMat σ (A * B) = ctufSiegelMat σ A * ctufSiegelMat σ B := by
  rw [ctufSiegelMat, ctufSiegelMat, ctufSiegelMat, fromBlocks_multiply, _root_.mul_inv_rev,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ctuf_map_mul,
    transpose_mul]
  simp

theorem ctufSiegelMat_isometry (hσ : ∀ c, σ (σ c) = c) (A : SL(N, F)) :
    ((ctufSiegelMat σ A).map σ)ᵀ * gram F N * ctufSiegelMat σ A = gram F N := by
  have h1 : ((A : Matrix (Fin N) (Fin N) F).map σ)ᵀ *
      (((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F).map σ)ᵀ = 1 := by
    rw [← transpose_mul, ← ctuf_map_mul, ctuf_coe_inv_mul, Matrix.map_one _ (map_zero σ)
      (map_one σ), transpose_one]
  have h2 : ((((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F).map σ)ᵀ.map σ)ᵀ *
      (A : Matrix (Fin N) (Fin N) F) = 1 := by
    have hmm : (((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F).map σ).map σ =
        ((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F) := by
      ext i j
      simp [hσ]
    rw [← transpose_map, transpose_transpose, hmm, ctuf_coe_inv_mul]
  have h0 : (0 : Matrix (Fin N) (Fin N) F).map σ = 0 := Matrix.map_zero _ (map_zero σ)
  rw [ctufSiegelMat, fromBlocks_map, fromBlocks_transpose, h0, transpose_zero,
    CFSG.ClassicalInvolution.Models.SymplecticPairs.gram,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, zero_add, mul_one, mul_neg, neg_mul]
  rw [h1, h2, neg_zero]

theorem det_ctufSiegelMat (A : SL(N, F)) : (ctufSiegelMat σ A).det = 1 := by
  rw [ctufSiegelMat, det_fromBlocks_zero₂₁, det_transpose,
    show (((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F).map σ) =
      (σ : F →+* F).mapMatrix ((A⁻¹ : SL(N, F)) : Matrix (Fin N) (Fin N) F) from rfl,
    ← RingHom.map_det, A.2, (A⁻¹).2, map_one, one_mul]

theorem ctufSiegelMat_map {K : Type} [Field K] {ι : K →+* F} (hι : ∀ c, σ (ι c) = ι c)
    (x : SL(N, K)) :
    ctufSiegelMat σ (SpecialLinearGroup.map ι x) =
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat N K (leviEmbedSL K N x)).map ι := by
  rw [mat_leviEmbedSL, fromBlocks_map, ctufSiegelMat, ← map_inv, Matrix.map_zero _ (map_zero ι)]
  congr 1
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  ext i j
  simp only [transpose_apply, Matrix.map_apply, hι]

theorem ctufSiegelMat_map_self (A : SL(N, F)) :
    (ctufSiegelMat σ A).map σ = ctufSiegelMat σ (SpecialLinearGroup.map (σ : F →+* F) A) := by
  rw [ctufSiegelMat, ctufSiegelMat, fromBlocks_map, ← map_inv, Matrix.map_zero _ (map_zero σ)]
  congr 1

end Mat

section Embed

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {N ε : ℕ}

omit [CharP F 2] in
theorem ctuf_ctuEmbedMat_map (y : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) F) :
    (ctuEmbedMat ε (RingHom.id F) y).map σ = ctuEmbedMat ε (RingHom.id F) (y.map σ) := by
  ext a b
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [Matrix.map_apply, ctuEmbedMat_apply, ctuEmbedMat_apply]
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁]
    rfl
  · rw [fromBlocks_apply₁₂, fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
  · rw [fromBlocks_apply₂₁, fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
  · rw [fromBlocks_apply₂₂, fromBlocks_apply₂₂]
    by_cases h : i = j
    · rw [h, one_apply_eq, map_one]
    · rw [one_apply_ne h, map_zero]

theorem ctufSiegel_isometry (hσ : ∀ c, σ (σ c) = c) (hε : ε ≤ 1) (A : SL(N, F)) :
    conjTr σ (ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A)) * antidiag (2 * N + ε) *
      ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A) = antidiag (2 * N + ε) := by
  rw [conjTr, ctuf_ctuEmbedMat_map, ctuEmbedMat_transpose,
    antidiag_eq_ctuEmbedMat_gram hε (RingHom.id F), ← ctuEmbedMat_mul, ← ctuEmbedMat_mul,
    ctufSiegelMat_isometry hσ]

variable (σ) in
@[expose] noncomputable def ctufSiegel (hσ : ∀ c, σ (σ c) = c) (ε : ℕ) (hε : ε ≤ 1) :
    SL(N, F) →* SU σ (2 * N + ε) where
  toFun A := ⟨⟨ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A),
      ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A⁻¹),
      by rw [← ctuEmbedMat_mul, ← ctufSiegelMat_mul, mul_inv_cancel, ctufSiegelMat_one,
        ctuEmbedMat_one],
      by rw [← ctuEmbedMat_mul, ← ctufSiegelMat_mul, inv_mul_cancel, ctufSiegelMat_one,
        ctuEmbedMat_one]⟩,
    by
      change (ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A)).det = 1
      rw [det_ctuEmbedMat, det_ctufSiegelMat, map_one],
    ctufSiegel_isometry hσ hε A⟩
  map_one' := Subtype.ext (Units.ext (by
    change ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ 1) = 1
    rw [ctufSiegelMat_one, ctuEmbedMat_one]))
  map_mul' A B := Subtype.ext (Units.ext (by
    change ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ (A * B)) =
      ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A) *
        ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ B)
    rw [ctufSiegelMat_mul, ctuEmbedMat_mul]))

variable {hσ : ∀ c, σ (σ c) = c} {hε : ε ≤ 1}

theorem coe_ctufSiegel (A : SL(N, F)) :
    ((ctufSiegel σ hσ ε hε A : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) =
      (ctuEmbedMat ε (RingHom.id F) (ctufSiegelMat σ A) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) := rfl

theorem ctufSiegel_apply_ctuCoord (A : SL(N, F)) (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    ((ctufSiegel σ hσ ε hε A : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w) (ctuCoord N ε w') =
        fromBlocks (ctufSiegelMat σ A) 0 0 1 w w' := by
  rw [coe_ctufSiegel, ctuEmbedMat_apply]
  rfl

theorem ctufSiegel_injective : Function.Injective (ctufSiegel (N := N) σ hσ ε hε) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have h1 := congrArg (fun x : SU σ (2 * N + ε) => ((x : GL (Fin (2 * N + ε)) F) :
    Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε (Sum.inl (Sum.inl i)))
      (ctuCoord N ε (Sum.inl (Sum.inl j)))) h
  simp only [ctufSiegel_apply_ctuCoord, fromBlocks_apply₁₁, ctufSiegelMat] at h1
  exact h1

theorem ctufSiegel_map {K : Type} [Field K] [CharP K 2] {ι : K →+* F}
    (hι : ∀ c, σ (ι c) = ι c) (x : SL(N, K)) :
    ctufSiegel σ hσ ε hε (SpecialLinearGroup.map ι x) =
      ctuEmbed ε hε σ ι hι (leviEmbedSL K N x) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctufSiegel, coe_ctuEmbed, ctufSiegelMat_map hι]
  rfl

theorem ctuaBarAut_ctufSiegel (A : SL(N, F)) :
    ctuaBarAut σ hσ (2 * N + ε) (ctufSiegel σ hσ ε hε A) =
      ctufSiegel σ hσ ε hε (SpecialLinearGroup.map (σ : F →+* F) A) := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_ctuaBarAut, coe_glAut, coe_ctufSiegel, coe_ctufSiegel, ctuf_ctuEmbedMat_map,
    ctufSiegelMat_map_self]

end Embed

section Blocks

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {N ε : ℕ} {hσ : ∀ c, σ (σ c) = c}
  {hε : ε ≤ 1}

omit [CharP F 2] in
theorem ctuf_one_ctuCoord (w w' : (Fin N ⊕ Fin N) ⊕ Fin ε) :
    (1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w) (ctuCoord N ε w') =
      fromBlocks (fromBlocks (1 : Matrix (Fin N) (Fin N) F) 0 0 1) 0 0
        (1 : Matrix (Fin ε) (Fin ε) F) w w' := by
  rw [fromBlocks_one, fromBlocks_one]
  by_cases h : w = w'
  · subst h
    rw [one_apply_eq, one_apply_eq]
  · rw [one_apply_ne h, one_apply_ne ((ctuCoord N ε).injective.ne h)]

theorem ctufSiegel_apply_eq_one {B : Finset (Fin N)} {A : SL(N, F)}
    (hA : A ∈ blockSpecialLinear B) {w w' : (Fin N ⊕ Fin N) ⊕ Fin ε}
    (h : ¬ ∃ u v : Fin N ⊕ Fin N, w = Sum.inl u ∧ w' = Sum.inl v ∧ planeOf u ∈ B ∧
      planeOf v ∈ B) :
    ((ctufSiegel σ hσ ε hε A : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w) (ctuCoord N ε w') =
        (1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w) (ctuCoord N ε w') := by
  rw [ctufSiegel_apply_ctuCoord, ctuf_one_ctuCoord]
  have hAi : A⁻¹ ∈ blockSpecialLinear B := inv_mem hA
  rcases w with u | x <;> rcases w' with v | y
  · rw [fromBlocks_apply₁₁, fromBlocks_apply₁₁]
    have huv : ¬ (planeOf u ∈ B ∧ planeOf v ∈ B) := fun h' => h ⟨u, v, rfl, rfl, h'.1, h'.2⟩
    rcases u with i | i <;> rcases v with j | j
    · rw [ctufSiegelMat, fromBlocks_apply₁₁, fromBlocks_apply₁₁, hA i j (not_and_or.1 huv)]
    · rw [ctufSiegelMat, fromBlocks_apply₁₂, fromBlocks_apply₁₂]
    · rw [ctufSiegelMat, fromBlocks_apply₂₁, fromBlocks_apply₂₁]
    · rw [ctufSiegelMat, fromBlocks_apply₂₂, fromBlocks_apply₂₂, transpose_apply, Matrix.map_apply,
        hAi j i (Or.symm (not_and_or.1 huv))]
      by_cases hij : i = j
      · subst hij
        rw [one_apply_eq, map_one]
      · rw [one_apply_ne (Ne.symm hij), one_apply_ne hij, map_zero]
  · rw [fromBlocks_apply₁₂, fromBlocks_apply₁₂]
  · rw [fromBlocks_apply₂₁, fromBlocks_apply₂₁]
  · rw [fromBlocks_apply₂₂, fromBlocks_apply₂₂]

theorem ctufSiegel_mem_ctuBlock {B R : Finset (Fin N)} (hBR : ∀ p ∈ R, p ∉ B) {A : SL(N, F)}
    (hA : A ∈ blockSpecialLinear B) : ctufSiegel σ hσ ε hε A ∈ ctuBlock σ ε R := by
  rw [mem_ctuBlock]
  intro a b hab
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  rw [ctuCoord_mem_ctuPlanes, ctuCoord_mem_ctuPlanes] at hab
  refine ctufSiegel_apply_eq_one hA ?_
  rintro ⟨u, v, rfl, rfl, hu, hv⟩
  rcases hab with h | h
  · exact hBR _ h hu
  · exact hBR _ h hv

theorem ctufSiegel_commute_ctuEmbed_diagSp {K : Type} [Field K] [CharP K 2] {ι : K →+* F}
    {hι : ∀ c, σ (ι c) = ι c} {B : Finset (Fin N)} {A : SL(N, F)}
    (hA : A ∈ blockSpecialLinear B) {t : Fin N → Kˣ} (ht : ∀ i ∈ B, ∀ j ∈ B, t i = t j) :
    ctufSiegel σ hσ ε hε A * ctuEmbed ε hε σ ι hι (diagSp K N t) =
      ctuEmbed ε hε σ ι hι (diagSp K N t) * ctufSiegel σ hσ ε hε A := by
  apply mat_injective
  rw [map_mul, map_mul, mat_ctuEmbed_diagSp, mat_apply]
  ext a b
  rw [mul_diagonal, diagonal_mul]
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective b
  by_cases hd : ctuDiag ε ι t (ctuCoord N ε w) = ctuDiag ε ι t (ctuCoord N ε w')
  · rw [hd, mul_comm]
  · suffices h0 : ((ctufSiegel σ hσ ε hε A : GL (Fin (2 * N + ε)) F) :
        Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε w) (ctuCoord N ε w') = 0 by
      rw [h0, zero_mul, mul_zero]
    by_cases hB : ∃ u v : Fin N ⊕ Fin N, w = Sum.inl u ∧ w' = Sum.inl v ∧ planeOf u ∈ B ∧
        planeOf v ∈ B
    · obtain ⟨u, v, rfl, rfl, hu, hv⟩ := hB
      rcases u with i | i <;> rcases v with j | j
      · exact absurd (by rw [ctuDiag_inl_inl, ctuDiag_inl_inl, ht i hu j hv]) hd
      · rw [ctufSiegel_apply_ctuCoord, fromBlocks_apply₁₁, ctufSiegelMat, fromBlocks_apply₁₂,
          Matrix.zero_apply]
      · rw [ctufSiegel_apply_ctuCoord, fromBlocks_apply₁₁, ctufSiegelMat, fromBlocks_apply₂₁,
          Matrix.zero_apply]
      · exact absurd (by rw [ctuDiag_inl_inr, ctuDiag_inl_inr, ht i hu j hv]) hd
    · rw [ctufSiegel_apply_eq_one hA hB]
      exact one_apply_ne fun h' => hd (by rw [h'])

end Blocks

end CFSG.SeitzReduction.SymplecticPilot
