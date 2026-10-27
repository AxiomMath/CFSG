module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUSplit
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUGP

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n r s : ℕ}

theorem isometry_inv {m : ℕ} {y : GL (Fin m) K}
    (hy : ∀ u u', gramForm h 1 ((y : Matrix (Fin m) (Fin m) K) *ᵥ u)
      ((y : Matrix (Fin m) (Fin m) K) *ᵥ u') = gramForm h 1 u u') (u u' : Fin m → K) :
    gramForm h 1 (((y⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ u)
      (((y⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ u') = gramForm h 1 u u' := by
  have h1 : ∀ v, (y : Matrix (Fin m) (Fin m) K) *ᵥ
      (((y⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v) = v := fun v => by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [← hy, h1, h1]

theorem conj_mem_gramSU_one {m : ℕ} {y : GL (Fin m) K}
    (hy : ∀ u u', gramForm h 1 ((y : Matrix (Fin m) (Fin m) K) *ᵥ u)
      ((y : Matrix (Fin m) (Fin m) K) *ᵥ u') = gramForm h 1 u u')
    {M : GL (Fin m) K} (hM : M ∈ gramSU h (1 : Matrix (Fin m) (Fin m) K)) :
    y * M * y⁻¹ ∈ gramSU h (1 : Matrix (Fin m) (Fin m) K) := by
  obtain ⟨hMi, hMd⟩ := mem_gramSU_iff_isometry.mp hM
  refine mem_gramSU_iff_isometry.mpr ⟨fun u u' => ?_, ?_⟩
  · simp only [Units.val_mul, ← mulVec_mulVec]
    rw [hy, hMi, isometry_inv h hy]
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hMd, mul_one, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]

section main

variable (β : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K)))
  (hF : ∀ v w, gramForm h 1 v w = gramForm h 1 (β v).1 (β w).1 + gramForm h 1 (β v).2 (β w).2)

theorem block_rel {g : gramSU h (idGram K n)} {x : GL (Fin r) K × GL (Fin s) K}
    (hx : blockConj β x ∈ gramSU h (idGram K n))
    (hgx : g * ⟨blockConj β x, hx⟩ = ⟨blockConj β x, hx⟩ * g) (w : (Fin r → K) × (Fin s → K)) :
    β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      β.symm ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ w.1, (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ w.2))
      = ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ (β (((g : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ β.symm w)).1,
        (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ (β (((g : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ β.symm w)).2) := by
  have hgx' : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    congrArg (fun y : gramSU h (idGram K n) => ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      hgx
  have h1 := apply_blockConj_mulVec β x (β.symm w)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply, mulVec_mulVec, hgx', ← mulVec_mulVec,
    apply_blockConj_mulVec]

theorem split_unitary_block (hq2 : 2 ≤ p ^ f) (hs : 2 ≤ s) (g : gramSU h (idGram K n))
    (h₂ : ∀ m ∈ (splitEmbR h β hF).range, g * m = m * g)
    (h₁ : 2 ≤ r → ∀ m ∈ (splitEmbL h β hF).range, g * m = m * g) :
    ∃ c₁ c₂ : K, ∀ v, β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      (c₁ • (β v).1, c₂ • (β v).2) := by
  obtain ⟨c, hcN, hc2⟩ := RankThree.PartOne.KCUnitary.exists_norm_one_sq_ne_one h hq2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcN
    exact zero_ne_one hcN
  have hc1 : c ≠ 1 := fun h1 => hc2 (by rw [h1, one_pow])
  have hcc : c * c ≠ 1 := fun h1 => hc2 (by rw [sq, h1])
  set gL : ((Fin r → K) × (Fin s → K)) →ₗ[K] ((Fin r → K) × (Fin s → K)) :=
    β.toLinearMap ∘ₗ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin ∘ₗ
      β.symm.toLinearMap
  have hgL : ∀ w, gL w = β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ β.symm w) :=
    fun _ => rfl
  have hR : ∀ D : GL (Fin s) K, D ∈ gramSU h (1 : Matrix (Fin s) (Fin s) K) → ∀ w,
      gL (w.1, (D : Matrix (Fin s) (Fin s) K) *ᵥ w.2) =
        ((gL w).1, (D : Matrix (Fin s) (Fin s) K) *ᵥ (gL w).2) := by
    intro D hD w
    have := block_rel h β (x := (1, D)) (splitEmbR h β hF ⟨D, hD⟩).2
      (h₂ _ ⟨⟨D, hD⟩, rfl⟩) w
    rw [hgL, hgL]
    simpa only [Units.val_one, one_mulVec] using this
  obtain ⟨⟨c₂, hc₂⟩, hz⟩ := prod_unitary_commutant hs hc0 hc1 hcc gL
    (fun i j hij w => by
      obtain ⟨D, hDe, hD⟩ := unitLambdaDiag_mem h hcN hij
      rw [← hDe]
      exact hR D hD w)
    (fun i j hij w => by
      obtain ⟨D, hDe, hD⟩ := unitSignedSwapMatrix_mem h hij
      rw [← hDe]
      exact hR D hD w)
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : K, ∀ u, gL (u, 0) = (c₁ • u, 0) := by
    rcases Nat.lt_or_ge r 2 with hr | hr
    · obtain ⟨c₁, hc⟩ := linear_fin_le_one (by omega : r ≤ 1)
        ((LinearMap.fst K _ _) ∘ₗ gL ∘ₗ (LinearMap.inl K _ _))
      exact ⟨c₁, fun u => Prod.ext (hc u) (hz u)⟩
    · have hL : ∀ D : GL (Fin r) K, D ∈ gramSU h (1 : Matrix (Fin r) (Fin r) K) → ∀ w,
          gL ((D : Matrix (Fin r) (Fin r) K) *ᵥ w.1, w.2) =
            ((D : Matrix (Fin r) (Fin r) K) *ᵥ (gL w).1, (gL w).2) := by
        intro D hD w
        have := block_rel h β (x := (D, 1)) (splitEmbL h β hF ⟨D, hD⟩).2
          (h₁ hr _ ⟨⟨D, hD⟩, rfl⟩) w
        rw [hgL, hgL]
        simpa only [Units.val_one, one_mulVec] using this
      exact (prod_unitary_commutant_fst hr hc0 hc1 hcc gL
        (fun i j hij w => by
          obtain ⟨D, hDe, hD⟩ := unitLambdaDiag_mem h hcN hij
          rw [← hDe]
          exact hL D hD w)
        (fun i j hij w => by
          obtain ⟨D, hDe, hD⟩ := unitSignedSwapMatrix_mem h hij
          rw [← hDe]
          exact hL D hD w)).1
  refine ⟨c₁, c₂, fun v => ?_⟩
  have h1 : β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) = gL (β v) := by
    rw [hgL, LinearEquiv.symm_apply_apply]
  have h2 : β v = ((β v).1, 0) + (0, (β v).2) := by simp
  rw [h1, h2, map_add, hc₁, hc₂]
  simp

end main

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
