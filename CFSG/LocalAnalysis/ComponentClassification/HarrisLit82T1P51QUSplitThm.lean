module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUSplitMain

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)

variable {p f : ℕ} {K : Type} [Field K] {n r s : ℕ}

theorem commute_blockScalar (β : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K)))
    (x : GL (Fin r) K × GL (Fin s) K) (c₁ c₂ : Kˣ) :
    blockConj β x * blockScalar β c₁ c₂ = blockScalar β c₁ c₂ * blockConj β x := by
  rw [blockScalar, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext (commute_scalar c₁ x.1).eq (commute_scalar c₂ x.2).eq

theorem blockConj_eq_scalar (β : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K)))
    {x : GL (Fin r) K × GL (Fin s) K} {c : Kˣ}
    (hx : blockConj β x = GeneralLinearGroup.scalar (Fin n) c) (w : (Fin r → K) × (Fin s → K)) :
    ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ w.1, (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ w.2) =
      (c : K) • w := by
  have h1 := apply_blockConj_mulVec β x (β.symm w)
  rw [hx, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec,
    one_mulVec, map_smul, LinearEquiv.apply_symm_apply] at h1
  exact h1.symm

variable (h : UnitaryFieldData p f K)

theorem evenCent_unitary_split (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f) {X : Type} [Group X]
    (π : gramSU h (idGram K n) →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 ↔ s ∈ normOneScalars h (gramSU h (idGram K n)) n)
    (a : gramSU h (idGram K n)) {l : K} (hl0 : l ≠ 0)
    (hAA : unitaryOp (suOp h a) * unitaryOp (suOp h a) = (l ^ 2) • 1) (hlN : h.norm l = 1)
    (hr : 1 ≤ finrank K (eigP l (unitaryOp (suOp h a))))
    (hs : 2 ≤ finrank K (eigM l (unitaryOp (suOp h a)))) :
    EvenCentComm X (π a) ∧ EvenCentInv X (π a) := by
  have htwo := two_ne_zero_of_odd h hp2
  have : Finite K := h.finite
  obtain ⟨hc, eP, eM, hF⟩ := exists_split_unitary_coord h hp2 a hl0 hAA hlN
  set β := eigCoord hc eP eM
  have hn : 0 < n := by
    have := Submodule.finrank_add_eq_of_isCompl hc
    rw [Module.finrank_fin_fun] at this
    omega
  have hπker : ∀ x, π x = 1 → x ∈ center (gramSU h (idGram K n)) := fun x hx =>
    normOneScalars_le_center h ((hker x).mp hx)
  set la := Units.mk0 l hl0
  set lb := Units.mk0 (-l) (neg_ne_zero.mpr hl0)
  have ha : (a : GL (Fin n) K) = blockScalar β la lb := coe_eq_blockScalar h a hl0 hc eP eM
  set 𝓜 : Set (Subgroup (gramSU h (idGram K n))) :=
    {M | M = (splitEmbR h β hF).range ∨ (2 ≤ finrank K (eigP l (unitaryOp (suOp h a))) ∧
      M = (splitEmbL h β hF).range)} with h𝓜
  have hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set (gramSU h (idGram K n))) := by
    rintro M (rfl | ⟨-, rfl⟩) _ ⟨M₀, rfl⟩ <;>
    · rw [mem_centralizer_singleton_iff]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ha]
      first
        | rw [coe_splitEmbR]; exact commute_blockScalar β _ la lb
        | rw [coe_splitEmbL]; exact commute_blockScalar β _ la lb
  have hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set (gramSU h (idGram K n))),
      ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    intro M hM x hx m hm
    obtain ⟨y, hy⟩ := exists_block_of_mem_centralizer h htwo a hl0 hc eP eM hx
    have hiso := block_isometry_split h β hF (hy.symm ▸ x.2)
    rcases hM with rfl | ⟨-, rfl⟩
    · obtain ⟨M₀, rfl⟩ := hm
      refine ⟨⟨y.2 * M₀ * y.2⁻¹, conj_mem_gramSU_one h hiso.2 M₀.2⟩, Subtype.ext ?_⟩
      rw [coe_splitEmbR, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_splitEmbR,
        ← hy, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    · obtain ⟨M₀, rfl⟩ := hm
      refine ⟨⟨y.1 * M₀ * y.1⁻¹, conj_mem_gramSU_one h hiso.1 M₀.2⟩, Subtype.ext ?_⟩
      rw [coe_splitEmbL, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_splitEmbL,
        ← hy, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
  have hQ : ∀ M ∈ 𝓜, IsQuasisimple M := by
    rintro M (rfl | ⟨hr2, rfl⟩)
    · exact LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective (splitEmbR_injective h β hF)) (isQuasisimple_gramSU_one h hs hq)
    · exact LocalCores.isQuasisimple_of_mulEquiv
        (MonoidHom.ofInjective (splitEmbL_injective h β hF)) (isQuasisimple_gramSU_one h hr2 hq)
  have hsq : ∀ {m : ℕ} (hm : 2 ≤ m), ∃ M : gramSU h (1 : Matrix (Fin m) (Fin m) K),
      M ^ 4 = 1 ∧ M ≠ 1 := by
    intro m hm
    have h01 : (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := fun h1 =>
      absurd (congrArg Fin.val h1) (by simp)
    obtain ⟨M, hMe, hM⟩ := unitSignDiag_mem h h01
    refine ⟨⟨M, hM⟩, Subtype.ext (Units.ext ?_), fun h1 => ?_⟩
    · rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hMe, diagonal_pow]
      simp only [Subgroup.coe_one, Units.val_one]
      rw [← diagonal_one]
      congr 1
      funext i
      simp only [unitSignDiag, Pi.pow_apply]
      split_ifs <;> norm_num
    · have h2 := congrArg (fun g : gramSU h (1 : Matrix (Fin m) (Fin m) K) =>
        ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) ⟨0, by omega⟩ ⟨0, by omega⟩) h1
      simp only [hMe, Subgroup.coe_one, Units.val_one, one_apply_eq, diagonal_apply_eq,
        unitSignDiag] at h2
      simp at h2
      exact htwo (by rw [show (2 : K) = 1 - (-1) by ring, h2, sub_self])
  have hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1 := by
    rintro M (rfl | ⟨hr2, rfl⟩)
    · obtain ⟨M₀, hM4, hM1⟩ := hsq hs
      refine ⟨splitEmbR h β hF M₀, ⟨M₀, rfl⟩, fun h1 => hM1 ?_, by rw [← map_pow, hM4, map_one]⟩
      obtain ⟨c, -, -, hcm⟩ := (hker _).mp h1
      have h2 := blockConj_eq_scalar β hcm
      have hc1 : (c : K) = 1 := by
        have h3 := congrArg (fun w => w.1 ⟨0, by omega⟩) (h2 (Pi.single ⟨0, by omega⟩ 1, 0))
        simpa using h3.symm
      refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.mpr fun v => ?_))
      have h3 := congrArg Prod.snd (h2 (0, v))
      simpa [hc1] using h3
    · obtain ⟨M₀, hM4, hM1⟩ := hsq hr2
      refine ⟨splitEmbL h β hF M₀, ⟨M₀, rfl⟩, fun h1 => hM1 ?_, by rw [← map_pow, hM4, map_one]⟩
      obtain ⟨c, -, -, hcm⟩ := (hker _).mp h1
      have h2 := blockConj_eq_scalar β hcm
      have hc1 : (c : K) = 1 := by
        have h3 := congrArg (fun w => w.2 ⟨0, by omega⟩) (h2 (0, Pi.single ⟨0, by omega⟩ 1))
        simpa using h3.symm
      refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.mpr fun v => ?_))
      have h3 := congrArg Prod.fst (h2 (v, 0))
      simpa [hc1] using h3
  have hq2 : 2 ≤ p ^ f := by omega
  have hblock : ∀ g : gramSU h (idGram K n), (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      ∃ c₁ c₂ : K, ∀ v, β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (c₁ • (β v).1, c₂ • (β v).2) := fun g hg =>
    split_unitary_block h β hF hq2 hs g (hg _ (Or.inl rfl)) (fun hr2 => hg _ (Or.inr ⟨hr2, rfl⟩))
  have hcomm : ∀ g g' : gramSU h (idGram K n), (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      (∀ M ∈ 𝓜, ∀ m ∈ M, g' * m = m * g') → g * g' = g' * g := by
    intro g g' hg hg'
    obtain ⟨c₁, c₂, hgc⟩ := hblock g hg
    obtain ⟨d₁, d₂, hgc'⟩ := hblock g' hg'
    refine Subtype.ext (Units.ext (Matrix.ext_iff_mulVec.mpr fun v => β.injective ?_))
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hgc, hgc', hgc', hgc]
    refine Prod.ext ?_ ?_ <;> simp [smul_smul, mul_comm]
  have hinv : ∀ g : gramSU h (idGram K n), (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      π (g * g) = 1 → π g = 1 ∨ π g = π a := by
    intro g hg hgg
    obtain ⟨c₁, c₂, hgc⟩ := hblock g hg
    obtain ⟨ρ, -, -, hρ⟩ := (hker _).mp hgg
    have hgg' : ∀ v, β ((((g * g : gramSU h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v) = (ρ : K) • β v := by
      intro v
      rw [hρ, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec,
        one_mulVec, map_smul]
    have hgg2 : ∀ v, β ((((g * g : gramSU h (idGram K n)) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ v) = ((c₁ * c₁) • (β v).1, (c₂ * c₂) • (β v).2) := by
      intro v
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [← mulVec_mulVec, hgc, hgc, smul_smul, smul_smul]
    have hs₁ : c₁ * c₁ = ρ := by
      have h1 := (hgg2 (β.symm (Pi.single ⟨0, by omega⟩ 1, 0))).symm.trans
        (hgg' (β.symm (Pi.single ⟨0, by omega⟩ 1, 0)))
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 := congrArg (fun w => w.1 ⟨0, by omega⟩) h1
      simpa using h2
    have hs₂ : c₂ * c₂ = ρ := by
      have h1 := (hgg2 (β.symm (0, Pi.single ⟨0, by omega⟩ 1))).symm.trans
        (hgg' (β.symm (0, Pi.single ⟨0, by omega⟩ 1)))
      rw [LinearEquiv.apply_symm_apply] at h1
      have h2 := congrArg (fun w => w.2 ⟨0, by omega⟩) h1
      simpa using h2
    have h3 : (c₁ - c₂) * (c₁ + c₂) = 0 := by linear_combination hs₁ - hs₂
    rcases mul_eq_zero.mp h3 with h4 | h4
    · left
      have hcc : c₁ = c₂ := sub_eq_zero.mp h4
      refine (hker g).mpr (mem_normOneScalars_of_smul h hn (c := c₁) fun v => β.injective ?_)
      rw [hgc, map_smul, hcc]
      rfl
    · right
      have hcc : c₁ = -c₂ := eq_neg_of_add_eq_zero_left h4
      have hainv : ∀ w, β (((a⁻¹ : gramSU h (idGram K n)) : GL (Fin n) K) *ᵥ w) =
          (l⁻¹ • (β w).1, (-l)⁻¹ • (β w).2) := by
        intro w
        have h5 := apply_blockScalar_mulVec β la lb
          ((((a⁻¹ : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w)
        rw [← ha, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, Units.val_one, one_mulVec] at h5
        rw [h5]
        simp [la, lb, smul_smul, inv_mul_cancel₀ hl0]
      have h6 : π (g * a⁻¹) = 1 := (hker _).mpr (mem_normOneScalars_of_smul h hn
        (c := -c₂ / l) fun v => β.injective (by
          simp only [Subgroup.coe_mul, Units.val_mul]
          rw [← mulVec_mulVec, hgc, hainv, map_smul, hcc, smul_smul, smul_smul]
          refine Prod.ext ?_ ?_
          · simp only [Prod.smul_fst]
            congr 1
            field_simp
          · simp only [Prod.smul_snd]
            congr 1
            field_simp))
      rw [map_mul, map_inv, mul_inv_eq_one] at h6
      exact h6
  exact ⟨evenCentComm_of_cover π hπ hπker a 𝓜 hC hN hQ hE hcomm,
    evenCentInv_of_cover' π hπ hπker a 𝓜 hC hN hQ hE hinv⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
