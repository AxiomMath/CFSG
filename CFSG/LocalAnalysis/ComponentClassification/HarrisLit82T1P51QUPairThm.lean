module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUPairEmb
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUSplitThm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QLin
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem exists_toGL_eq_conj {m : ℕ} (g : GL (Fin m) K) (w : Matrix.SpecialLinearGroup (Fin m) K) :
    ∃ w' : Matrix.SpecialLinearGroup (Fin m) K,
      Matrix.SpecialLinearGroup.toGL w' = g * Matrix.SpecialLinearGroup.toGL w * g⁻¹ := by
  have hN : (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range.Normal := by
    rw [Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]
    infer_instance
  exact hN.conj_mem _ ⟨w, rfl⟩ g

variable (h : UnitaryFieldData p f K)

theorem evenCent_unitary_paired_core (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f) {X : Type} [Group X]
    (π : gramSU h (idGram K n) →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 ↔ s ∈ normOneScalars h (gramSU h (idGram K n)) n)
    (a : gramSU h (idGram K n)) {l : K} (hl0 : l ≠ 0) {m : ℕ} (hm : 2 ≤ m)
    (β : (Fin n → K) ≃ₗ[K] ((Fin m → K) × (Fin m → K)))
    (hF : ∀ v w, gramForm h 1 v w = gramForm h 1 (β v).1 (β w).2 + gramForm h 1 (β v).2 (β w).1)
    (ha : (a : GL (Fin n) K) = blockScalar β (Units.mk0 l hl0) (Units.mk0 (-l)
      (neg_ne_zero.mpr hl0)))
    (hcent : ∀ x ∈ centralizer ({a} : Set (gramSU h (idGram K n))),
      ∃ y : GL (Fin m) K × GL (Fin m) K, blockConj β y = x) :
    EvenCentComm X (π a) ∧ EvenCentInv X (π a) := by
  have htwo := two_ne_zero_of_odd h hp2
  have : Finite K := h.finite
  have hn0 : 0 < n := by
    have h1 := LinearEquiv.finrank_eq β
    rw [Module.finrank_fin_fun, Module.finrank_prod, Module.finrank_fin_fun] at h1
    omega
  have hcard : Nat.card K = (p ^ f) ^ 2 := h.card_eq_sq
  have h4 : 4 ≤ Nat.card K := by rw [hcard]; nlinarith
  have hπker : ∀ x, π x = 1 → x ∈ center (gramSU h (idGram K n)) := fun x hx =>
    normOneScalars_le_center h ((hker x).mp hx)
  set 𝓜 : Set (Subgroup (gramSU h (idGram K n))) := {(pairEmb h β hF).range} with h𝓜
  have hC : ∀ M ∈ 𝓜, M ≤ centralizer ({a} : Set (gramSU h (idGram K n))) := by
    rintro M rfl _ ⟨y₀, rfl⟩
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha, coe_pairEmb]
    exact commute_blockScalar β _ _ _
  have hN : ∀ M ∈ 𝓜, ∀ x ∈ centralizer ({a} : Set (gramSU h (idGram K n))),
      ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
    rintro M rfl x hx _ ⟨y₀, rfl⟩
    obtain ⟨y, hy⟩ := hcent x hx
    have hy2 := adjInv_of_isometry h β hF (hy.symm ▸ x.2)
    obtain ⟨z, hz⟩ := exists_toGL_eq_conj y.1 y₀
    refine ⟨z, Subtype.ext ?_⟩
    rw [coe_pairEmb, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_pairEmb, ← hy,
      ← map_inv, ← map_mul, ← map_mul, hz]
    congr 1
    refine Prod.ext rfl ?_
    simp only [Prod.snd_mul, Prod.snd_inv, map_mul, map_inv, hy2]
  have hQ : ∀ M ∈ 𝓜, IsQuasisimple M := by
    rintro M rfl
    exact LocalCores.isQuasisimple_of_mulEquiv (MonoidHom.ofInjective (pairEmb_injective h β hF))
      (RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)
  have hE : ∀ M ∈ 𝓜, ∃ m ∈ M, π m ≠ 1 ∧ m ^ 4 = 1 := by
    rintro M rfl
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨ε, hε⟩ : IsSquare (-1 : K) := FiniteField.isSquare_neg_one_iff.mpr (by
      rw [← Nat.card_eq_fintype_card, hcard]
      obtain ⟨t, ht⟩ : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
      rw [ht]
      ring_nf
      omega)
    have hεε : ε * -ε = 1 := by rw [mul_neg, ← hε, neg_neg]
    have hε2 : ε ^ 2 = -1 := by rw [sq, ← hε]
    have hε4 : ε ^ 4 = 1 := by rw [show ε ^ 4 = (ε ^ 2) ^ 2 by ring, hε2]; norm_num
    have hε4' : (-ε) ^ 4 = 1 := by rw [neg_pow, hε4]; norm_num
    set y₀ := diagSL hm ε (-ε) hεε
    refine ⟨pairEmb h β hF y₀, ⟨y₀, rfl⟩, fun h1 => ?_, by
      rw [← map_pow, diagSL_pow_four hm hεε hε4 hε4', map_one]⟩
    obtain ⟨c, -, -, hcm⟩ := (hker _).mp h1
    have h2 := blockConj_eq_scalar β hcm
    have h00 := congrArg (fun w => w.1 ⟨0, by omega⟩) (h2 (Pi.single ⟨0, by omega⟩ 1, 0))
    have h11 := congrArg (fun w => w.1 ⟨1, by omega⟩) (h2 (Pi.single ⟨1, by omega⟩ 1, 0))
    simp only [mulVec_single_one, Prod.smul_mk, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_same, mul_one, MonoidHom.prod_apply, MonoidHom.id_apply, col_apply] at h00 h11
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, diagSL_apply_zero] at h00
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, diagSL_apply_one] at h11
    have h3 : (2 : K) * ε = 0 := by linear_combination h00 - h11
    have hε0 : ε = 0 := (mul_eq_zero.mp h3).resolve_left htwo
    rw [hε0, mul_zero] at hε
    exact one_ne_zero (neg_eq_zero.mp hε)
  obtain ⟨t₀, ht₀⟩ := h.exists_bar_ne
  have hblock : ∀ g : gramSU h (idGram K n), (∀ M ∈ 𝓜, ∀ m ∈ M, g * m = m * g) →
      ∃ c₁ c₂ : K, ∀ v, β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
        (c₁ • (β v).1, c₂ • (β v).2) := by
    intro g hg
    set gL : ((Fin m → K) × (Fin m → K)) →ₗ[K] ((Fin m → K) × (Fin m → K)) :=
      β.toLinearMap ∘ₗ ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVecLin ∘ₗ
        β.symm.toLinearMap
    have hgL : ∀ w, gL w = β (((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ β.symm w) :=
      fun _ => rfl
    obtain ⟨α, α', hα⟩ := prod_twisted_commutant hm h.bar ht₀ gL (fun i j hij t w => by
      set T : Matrix.SpecialLinearGroup (Fin m) K :=
        ⟨transvection i j t, det_transvection_of_ne i j hij t⟩
      have := block_rel h β (x := (Matrix.SpecialLinearGroup.toGL T,
        adjInv h (Matrix.SpecialLinearGroup.toGL T))) (pairEmb h β hF T).2
        (hg _ rfl _ ⟨T, rfl⟩) w
      rw [coe_adjInv_transvection h hij t] at this
      rw [hgL, hgL]
      exact this)
    refine ⟨α, α', fun v => ?_⟩
    have h1 := hα (β v)
    rw [hgL, LinearEquiv.symm_apply_apply] at h1
    exact h1
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
      refine (hker g).mpr (mem_normOneScalars_of_smul h hn0 (c := c₁) fun v => β.injective ?_)
      rw [hgc, map_smul, hcc]
      rfl
    · right
      have hcc : c₁ = -c₂ := eq_neg_of_add_eq_zero_left h4
      have hainv : ∀ w, β (((a⁻¹ : gramSU h (idGram K n)) : GL (Fin n) K) *ᵥ w) =
          (l⁻¹ • (β w).1, (-l)⁻¹ • (β w).2) := by
        intro w
        have h5 := apply_blockScalar_mulVec β (Units.mk0 l hl0) (Units.mk0 (-l)
        (neg_ne_zero.mpr hl0))
          ((((a⁻¹ : gramSU h (idGram K n)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w)
        rw [← ha, mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
          Subgroup.coe_one, Units.val_one, one_mulVec] at h5
        rw [h5]
        simp [smul_smul, inv_mul_cancel₀ hl0]
      have h6 : π (g * a⁻¹) = 1 := (hker _).mpr (mem_normOneScalars_of_smul h hn0
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

theorem evenCent_unitary_paired (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f) {X : Type} [Group X]
    (π : gramSU h (idGram K n) →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 ↔ s ∈ normOneScalars h (gramSU h (idGram K n)) n)
    (a : gramSU h (idGram K n)) {l : K} (hl0 : l ≠ 0)
    (hAA : unitaryOp (suOp h a) * unitaryOp (suOp h a) = (l ^ 2) • 1) (hlN : h.norm l = -1)
    (hn : 3 ≤ n) : EvenCentComm X (π a) ∧ EvenCentInv X (π a) := by
  have htwo := two_ne_zero_of_odd h hp2
  obtain ⟨hc, eP, eM, hF⟩ := exists_paired_unitary_coord h hp2 a hl0 hAA hlN
  have hm : 2 ≤ finrank K (eigP l (unitaryOp (suOp h a))) := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    rw [Module.finrank_fin_fun, eM.finrank_eq, Module.finrank_fin_fun] at h1
    omega
  exact evenCent_unitary_paired_core h hp2 hq π hπ hker a hl0 hm (eigCoord hc eP eM) hF
    (coe_eq_blockScalar h a hl0 hc eP eM)
    (fun x hx => exists_block_of_mem_centralizer h htwo a hl0 hc eP eM hx)

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
