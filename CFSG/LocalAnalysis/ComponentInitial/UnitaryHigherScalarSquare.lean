module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareForms
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarSquareSplit

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module

theorem odd_symplectic_scalar_square_centralizer_structure {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {r : ℕ} (hr : 1 ≤ r)
    (hdim : finrank K V = 2 * r) {B : LinearMap.BilinForm K V} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {A : LinearMap.GeneralLinearGroup K V}
    (hAns : ∀ c : K, (A : Module.End K V) ≠ c • 1) {d : K} (hd0 : d ≠ 0)
    (hAA : (A : Module.End K V) * (A : Module.End K V) = d • 1) {μ : K}
    (hAμ : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = μ * B v w) :
    (μ / d = 1 ∨ μ / d = -1) ∧
    (∀ l : K, l ^ 2 = d →
      eigenPlus l (A : Module.End K V) ≠ ⊥ ∧ eigenMinus l (A : Module.End K V) ≠ ⊥ ∧
      (μ / d = 1 →
        (∀ v ∈ eigenPlus l (A : Module.End K V), ∀ w ∈ eigenMinus l (A : Module.End K V),
          B v w = 0) ∧
        (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
          (eigenPlus l (A : Module.End K V))).IsAlt ∧
        (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
          (eigenMinus l (A : Module.End K V))).IsAlt ∧
        (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
          (eigenPlus l (A : Module.End K V))).Nondegenerate ∧
        (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
          (eigenMinus l (A : Module.End K V))).Nondegenerate ∧
        ∃ e : similitudeCentralizer B A ≃*
            sesqUnitaryGroup (B.domRestrict₁₂ (eigenPlus l (A : Module.End K V))
              (eigenPlus l (A : Module.End K V))) ×
            sesqUnitaryGroup (B.domRestrict₁₂ (eigenMinus l (A : Module.End K V))
              (eigenMinus l (A : Module.End K V))),
          ∀ g : similitudeCentralizer B A,
            (eigenPlus l (A : Module.End K V)).subtype ∘ₗ
                (((e g).1 : LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V))) :
                  Module.End K (eigenPlus l (A : Module.End K V))) =
              ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ
                (eigenPlus l (A : Module.End K V)).subtype ∧
            (eigenMinus l (A : Module.End K V)).subtype ∘ₗ
                (((e g).2 : LinearMap.GeneralLinearGroup K (eigenMinus l (A : Module.End K V))) :
                  Module.End K (eigenMinus l (A : Module.End K V))) =
              ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ
                (eigenMinus l (A : Module.End K V)).subtype) ∧
      (μ / d = -1 →
        (∀ v ∈ eigenPlus l (A : Module.End K V), ∀ w ∈ eigenPlus l (A : Module.End K V),
          B v w = 0) ∧
        (∀ v ∈ eigenMinus l (A : Module.End K V), ∀ w ∈ eigenMinus l (A : Module.End K V),
          B v w = 0) ∧
        finrank K (eigenPlus l (A : Module.End K V)) = r ∧
        finrank K (eigenMinus l (A : Module.End K V)) = r ∧
        (∀ v ∈ eigenPlus l (A : Module.End K V),
          (∀ w ∈ eigenMinus l (A : Module.End K V), B v w = 0) → v = 0) ∧
        (∀ w ∈ eigenMinus l (A : Module.End K V),
          (∀ v ∈ eigenPlus l (A : Module.End K V), B v w = 0) → w = 0) ∧
        ∃ e : similitudeCentralizer B A ≃*
            LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V)),
          (∀ g : similitudeCentralizer B A,
            (eigenPlus l (A : Module.End K V)).subtype ∘ₗ
                ((e g : LinearMap.GeneralLinearGroup K (eigenPlus l (A : Module.End K V))) :
                  Module.End K (eigenPlus l (A : Module.End K V))) =
              ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) ∘ₗ
                (eigenPlus l (A : Module.End K V)).subtype) ∧
          (∀ (g : similitudeCentralizer B A) (w : V), w ∈ eigenMinus l (A : Module.End K V) →
            ∀ w' ∈ eigenMinus l (A : Module.End K V),
              ((∀ v ∈ eigenPlus l (A : Module.End K V),
                B (((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v) w' = B v w) ↔
                w' = ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) w)))) ∧
    ((∀ l : K, l ^ 2 ≠ d) →
      (∀ x : Module.End K V,
        x ∈ scalarSquareField (A : Module.End K V) ↔ ∃ a b : K, x = a • 1 + b • A) ∧
      IsField (scalarSquareField (A : Module.End K V)) ∧
      Nat.card (scalarSquareField (A : Module.End K V)) = (ℓ ^ f) ^ 2 ∧
      finrank (scalarSquareField (A : Module.End K V)) V = r ∧
      ∃ bar : scalarSquareField (A : Module.End K V) →+* scalarSquareField (A : Module.End K V),
        (∀ (x : scalarSquareField (A : Module.End K V)) (a b : K),
          (x : Module.End K V) = a • 1 + b • A → (bar x : Module.End K V) = a • 1 - b • A) ∧
        (∀ x, bar x = x ^ (ℓ ^ f)) ∧ (∀ x, bar (bar x) = x) ∧
        (μ / d = 1 → ∃ BE : LinearMap.BilinForm (scalarSquareField (A : Module.End K V)) V,
          (∀ v w, (BE v w : Module.End K V) =
            B v w • 1 + (d⁻¹ * B ((A : Module.End K V) v) w) • A) ∧
          BE.IsAlt ∧ BE.Nondegenerate ∧ Even r ∧
          ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
            g ∈ Subgroup.centralizer {A} ∧
              ∀ v w, BE ((g : Module.End K V) v) ((g : Module.End K V) w) = BE v w) ∧
        (μ / d = -1 → ∃ hf : V →ₛₗ[bar] V →ₗ[scalarSquareField (A : Module.End K V)]
            scalarSquareField (A : Module.End K V),
          (∀ v w, (hf v w : Module.End K V) = B v ((A : Module.End K V) w) • 1 + B v w • A) ∧
          hf.IsSymm ∧ hf.SeparatingLeft ∧
          ∀ g : LinearMap.GeneralLinearGroup K V, g ∈ similitudeCentralizer B A ↔
            g ∈ Subgroup.centralizer {A} ∧
              ∀ v w, hf ((g : Module.End K V) v) ((g : Module.End K V) w) = hf v w)) := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h3 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K ℓ] at h3
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h3)
  have hε := multiplier_ratio hBnd hd0 hAA hAμ
  refine ⟨hε, fun l hld => ?_, fun hd => ?_⟩
  ·
    have hl0 : l ≠ 0 := by
      rintro rfl
      rw [zero_pow two_ne_zero] at hld
      exact hd0 hld.symm
    have hAA' : (A : Module.End K V) * (A : Module.End K V) = (l ^ 2) • 1 := by
      rw [hld]
      exact hAA
    obtain ⟨hP, hM⟩ := eigen_ne_bot h2 hl0 hAA' hAns
    refine ⟨hP, hM, fun h1 => ?_, fun h1 => ?_⟩
    · have hTB : ∀ v w, B (invSMulOp l (A : Module.End K V) v)
          (invSMulOp l (A : Module.End K V) w) = B v w := fun v w => by
        rw [bilin_invSMulOp hld hAμ, h1, one_mul]
      exact exists_bilin_split_equiv h2 hB hBnd hl0 hAA' hTB
    · have hTB : ∀ v w, B (invSMulOp l (A : Module.End K V) v)
          (invSMulOp l (A : Module.End K V) w) = -B v w := fun v w => by
        rw [bilin_invSMulOp hld hAμ, h1, neg_one_mul]
      obtain ⟨i1, i2, hPM, hdim2, i5, i6, e, he1, he2⟩ :=
        exists_bilin_paired_equiv h2 hB hBnd hl0 hAA' hTB
      exact ⟨i1, i2, by omega, by omega, i5, i6, e, he1, he2⟩
  ·
    have hF := isField_scalarSquareField hAA hd
    have := Fintype.ofFinite K
    have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
    have h2' : ringChar K ≠ 2 := by
      rw [ringChar.eq K ℓ]
      exact hℓ2
    have hcharE := charP_scalarSquareField (A := (A : Module.End K V)) (ℓ := ℓ)
    obtain ⟨bar, hbardef⟩ : ∃ bar : scalarSquareField (A : Module.End K V) →+*
        scalarSquareField (A : Module.End K V),
        bar = iterateFrobenius (scalarSquareField (A : Module.End K V)) ℓ f := ⟨_, rfl⟩
    have hbarpow : ∀ x, bar x = x ^ (ℓ ^ f) := fun x => by
      rw [hbardef, iterateFrobenius_def]
    have hbar : ∀ (x : scalarSquareField (A : Module.End K V)) (a b : K),
        (x : Module.End K V) = a • 1 + b • A → (bar x : Module.End K V) = a • 1 - b • A := by
      intro x a b hx
      have hx' : x = ⟨a • 1 + b • A, smul_add_smul_mem a b⟩ := Subtype.ext hx
      rw [hbarpow, hx', pow_card_scalarSquare hcardK h2' hAA hd0 hd]
    have hbarbar : ∀ x, bar (bar x) = x := by
      intro x
      obtain ⟨a, b, hab⟩ := (mem_scalarSquareField_iff hAA).mp x.2
      apply Subtype.ext
      rw [hbar (bar x) a (-b) (by rw [hbar x a b hab, neg_smul, sub_eq_add_neg]), neg_smul,
        sub_neg_eq_add, hab]
    refine ⟨fun x => mem_scalarSquareField_iff hAA, hF,
      by rw [card_scalarSquareField hAns hAA, hK],
      finrank_scalarSquareField hAns hAA hd hdim, bar, hbar, hbarpow, hbarbar,
      fun h1 => ?_, fun h1 => ?_⟩
    ·
      have hadj : ∀ v w, B ((A : Module.End K V) v) w = B v ((A : Module.End K V) w) :=
        fun v w => by rw [bilin_adjoint hd0 hAA hAμ, h1, one_mul]
      obtain ⟨BE, hBE⟩ := exists_altFieldBilin hAA hd0 hadj
      have hBEalt : BE.IsAlt := fun v => by
        rw [hBE]
        exact altFieldForm_self h2 hB hadj v
      have hBEnd : BE.Nondegenerate :=
        ⟨fun v hv => hBnd.1 v fun w => altFieldForm_eq_zero hAns (by rw [← hBE]; exact hv w),
          fun w hw => hBnd.2 w fun v => altFieldForm_eq_zero hAns (by rw [← hBE]; exact hw v)⟩
      have hEven : Even r := by
        let _ : Field (scalarSquareField (A : Module.End K V)) := hF.toField
        have : Finite V := Module.finite_of_finite K
        have : Module.Finite (scalarSquareField (A : Module.End K V)) V := Module.Finite.of_finite
        have h3 := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.even_finrank BE
          hBEalt hBEnd
        rwa [finrank_scalarSquareField hAns hAA hd hdim] at h3
      refine ⟨BE, fun v w => by rw [hBE]; rfl, hBEalt, hBEnd, hEven, fun g => ⟨fun hg =>
        ⟨hg.2, fun v w => ?_⟩, fun ⟨hgc, hgBE⟩ => ⟨fun v w => ?_, hgc⟩⟩⟩
      · rw [hBE, hBE, altFieldForm_eq_iff hAns]
        refine ⟨hg.1 v w, ?_⟩
        rw [← Module.End.mul_apply, ← commute_of_mem_similitudeCentralizer hg,
          Module.End.mul_apply, hg.1]
      · have h3 := hgBE v w
        rw [hBE, hBE, altFieldForm_eq_iff hAns] at h3
        exact h3.1
    ·
      have hadj : ∀ v w, B ((A : Module.End K V) v) w = -B v ((A : Module.End K V) w) :=
        fun v w => by rw [bilin_adjoint hd0 hAA hAμ, h1, neg_one_mul]
      have hμd : μ = -d := by
        field_simp at h1
        linear_combination h1
      have hAμ' : ∀ v w, B ((A : Module.End K V) v) ((A : Module.End K V) w) = -d * B v w :=
        fun v w => by rw [hAμ, hμd]
      obtain ⟨hf, hhf⟩ := exists_hermFieldSesq hAA bar hbar hadj hAμ'
      refine ⟨hf, fun v w => by rw [hhf]; rfl, ⟨fun x y => by
          rw [hhf, hhf]
          exact hermFieldForm_symm hB bar hbar hadj x y⟩,
        fun v hv => hBnd.1 v fun w => hermFieldForm_eq_zero hAns (by rw [← hhf]; exact hv w),
        fun g => ⟨fun hg => ⟨hg.2, fun v w => ?_⟩, fun ⟨hgc, hghf⟩ => ⟨fun v w => ?_, hgc⟩⟩⟩
      · rw [hhf, hhf, hermFieldForm_eq_iff hAns]
        refine ⟨?_, hg.1 v w⟩
        rw [← Module.End.mul_apply (A : Module.End K V), ← commute_of_mem_similitudeCentralizer hg,
          Module.End.mul_apply, hg.1]
      · have h3 := hghf v w
        rw [hhf, hhf, hermFieldForm_eq_iff hAns] at h3
        exact h3.2

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
