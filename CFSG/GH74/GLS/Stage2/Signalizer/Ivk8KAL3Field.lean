module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL3Aut
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KACover
import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.KGroups.L3Eps
open scoped MatrixGroups

section FixN

variable {n : ℕ} {F : Type} [Field F]

@[expose] noncomputable def kaSlMapN (σ : F ≃+* F) : SL(n, F) →* SL(n, F) :=
  Matrix.SpecialLinearGroup.map σ.toRingHom

theorem mem_kaFix_slMapN {σ : F ≃+* F} {M : SL(n, F)} :
    M ∈ kaFix (kaSlMapN σ) ↔
      ∀ i j, σ ((M : Matrix (Fin n) (Fin n) F) i j) = (M : Matrix (Fin n) (Fin n) F) i j := by
  rw [mem_kaFix]
  constructor
  · intro h i j
    have := congrArg (fun A : SL(n, F) => (A : Matrix (Fin n) (Fin n) F) i j) h
    simpa [kaSlMapN, Matrix.SpecialLinearGroup.map_apply_coe] using this
  · intro h
    apply Subtype.ext
    ext i j
    simpa [kaSlMapN, Matrix.SpecialLinearGroup.map_apply_coe] using h i j

@[expose] noncomputable def kaSlInclN (σ : F ≃+* F) : SL(n, ↥(fixedField σ)) →* SL(n, F) :=
  Matrix.SpecialLinearGroup.map (fixedField σ).subtype

theorem kaSlInclN_injective (σ : F ≃+* F) : Function.Injective (kaSlInclN (n := n) σ) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun C : SL(n, F) => (C : Matrix (Fin n) (Fin n) F) i j) h
  simpa [kaSlInclN, Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem kaFix_slMapN_eq_range (σ : F ≃+* F) :
    kaFix (kaSlMapN (n := n) σ) = (kaSlInclN σ).range := by
  ext M
  constructor
  · intro hM
    rw [mem_kaFix_slMapN] at hM
    have hmem : ∀ i j, (M : Matrix (Fin n) (Fin n) F) i j ∈ fixedField σ :=
      fun i j => (mem_fixedField_iff σ _).mpr (hM i j)
    let A : Matrix (Fin n) (Fin n) (fixedField σ) :=
      Matrix.of fun i j => ⟨(M : Matrix (Fin n) (Fin n) F) i j, hmem i j⟩
    have hAM : (fixedField σ).subtype.mapMatrix A = (M : Matrix (Fin n) (Fin n) F) := by
      ext i j
      rfl
    have hdet : A.det = 1 := by
      apply (fixedField σ).subtype.injective
      rw [RingHom.map_det, hAM, M.2, map_one]
    refine ⟨⟨A, hdet⟩, Subtype.ext ?_⟩
    simp only [kaSlInclN]
    exact hAM
  · rintro ⟨A, rfl⟩
    rw [mem_kaFix_slMapN]
    intro i j
    simp only [kaSlInclN, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact fixedField_apply σ (A i j)

@[expose] noncomputable def kaFixSlEquivN (σ : F ≃+* F) :
    ↥(kaFix (kaSlMapN (n := n) σ)) ≃* SL(n, ↥(fixedField σ)) :=
  (MulEquiv.subgroupCongr (kaFix_slMapN_eq_range σ)).trans
    (MonoidHom.ofInjective (kaSlInclN_injective σ)).symm

theorem kaFix_slMapN_quasisimple (hn : 3 ≤ n) (σ : F ≃+* F) :
    CFSG.IsQuasisimple ↥(kaFix (kaSlMapN (n := n) σ)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (kaFixSlEquivN σ).symm
    (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup hn)

end FixN

section Field3

variable {F : Type} [Field F] [Finite F]

theorem kaL3_eq_one_of_fixed (σ τ : F ≃+* F) (hσ : orderOf σ = 2) (hτ : Odd (orderOf τ))
    (hfix : ∀ t ∈ fixedField σ, τ t = t) : τ = 1 := by
  have hs : Nat.card (fixedField σ) ^ 2 = Nat.card F := by
    have := fixedField_card_pow σ
    rwa [hσ] at this
  have ht := fixedField_card_pow τ
  have hle : Nat.card (fixedField σ) ≤ Nat.card (fixedField τ) := by
    refine Nat.card_le_card_of_injective
      (fun x : fixedField σ => (⟨x.1, (mem_fixedField_iff τ _).mpr (hfix x.1 x.2)⟩ : fixedField τ))
      ?_
    intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have h1 : Nat.card (fixedField σ) ^ orderOf τ ≤ Nat.card (fixedField σ) ^ 2 := by
    calc Nat.card (fixedField σ) ^ orderOf τ
        ≤ Nat.card (fixedField τ) ^ orderOf τ := Nat.pow_le_pow_left hle _
      _ = Nat.card F := ht
      _ = Nat.card (fixedField σ) ^ 2 := hs.symm
  have hq : 1 < Nat.card (fixedField σ) := one_lt_card_fixedField σ
  have h2 : orderOf τ ≤ 2 := (Nat.pow_le_pow_iff_right hq).mp h1
  have h3 := Nat.odd_iff.mp hτ
  have h4 := orderOf_pos τ
  exact orderOf_eq_one_iff.mp (by omega)

omit [Finite F] in
theorem kaTransv_mem {σ : F ≃+* F} {i j : Fin 3} (hij : i ≠ j) :
    Matrix.SpecialLinearGroup.transvection hij (1 : F) ∈ kaFix (kaSlMapN (n := 3) σ) := by
  rw [mem_kaFix_slMapN]
  intro a b
  simp only [Matrix.SpecialLinearGroup.transvection_coe]
  by_cases hab : a = b
  · subst hab
    have : i ≠ a ∨ j ≠ a := by
      by_contra h
      push Not at h
      exact hij (h.1.trans h.2.symm)
    rcases this with h | h
    · simp [h]
    · simp [h]
  · by_cases h : i = a ∧ j = b
    · simp [h, hab]
    · simp [h, hab]

@[expose] noncomputable def kaL3Tr3 (t : F) : SL(3, F) :=
  ⟨!![0, 1, 0; -1, t, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

omit [Finite F] in
theorem kaL3Tr3_mem {σ : F ≃+* F} {t : F} (ht : t ∈ fixedField σ) :
    kaL3Tr3 t ∈ kaFix (kaSlMapN (n := 3) σ) := by
  rw [mem_kaFix_slMapN]
  intro a b
  have ht' := (mem_fixedField_iff σ t).mp ht
  fin_cases a <;> fin_cases b <;> simp [kaL3Tr3, ht']

omit [Finite F] in
theorem kaL3_comm_scalar {σ : F ≃+* F} (T : Matrix (Fin 3) (Fin 3) F)
    (hT : ∀ g ∈ kaFix (kaSlMapN (n := 3) σ),
      T * (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * T) :
    ∃ c : F, T = c • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have h : Pairwise fun i j : Fin 3 => Commute (Matrix.single i j (1 : F)) T := by
    intro i j hij
    have h1 := hT _ (kaTransv_mem (σ := σ) hij)
    simp only [Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul, mul_one,
      one_mul] at h1
    have h2 : T * Matrix.single i j (1 : F) = Matrix.single i j (1 : F) * T := add_left_cancel h1
    exact h2.symm
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single h
  exact ⟨c, by rw [← hc]; simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem kaL3_field_pure (σ : F ≃+* F) (hσ : orderOf σ = 2) : KAAll (fieldAut 3 F σ) := by
  have hLq := kaFix_slMapN_quasisimple (n := 3) le_rfl σ
  have hker : ∀ z ∈ (proj 3 F).ker, ∀ g : SL(3, F), g * z = z * g := by
    intro z hz g
    rw [ker_proj] at hz
    exact Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz) g
  refine ka_all_of_cover (ka_conj_injective_of_center_bot center_projectiveSL_three_eq_bot)
    (proj 3 F) (proj_surjective 3 F) hker (kaSlMapN (n := 3) σ)
    (fun g => fieldAut_proj σ g) (kaFix (kaSlMapN (n := 3) σ)) le_rfl
    (Subgroup.isPerfect_iff.mp hLq.1) (fun g hg => hg) hLq ?_
  intro p hp hp2 e hord _ hfix
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hord) ⟨e, Subgroup.mem_zpowers e⟩
  rw [Subgroup.orderOf_mk] at hm
  have hβ : e ^ (p ^ m) = 1 := by rw [← hm]; exact pow_orderOf_eq_one e
  refine kaL3_aut_fixing_trivial (Ω := kaFix (kaSlMapN (n := 3) σ))
    (fun A τ h => semiSL_fix_of_perfect A τ hLq.1 h) (fun T hT => kaL3_comm_scalar T hT) ?_
    ((hp.odd_of_ne_two hp2).pow) hβ (fun g hg => hfix _ ⟨g, hg, rfl⟩)
  intro τ hτodd htr
  refine kaL3_eq_one_of_fixed σ τ hσ hτodd fun t ht => ?_
  have h1 := htr (kaL3Tr3 t) (kaL3Tr3_mem ht)
  have h2 : Matrix.trace ((kaL3Tr3 t : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = t + 1 := by
    simp [Matrix.trace_fin_three, kaL3Tr3]
  rw [h2, map_add, map_one] at h1
  linear_combination h1

theorem kaL3_field {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hK : Nat.card F = p ^ f)
    (A : GL (Fin 3) F) (σ : F ≃+* F) (hσ : σ ≠ 1)
    (hα : (conjAut 3 F A * fieldAut 3 F σ) ^ 2 = 1) :
    KAAll (conjAut 3 F A * fieldAut 3 F σ) := by
  obtain ⟨-, -, H, hH⟩ := linear_field_involution_descent hp hf hK (le_refl 3) A σ hσ hα
  have hσ2 : orderOf σ = 2 := by
    have h1 := CFSG.RankThree.LinearDescent.conjAut_mul_fieldAut_pow σ A 2
    rw [h1] at hα
    have hσ2' : σ ^ 2 = 1 := (eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ hα).1
    exact orderOf_eq_prime hσ2' hσ
  have hK0 := kaL3_field_pure σ hσ2
  have h := KAAll.of_mulEquiv (conjAut 3 F H : projectiveSL 3 F ≃* projectiveSL 3 F) hK0
  rw [ka_congr_eq_mul_aut] at h
  rw [hH]
  exact h

end Field3

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
