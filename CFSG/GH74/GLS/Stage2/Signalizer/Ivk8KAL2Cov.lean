module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KACover
public import CFSG.LieType.HighestRoot.CentTrialityThree

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section FixSL

variable {F : Type} [Field F]

@[expose] noncomputable def kaSlMap (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.map σ.toRingHom

theorem mem_kaFix_slMap {σ : F ≃+* F} {M : Matrix.SpecialLinearGroup (Fin 2) F} :
    M ∈ kaFix (kaSlMap σ) ↔
      ∀ i j, σ ((M : Matrix (Fin 2) (Fin 2) F) i j) = (M : Matrix (Fin 2) (Fin 2) F) i j := by
  rw [mem_kaFix]
  constructor
  · intro h i j
    have := congrArg
      (fun A : Matrix.SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) i j) h
    simpa [kaSlMap, Matrix.SpecialLinearGroup.map_apply_coe] using this
  · intro h
    apply Subtype.ext
    ext i j
    simpa [kaSlMap, Matrix.SpecialLinearGroup.map_apply_coe] using h i j

@[expose] noncomputable def kaSlIncl (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) →* Matrix.SpecialLinearGroup (Fin 2) F :=
  Matrix.SpecialLinearGroup.map (fixedField σ).subtype

theorem kaSlIncl_injective (σ : F ≃+* F) : Function.Injective (kaSlIncl σ) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg
    (fun C : Matrix.SpecialLinearGroup (Fin 2) F => (C : Matrix (Fin 2) (Fin 2) F) i j) h
  simpa [kaSlIncl, Matrix.SpecialLinearGroup.map_apply_coe] using this

theorem kaFix_slMap_eq_range (σ : F ≃+* F) : kaFix (kaSlMap σ) = (kaSlIncl σ).range := by
  ext M
  constructor
  · intro hM
    rw [mem_kaFix_slMap] at hM
    have hmem : ∀ i j, (M : Matrix (Fin 2) (Fin 2) F) i j ∈ fixedField σ :=
      fun i j => (mem_fixedField_iff σ _).mpr (hM i j)
    let A : Matrix (Fin 2) (Fin 2) (fixedField σ) :=
      Matrix.of fun i j => ⟨(M : Matrix (Fin 2) (Fin 2) F) i j, hmem i j⟩
    have hAM : (fixedField σ).subtype.mapMatrix A = (M : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rfl
    have hdet : A.det = 1 := by
      apply (fixedField σ).subtype.injective
      rw [RingHom.map_det, hAM, M.2, map_one]
    refine ⟨⟨A, hdet⟩, Subtype.ext ?_⟩
    simp only [kaSlIncl]
    exact hAM
  · rintro ⟨A, rfl⟩
    rw [mem_kaFix_slMap]
    intro i j
    simp only [kaSlIncl, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    exact fixedField_apply σ (A i j)

@[expose] noncomputable def kaFixSlEquiv (σ : F ≃+* F) :
    ↥(kaFix (kaSlMap σ)) ≃* Matrix.SpecialLinearGroup (Fin 2) (fixedField σ) :=
  (MulEquiv.subgroupCongr (kaFix_slMap_eq_range σ)).trans
    (MonoidHom.ofInjective (kaSlIncl_injective σ)).symm

theorem kaFix_slMap_quasisimple [Finite F] (σ : F ≃+* F)
    (h4 : 4 ≤ Nat.card (fixedField σ)) : CFSG.IsQuasisimple ↥(kaFix (kaSlMap σ)) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (kaFixSlEquiv σ).symm
    (CFSG.LieType.HighestRoot.isQuasisimple_SL2_of_four_le h4)

end FixSL

section CoverK

variable {F : Type} [Field F] {K : Type} [Group K]

@[expose] noncomputable def kaL2Cover (e : K ≃* L2 F) : Matrix.SpecialLinearGroup (Fin 2) F →* K :=
  (toPSL e).symm.toMonoidHom.comp
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))

theorem toPSL_kaL2Cover (e : K ≃* L2 F) (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    toPSL e (kaL2Cover e g) = (QuotientGroup.mk g : PSL2 F) := by
  simp [kaL2Cover]

theorem kaL2Cover_surjective (e : K ≃* L2 F) : Function.Surjective (kaL2Cover e) := by
  intro k
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (toPSL e k)
  refine ⟨g, (toPSL e).injective ?_⟩
  rw [toPSL_kaL2Cover, hg]

theorem kaL2Cover_central (e : K ≃* L2 F) :
    ∀ z ∈ (kaL2Cover e).ker, ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g * z = z * g := by
  intro z hz g
  have h1 : toPSL e (kaL2Cover e z) = 1 := by
    rw [MonoidHom.mem_ker] at hz
    rw [hz, map_one]
  rw [toPSL_kaL2Cover] at h1
  have hzc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff z).mp h1
  exact Subgroup.mem_center_iff.mp hzc g

theorem kaL2Cover_field (e : K ≃* L2 F) (σ : F ≃+* F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    fieldAutHom e σ (kaL2Cover e g) = kaL2Cover e (kaSlMap σ g) := by
  apply (toPSL e).injective
  rw [toPSL_fieldAutHom, toPSL_kaL2Cover, toPSL_kaL2Cover, psl2FieldAut_apply]
  exact psl2RingEquiv_mk σ g

end CoverK

section Gens

variable {F : Type} [Field F]

@[expose] noncomputable def kaSlTr (t : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; -1, t], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def kaSlU : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] noncomputable def kaSlL : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem kaSlTr_mem {σ : F ≃+* F} {t : F} (ht : t ∈ fixedField σ) :
    kaSlTr t ∈ kaFix (kaSlMap σ) := by
  rw [mem_kaFix_slMap]
  intro i j
  have ht' := (mem_fixedField_iff σ t).mp ht
  fin_cases i <;> fin_cases j <;> simp [kaSlTr, ht']

theorem kaSlU_mem (σ : F ≃+* F) :
    (kaSlU : Matrix.SpecialLinearGroup (Fin 2) F) ∈ kaFix (kaSlMap σ) := by
  rw [mem_kaFix_slMap]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [kaSlU]

theorem kaSlL_mem (σ : F ≃+* F) :
    (kaSlL : Matrix.SpecialLinearGroup (Fin 2) F) ∈ kaFix (kaSlMap σ) := by
  rw [mem_kaFix_slMap]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [kaSlL]

theorem kaL2_scalar_of_rel (G : Matrix (Fin 2) (Fin 2) F) (hG : G.det ≠ 0) (c c' : F)
    (hu : G * !![1, 1; 0, 1] = c • (!![1, 1; 0, 1] * G))
    (hl : G * !![1, 0; 1, 1] = c' • (!![1, 0; 1, 1] * G)) : ∃ s : F, s ≠ 0 ∧ G = s • 1 := by
  have hd : G 0 0 * G 1 1 - G 0 1 * G 1 0 ≠ 0 := by rwa [Matrix.det_fin_two] at hG
  have u00 := congrFun (congrFun hu 0) 0
  have u01 := congrFun (congrFun hu 0) 1
  have u10 := congrFun (congrFun hu 1) 0
  have l00 := congrFun (congrFun hl 0) 0
  have l10 := congrFun (congrFun hl 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] at u00 u01 u10 l00 l10
  have hc : c = 1 := by
    by_cases hγ : G 1 0 = 0
    · have ha : G 0 0 ≠ 0 := by
        intro h0
        apply hd
        rw [h0, hγ]
        ring
      have h1 : G 0 0 * (1 - c) = 0 := by rw [hγ] at u00; linear_combination u00
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h ha
      · linear_combination -h
    · have h1 : G 1 0 * (1 - c) = 0 := by linear_combination u10
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hγ
      · linear_combination -h
  subst hc
  have hγ0 : G 1 0 = 0 := by linear_combination -u00
  have hδa : G 1 1 = G 0 0 := by linear_combination -u01 + u00 * 0
  have ha : G 0 0 ≠ 0 := by
    intro h0
    apply hd
    rw [h0, hγ0, hδa, h0]
    ring
  have hc' : c' = 1 := by
    have h1 : G 0 0 * (1 - c') = 0 := by
      rw [hγ0, hδa] at l10
      linear_combination l10
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h ha
    · linear_combination -h
  subst hc'
  have hb0 : G 0 1 = 0 := by linear_combination l00
  refine ⟨G 0 0, ha, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb0, hγ0, hδa]

end Gens

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
