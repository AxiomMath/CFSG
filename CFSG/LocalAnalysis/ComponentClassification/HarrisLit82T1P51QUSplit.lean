module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUEig
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherScalarCommutantSpace

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n r s : ℕ}

theorem mem_normOneScalars_of_smul (hn : 0 < n) {g : gramSU h (idGram K n)} {c : K}
    (hg : ∀ v, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = c • v) :
    g ∈ normOneScalars h (gramSU h (idGram K n)) n := by
  have hgm : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • (1 : Matrix (Fin n) (Fin n) K) :=
    Matrix.ext_iff_mulVec.mpr fun v => by rw [hg, Matrix.smul_mulVec, Matrix.one_mulVec]
  obtain ⟨hU, hdet⟩ := mem_gramSU.mp g.2
  rw [hgm, det_smul, det_one, mul_one, Fintype.card_fin] at hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hdet
    exact zero_ne_one hdet
  have hN : h.norm c = 1 := by
    rw [hgm] at hU
    have h1 := congrFun (congrFun hU ⟨0, hn⟩) ⟨0, hn⟩
    simp at h1
    rw [UnitaryFieldData.norm]
    exact h1
  refine ⟨Units.mk0 c hc0, hN, Units.ext hdet, Units.ext ?_⟩
  rw [hgm, GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal]
  rfl

theorem exists_split_unitary_coord (hp2 : p ≠ 2) (a : gramSU h (idGram K n)) {l : K}
    (hl0 : l ≠ 0) (hAA : unitaryOp (suOp h a) * unitaryOp (suOp h a) = (l ^ 2) • 1)
    (hlN : h.norm l = 1) :
    ∃ (hc : IsCompl (eigP l (unitaryOp (suOp h a))) (eigM l (unitaryOp (suOp h a))))
      (eP : eigP l (unitaryOp (suOp h a)) ≃ₗ[K]
        (Fin (finrank K (eigP l (unitaryOp (suOp h a)))) → K))
      (eM : eigM l (unitaryOp (suOp h a)) ≃ₗ[K]
        (Fin (finrank K (eigM l (unitaryOp (suOp h a)))) → K)),
      ∀ v w, gramForm h 1 v w =
        gramForm h 1 (eigCoord hc eP eM v).1 (eigCoord hc eP eM w).1 +
          gramForm h 1 (eigCoord hc eP eM v).2 (eigCoord hc eP eM w).2 := by
  have htwo := two_ne_zero_of_odd h hp2
  set A := unitaryOp (suOp h a)
  have hc : IsCompl (eigP l A) (eigM l A) :=
    isCompl_ker_sub_one_ker_add_one htwo (invSMulOp_mul_self hl0 hAA)
  set B := idForm h n
  have hT : ∀ v w, B (invSMulOp l A v) (invSMulOp l A w) = B v w := fun v w => by
    rw [sesq_invSMulOp l (suOp h a) v w, hlN, inv_one, one_mul]
  have horth : ∀ v ∈ eigP l A, ∀ w ∈ eigM l A, B v w = 0 :=
    fun v hv w hw => sesq_eq_zero_of_eigen_one htwo hT hv hw
  have horth' : ∀ v ∈ eigM l A, ∀ w ∈ eigP l A, B v w = 0 := fun v hv w hw => by
    rw [← (idForm_isSymm h n).eq, horth w hw v hv, map_zero]
  have hSP : (B.domRestrict₁₂ (eigP l A) (eigP l A)).IsSymm :=
    ⟨fun x y => (idForm_isSymm h n).eq (x : Fin n → K) (y : Fin n → K)⟩
  have hSM : (B.domRestrict₁₂ (eigM l A) (eigM l A)).IsSymm :=
    ⟨fun x y => (idForm_isSymm h n).eq (x : Fin n → K) (y : Fin n → K)⟩
  have hLP := separatingLeft_domRestrict_of_orth (idForm_separatingLeft h n) hc horth
  have hLM := separatingLeft_domRestrict_of_orth (idForm_separatingLeft h n) hc.symm horth'
  obtain ⟨bP, hbP⟩ := h.exists_orthonormal_basis hSP hLP
  obtain ⟨bM, hbM⟩ := h.exists_orthonormal_basis hSM hLM
  refine ⟨hc, bP.equivFun, bM.equivFun, fun v w => ?_⟩
  set β := eigCoord hc bP.equivFun bM.equivFun
  obtain ⟨x, rfl⟩ := β.symm.surjective v
  obtain ⟨y, rfl⟩ := β.symm.surjective w
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, eigCoord_symm,
    eigCoord_symm]
  change B _ _ = _
  simp only [map_add, LinearMap.add_apply]
  rw [horth _ (bP.equivFun.symm x.1).2 _ (bM.equivFun.symm y.2).2,
    horth' _ (bM.equivFun.symm x.2).2 _ (bP.equivFun.symm y.1).2, add_zero, zero_add]
  have h1 := hermForm_eq_gramForm_one h bP hbP (bP.equivFun.symm x.1) (bP.equivFun.symm y.1)
  have h2 := hermForm_eq_gramForm_one h bM hbM (bM.equivFun.symm x.2) (bM.equivFun.symm y.2)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1 h2
  exact congrArg₂ (· + ·) h1 h2

section blocks

variable (β : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K)))
  (hF : ∀ v w, gramForm h 1 v w = gramForm h 1 (β v).1 (β w).1 + gramForm h 1 (β v).2 (β w).2)

include hF in
theorem blockConj_mem_split {M₁ : GL (Fin r) K} {M₂ : GL (Fin s) K}
    (h₁ : ∀ u u', gramForm h 1 ((M₁ : Matrix (Fin r) (Fin r) K) *ᵥ u)
      ((M₁ : Matrix (Fin r) (Fin r) K) *ᵥ u') = gramForm h 1 u u')
    (h₂ : ∀ u u', gramForm h 1 ((M₂ : Matrix (Fin s) (Fin s) K) *ᵥ u)
      ((M₂ : Matrix (Fin s) (Fin s) K) *ᵥ u') = gramForm h 1 u u')
    (hdet : (M₁ : Matrix (Fin r) (Fin r) K).det * (M₂ : Matrix (Fin s) (Fin s) K).det = 1) :
    blockConj β (M₁, M₂) ∈ gramSU h (idGram K n) :=
  blockConj_mem_gramSU β h (fun u u' => gramForm h 1 u.1 u'.1 + gramForm h 1 u.2 u'.2) hF _
    (fun u u' => by simp only [h₁, h₂]) hdet

@[expose] def splitEmbR : gramSU h (1 : Matrix (Fin s) (Fin s) K) →* gramSU h (idGram K n) :=
  ((blockConj β).comp ((MonoidHom.inr _ _).comp (gramSU h 1).subtype)).codRestrict _ fun M =>
    blockConj_mem_split h β hF (fun _ _ => by simp) (mem_gramSU_iff_isometry.mp M.2).1
      (by simp [(mem_gramSU_iff_isometry.mp M.2).2])

@[expose] def splitEmbL : gramSU h (1 : Matrix (Fin r) (Fin r) K) →* gramSU h (idGram K n) :=
  ((blockConj β).comp ((MonoidHom.inl _ _).comp (gramSU h 1).subtype)).codRestrict _ fun M =>
    blockConj_mem_split h β hF (mem_gramSU_iff_isometry.mp M.2).1 (fun _ _ => by simp)
      (by simp [(mem_gramSU_iff_isometry.mp M.2).2])

theorem coe_splitEmbR (M : gramSU h (1 : Matrix (Fin s) (Fin s) K)) :
    (splitEmbR h β hF M : GL (Fin n) K) = blockConj β (1, M) := rfl

theorem coe_splitEmbL (M : gramSU h (1 : Matrix (Fin r) (Fin r) K)) :
    (splitEmbL h β hF M : GL (Fin n) K) = blockConj β (M, 1) := rfl

theorem splitEmbR_injective : Function.Injective (splitEmbR h β hF) := fun _ _ hMM' =>
  Subtype.ext (congrArg Prod.snd (blockConj_injective β (congrArg Subtype.val hMM')))

theorem splitEmbL_injective : Function.Injective (splitEmbL h β hF) := fun _ _ hMM' =>
  Subtype.ext (congrArg Prod.fst (blockConj_injective β (congrArg Subtype.val hMM')))

include hF in
theorem block_isometry_split {y : GL (Fin r) K × GL (Fin s) K}
    (hy : blockConj β y ∈ gramSU h (idGram K n)) :
    (∀ u u', gramForm h 1 ((y.1 : Matrix (Fin r) (Fin r) K) *ᵥ u)
      ((y.1 : Matrix (Fin r) (Fin r) K) *ᵥ u') = gramForm h 1 u u') ∧
    (∀ u u', gramForm h 1 ((y.2 : Matrix (Fin s) (Fin s) K) *ᵥ u)
      ((y.2 : Matrix (Fin s) (Fin s) K) *ᵥ u') = gramForm h 1 u u') := by
  have hiso : ∀ v w, gramForm h (1 : Matrix (Fin n) (Fin n) K)
      (((blockConj β y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (((blockConj β y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
      gramForm h 1 v w := (mem_gramSU_iff_isometry.mp hy).1
  constructor
  · intro u u'
    have h1 := hiso (β.symm (u, 0)) (β.symm (u', 0))
    rw [hF, hF (β.symm (u, 0)), apply_blockConj_mulVec, apply_blockConj_mulVec,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    simpa using h1
  · intro u u'
    have h1 := hiso (β.symm (0, u)) (β.symm (0, u'))
    rw [hF, hF (β.symm (0, u)), apply_blockConj_mulVec, apply_blockConj_mulVec,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    simpa using h1

end blocks

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
