module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTSp4P
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4Adm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BU4

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher BL4
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K]

abbrev eU : Fin 2 ⊕ Fin 2 ≃ HypIndex 2 0 :=
  Equiv.sumCongr (Equiv.refl (Fin 2)) (Equiv.emptySum (Fin 0) (Fin 2)).symm

@[expose] noncomputable def rv :
    Matrix (HypIndex 2 0) (HypIndex 2 0) K ≃ₐ[K] Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.reindexAlgEquiv K K eU.symm

theorem rv_apply (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (i j : Fin 2 ⊕ Fin 2) :
    rv M i j = M (eU i) (eU j) := rfl

theorem rv_map (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (φ : K →+* K) :
    rv (M.map φ) = (rv M).map φ := rfl

theorem rv_transpose (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : rv Mᵀ = (rv M)ᵀ := rfl

theorem det_rv (M : Matrix (HypIndex 2 0) (HypIndex 2 0) K) : (rv M).det = M.det := by
  simp only [rv, Matrix.coe_reindexAlgEquiv, det_reindex_self]

abbrev jU : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 1 0

theorem rv_hypGram : rv (hypGram 2 0 K) = (jU : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [rv_apply, hypGram_apply, one_apply, eq_comm]

@[expose] noncomputable def rvGL : GL (HypIndex 2 0) K →* GL (Fin 2 ⊕ Fin 2) K :=
  Units.map (rv : Matrix (HypIndex 2 0) (HypIndex 2 0) K ≃ₐ[K] _).toMonoidHom

theorem coe_rvGL (x : GL (HypIndex 2 0) K) :
    ((rvGL x : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      rv (x : Matrix (HypIndex 2 0) (HypIndex 2 0) K) := rfl

theorem rvGL_injective : Function.Injective (rvGL : GL (HypIndex 2 0) K →* _) :=
  fun _ _ e => Units.ext (rv.injective (congrArg Units.val e))

theorem toBlocks₂₁_rv_of_stab2 (h : UnitaryFieldData p f K)
    {M : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hM : ∀ v ∈ hypFlag h 2 0 2, M *ᵥ v ∈ hypFlag h 2 0 2) : (rv M).toBlocks₂₁ = 0 := by
  have hF := hypFlag_eq_posFlag (r := 2) (ε := 0) h (by norm_num) (i := 2) (by norm_num)
  ext i j
  have hv : (Pi.single (Sum.inl j) 1 : HypIndex 2 0 → K) ∈ hypFlag h 2 0 2 := by
    rw [hF, mem_posFlag]
    intro a ha
    have : a ≠ Sum.inl j := by
      rintro rfl
      simp only [fullPos_inl] at ha
      omega
    simp [this]
  have hm := hM _ hv
  rw [hF, mem_posFlag] at hm
  have := hm (Sum.inr (Sum.inr i)) (by simp only [fullPos_inr_inr]; omega)
  simpa [mulVec_single_one, toBlocks₂₁, rv_apply] using this

theorem mulVec_e0_rv_of_stab1 (h : UnitaryFieldData p f K)
    {M : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hM : ∀ v ∈ hypFlag h 2 0 1, M *ᵥ v ∈ hypFlag h 2 0 1) :
    rv M *ᵥ BS4.e0 = (rv M) (Sum.inl 0) (Sum.inl 0) • BS4.e0 := by
  have hF := hypFlag_eq_posFlag (r := 2) (ε := 0) h (by norm_num) (i := 1) (by norm_num)
  have hv : (Pi.single (Sum.inl 0) 1 : HypIndex 2 0 → K) ∈ hypFlag h 2 0 1 := by
    rw [hF, mem_posFlag]
    intro a ha
    have : a ≠ Sum.inl 0 := by
      rintro rfl
      simp at ha
    simp [this]
  have hm := hM _ hv
  rw [hF, mem_posFlag] at hm
  ext i
  rcases i with i | i
  · fin_cases i
    · simp [rv_apply]
    · have := hm (Sum.inl 1) (by simp)
      simpa [mulVec_single_one, rv_apply] using this
  · have := hm (Sum.inr (Sum.inr i)) (by simp only [fullPos_inr_inr]; omega)
    simpa [mulVec_single_one, rv_apply] using this

theorem stab_conj (h : UnitaryFieldData p f K) {d : ℕ} {N : Submodule K (HypIndex 2 0 → K)}
    {g : hypSU h 2 0} (hg : g • hypFlag h 2 0 d = N) {A : Matrix (HypIndex 2 0) (HypIndex 2 0) K}
    (hA : ∀ v ∈ N, A *ᵥ v ∈ N) :
    ∀ v ∈ hypFlag h 2 0 d, ((((g : GL (HypIndex 2 0) K))⁻¹ : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ (A *ᵥ (((g : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v)) ∈ hypFlag h 2 0 d := by
  intro v hv
  replace hg := (hypSU_smul_eq_map g (hypFlag h 2 0 d)).symm.trans hg
  have h1 : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v ∈ N := by
    rw [← hg]
    exact ⟨v, hv, rfl⟩
  have h2 := hA _ h1
  rw [← hg] at h2
  obtain ⟨w, hw, hwe⟩ := h2
  have hgg : ((((g : GL (HypIndex 2 0) K))⁻¹ : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) * ((g : GL (HypIndex 2 0) K) :
        Matrix (HypIndex 2 0) (HypIndex 2 0) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hwe' : ((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ w =
      A *ᵥ (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) *ᵥ v) := hwe
  rw [← hwe', mulVec_mulVec, hgg, one_mulVec]
  exact hw

end BU4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
