module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTL4E

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

namespace BL4

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F]

abbrev StabF (d : ℕ) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ v ∈ flagSpace 4 F d, M *ᵥ v ∈ flagSpace 4 F d

abbrev ee0 : Fin 4 → F := Pi.single 0 1

abbrev ee3 : Fin 4 → F := Pi.single 3 1

theorem entry_zero_of_stabF {d : ℕ} {M : Matrix (Fin 4) (Fin 4) F} (h : StabF d M)
    {i j : Fin 4} (hj : (j : ℕ) < d) (hi : d ≤ (i : ℕ)) : M i j = 0 := by
  have hv : (Pi.single j 1 : Fin 4 → F) ∈ flagSpace 4 F d := mem_flagSpace.mpr fun k hk => by
    have hkj : k ≠ j := fun h => by subst h; omega
    simp [hkj]
  have := mem_flagSpace.mp (h _ hv) i hi
  simpa [mulVec_single_one] using this

theorem mulVec_e0_of_stabF1 {M : Matrix (Fin 4) (Fin 4) F} (h : StabF 1 M) :
    M *ᵥ ee0 = M 0 0 • ee0 := by
  ext i
  by_cases hi : i = 0
  · subst hi
    simp
  · have h1 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.mpr fun h0 => hi (Fin.ext h0)
    simp [hi, entry_zero_of_stabF h (j := 0) (by norm_num) h1]

theorem vecMul_e3_of_stabF3 {M : Matrix (Fin 4) (Fin 4) F} (h : StabF 3 M) :
    ee3 ᵥ* M = M 3 3 • ee3 := by
  ext j
  by_cases hj : j = 3
  · subst hj
    simp
  · have h3 : (j : ℕ) < 3 := by
      have := j.isLt
      have : (j : ℕ) ≠ 3 := fun h0 => hj (Fin.ext h0)
      omega
    simp [hj, entry_zero_of_stabF h (i := 3) h3 (by norm_num)]

theorem toBlocks₂₁_bv_of_stabF2 {M : Matrix (Fin 4) (Fin 4) F} (h : StabF 2 M) :
    (bv M).toBlocks₂₁ = 0 := by
  ext i j
  rw [toBlocks₂₁, of_apply, bv_apply]
  exact entry_zero_of_stabF h (by rw [val_e4_inl]; exact j.isLt)
    (by rw [val_e4_inr]; omega)

theorem e4_inl_zero : e4 (Sum.inl (0 : Fin 2)) = (0 : Fin 4) := rfl

theorem e4_inr_one : e4 (Sum.inr (1 : Fin 2)) = (3 : Fin 4) := rfl

theorem e4_inl_one : e4 (Sum.inl (1 : Fin 2)) = (1 : Fin 4) := rfl

theorem e4_inr_zero : e4 (Sum.inr (0 : Fin 2)) = (2 : Fin 4) := rfl

theorem mulVec_e0_of_bv {M : Matrix (Fin 4) (Fin 4) F} {ν : F} (h21 : (bv M).toBlocks₂₁ = 0)
    (h11 : (bv M).toBlocks₁₁ = ν • 1) : M *ᵥ ee0 = ν • ee0 := by
  ext i
  obtain ⟨a, rfl⟩ := e4.surjective i
  have hcol : M (e4 a) 0 = bv M a (Sum.inl 0) := by rw [bv_apply, e4_inl_zero]
  rcases a with a | a
  · have := congrFun (congrFun h11 a) 0
    simp only [toBlocks₁₁, of_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [mulVec_single_one, col_apply, hcol, this]
    fin_cases a
    · simp [e4_inl_zero, Matrix.one_apply]
    · simp [e4_inl_one]
  · have := congrFun (congrFun h21 a) 0
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply] at this
    rw [mulVec_single_one, col_apply, hcol, this]
    have hne : e4 (Sum.inr a) ≠ 0 := fun h0 => by
      have := congrArg Fin.val h0
      rw [val_e4_inr] at this
      simp at this
    simp [hne]

theorem vecMul_e3_of_bv {M : Matrix (Fin 4) (Fin 4) F} {ν : F} (h21 : (bv M).toBlocks₂₁ = 0)
    (h22 : (bv M).toBlocks₂₂ = ν • 1) : ee3 ᵥ* M = ν • ee3 := by
  ext j
  obtain ⟨a, rfl⟩ := e4.surjective j
  have hrow : M 3 (e4 a) = bv M (Sum.inr 1) a := by rw [bv_apply, e4_inr_one]
  rcases a with a | a
  · have := congrFun (congrFun h21 1) a
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply] at this
    rw [single_one_vecMul, row_apply, hrow, this]
    have hne : e4 (Sum.inl a) ≠ 3 := fun h0 => by
      have := congrArg Fin.val h0
      rw [val_e4_inl] at this
      have := a.isLt
      simp_all
    simp [hne]
  · have := congrFun (congrFun h22 1) a
    simp only [toBlocks₂₂, of_apply, Matrix.smul_apply, smul_eq_mul] at this
    rw [single_one_vecMul, row_apply, hrow, this]
    fin_cases a
    · simp [e4_inr_zero]
    · simp [e4_inr_one, Matrix.one_apply]

theorem stabF_conj {d : ℕ} {N : Submodule F (Fin 4 → F)} {g : SpecialLinearGroup (Fin 4) F}
    (hg : (flagSpace 4 F d).map (mulVecLin (g : Matrix (Fin 4) (Fin 4) F)) = N)
    {A : Matrix (Fin 4) (Fin 4) F} (hA : ∀ v ∈ N, A *ᵥ v ∈ N) :
    StabF d ((((SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A *
      (g : Matrix (Fin 4) (Fin 4) F)) := by
  intro v hv
  have h1 : (g : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ N := by
    rw [← hg]
    exact ⟨v, hv, rfl⟩
  have h2 := hA _ h1
  rw [← hg] at h2
  obtain ⟨w, hw, hwe⟩ := h2
  have hgg : (((SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((SpecialLinearGroup.toGL g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hwe' : (g : Matrix (Fin 4) (Fin 4) F) *ᵥ w = A *ᵥ ((g : Matrix (Fin 4) (Fin 4) F) *ᵥ v) :=
    hwe
  have e : ((((SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * A *
      (g : Matrix (Fin 4) (Fin 4) F)) *ᵥ v = w := by
    have hgg' : (((SpecialLinearGroup.toGL g)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        (g : Matrix (Fin 4) (Fin 4) F) = 1 := hgg
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hwe', mulVec_mulVec, hgg', one_mulVec]
  rw [e]
  exact hw

end BL4

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT
