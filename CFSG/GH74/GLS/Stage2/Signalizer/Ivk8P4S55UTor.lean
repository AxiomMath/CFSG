module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Burgoyne.U CFSG.ComponentClassification.Burgoyne.Proj
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartOne.KFU (diagU diagU_val diagU_mul diagU_one det_diagU)

variable {p f : ℕ} {K : Type} [Field K] {n : ℕ}

@[expose] def normOneU (q : ℕ) (K : Type) [Field K] : Subgroup Kˣ :=
  (powMonoidHom (q + 1) : Kˣ →* Kˣ).ker

theorem norm_eq_pow (h : UnitaryFieldData p f K) (c : K) : h.norm c = c ^ (p ^ f + 1) := by
  rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, pow_succ']

theorem mem_normOneU_iff (h : UnitaryFieldData p f K) (c : Kˣ) :
    c ∈ normOneU (p ^ f) K ↔ h.norm (c : K) = 1 := by
  rw [normOneU, MonoidHom.mem_ker, powMonoidHom_apply, norm_eq_pow h,
    ← Units.val_pow_eq_pow_val, Units.val_eq_one]

@[expose] def uDiagVec (i₀ i₁ : Fin n) (c : Kˣ) : Fin n → Kˣ :=
  Pi.mulSingle i₀ c * Pi.mulSingle i₁ c⁻¹

theorem uDiagVec_one (i₀ i₁ : Fin n) : uDiagVec i₀ i₁ (1 : Kˣ) = 1 := by
  funext i
  simp [uDiagVec]

theorem uDiagVec_i₀ {i₀ i₁ : Fin n} (hij : i₀ ≠ i₁) (c : Kˣ) : uDiagVec i₀ i₁ c i₀ = c := by
  simp [uDiagVec, hij]

theorem uDiagVec_i₁ {i₀ i₁ : Fin n} (hij : i₀ ≠ i₁) (c : Kˣ) : uDiagVec i₀ i₁ c i₁ = c⁻¹ := by
  simp [uDiagVec, hij.symm]

theorem uDiagVec_other {i₀ i₁ i : Fin n} (h0 : i ≠ i₀) (h1 : i ≠ i₁) (c : Kˣ) :
    uDiagVec i₀ i₁ c i = 1 := by
  simp [uDiagVec, h0, h1]

theorem uDiagVec_mul {i₀ i₁ : Fin n} (hij : i₀ ≠ i₁) (c d : Kˣ) :
    uDiagVec i₀ i₁ (c * d) = uDiagVec i₀ i₁ c * uDiagVec i₀ i₁ d := by
  funext i
  by_cases h0 : i = i₀
  · subst h0
    rw [Pi.mul_apply, uDiagVec_i₀ hij, uDiagVec_i₀ hij, uDiagVec_i₀ hij]
  by_cases h1 : i = i₁
  · subst h1
    rw [Pi.mul_apply, uDiagVec_i₁ hij, uDiagVec_i₁ hij, uDiagVec_i₁ hij, mul_inv]
  · rw [Pi.mul_apply, uDiagVec_other h0 h1, uDiagVec_other h0 h1, uDiagVec_other h0 h1, one_mul]

theorem norm_uDiagVec (h : UnitaryFieldData p f K) {i₀ i₁ : Fin n} (hij : i₀ ≠ i₁) {c : Kˣ}
    (hc : h.norm (c : K) = 1) (i : Fin n) : h.norm ((uDiagVec i₀ i₁ c i : Kˣ) : K) = 1 := by
  by_cases h0 : i = i₀
  · subst h0
    rw [uDiagVec_i₀ hij]
    exact hc
  by_cases h1 : i = i₁
  · subst h1
    rw [uDiagVec_i₁ hij, Units.val_inv_eq_inv_val, UnitaryFieldData.norm, map_inv₀,
      ← mul_inv, ← UnitaryFieldData.norm, hc, inv_one]
  · rw [uDiagVec_other h0 h1, Units.val_one, UnitaryFieldData.norm, map_one, mul_one]

theorem diagU_mem_gramSU (h : UnitaryFieldData p f K) {i₀ i₁ : Fin n} (hij : i₀ ≠ i₁) {c : Kˣ}
    (hc : h.norm (c : K) = 1) :
    (diagU (uDiagVec i₀ i₁ c) : GL (Fin n) K) ∈
      gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rw [mem_gramSU, Units.val_one, Matrix.mul_one]
  refine ⟨?_, ?_⟩
  · rw [diagU_val, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    have := norm_uDiagVec h hij hc i
    rwa [UnitaryFieldData.norm, mul_comm] at this
  · rw [det_diagU, Finset.prod_eq_mul i₀ i₁ hij]
    · rw [uDiagVec_i₀ hij, uDiagVec_i₁ hij, Units.val_inv_eq_inv_val, mul_inv_cancel₀ c.ne_zero]
    · intro i _ ⟨hi0, hi1⟩
      rw [uDiagVec_other hi0 hi1, Units.val_one]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

section Hom

variable (h : UnitaryFieldData p f K) {i₀ i₁ : Fin n}

@[expose] noncomputable def suDiagT (hij : i₀ ≠ i₁) :
    ↥(normOneU (p ^ f) K) →* StatedSU n (p ^ f) K where
  toFun c := ⟨diagU (uDiagVec i₀ i₁ (c : Kˣ)), by
    rw [statedSU_eq_gramSU h]
    exact diagU_mem_gramSU h hij ((mem_normOneU_iff h c).mp c.2)⟩
  map_one' := by
    apply Subtype.ext
    show diagU (uDiagVec i₀ i₁ (1 : Kˣ)) = 1
    rw [uDiagVec_one, diagU_one]
  map_mul' c d := by
    apply Subtype.ext
    show diagU (uDiagVec i₀ i₁ ((c : Kˣ) * (d : Kˣ))) =
      diagU (uDiagVec i₀ i₁ (c : Kˣ)) * diagU (uDiagVec i₀ i₁ (d : Kˣ))
    rw [uDiagVec_mul hij, diagU_mul]

@[expose] noncomputable def uTor (hij : i₀ ≠ i₁) :
    ↥(normOneU (p ^ f) K) →* StatedProj (StatedSU n (p ^ f) K) :=
  (projH (StatedSU n (p ^ f) K)).comp (suDiagT h hij)

theorem uTor_injective (hij : i₀ ≠ i₁) {i₂ : Fin n} (h02 : i₂ ≠ i₀) (h12 : i₂ ≠ i₁) :
    Function.Injective (uTor h hij) := by
  intro a b hab
  have h1 := projH_eq_projH_iff.mp hab
  rw [← map_inv, ← map_mul, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  set κ : ↥(normOneU (p ^ f) K) := a⁻¹ * b with hκ
  have hdiag : ((suDiagT h hij κ : StatedSU n (p ^ f) K) : GL (Fin n) K) =
      diagU (uDiagVec i₀ i₁ (κ : Kˣ)) := rfl
  rw [hdiag] at hc
  have e2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i₂ i₂) hc
  have e0 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i₀ i₀) hc
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagU_val,
    Matrix.diagonal_apply_eq, uDiagVec_other h02 h12, uDiagVec_i₀ hij, Units.val_one] at e2 e0
  have hκ1 : (κ : Kˣ) = 1 := Units.ext (e0.symm.trans e2)
  exact inv_mul_eq_one.mp (Subtype.ext hκ1)

theorem map_mem_normOneU (φ : K ≃+* K) {c : Kˣ} (hc : c ∈ normOneU (p ^ f) K) :
    Units.map (φ : K →* K) c ∈ normOneU (p ^ f) K := by
  rw [normOneU, MonoidHom.mem_ker, powMonoidHom_apply, ← map_pow]
  rw [normOneU, MonoidHom.mem_ker, powMonoidHom_apply] at hc
  rw [hc, map_one]

theorem glAut_diagU_uDiagVec (hij : i₀ ≠ i₁) (φ : K ≃+* K) (c : Kˣ) :
    glAut φ (diagU (uDiagVec i₀ i₁ c) : GL (Fin n) K) =
      diagU (uDiagVec i₀ i₁ (Units.map (φ : K →* K) c)) := by
  apply Units.ext
  rw [coe_glAut, diagU_val, diagU_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  by_cases h0 : i = i₀
  · subst h0
    rw [uDiagVec_i₀ hij, uDiagVec_i₀ hij]
    rfl
  by_cases h1 : i = i₁
  · subst h1
    rw [uDiagVec_i₁ hij, uDiagVec_i₁ hij, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      map_inv₀]
    rfl
  · rw [uDiagVec_other h0 h1, uDiagVec_other h0 h1]
    simp

theorem uFieldAut_uTor (hn : 1 ≤ n) (hij : i₀ ≠ i₁) (φ : K ≃+* K)
    (c : ↥(normOneU (p ^ f) K)) :
    uFieldAut h hn φ (uTor h hij c) =
      uTor h hij ⟨Units.map (φ : K →* K) (c : Kˣ), map_mem_normOneU φ c.2⟩ := by
  show uFieldAut h hn φ (projH _ (suDiagT h hij c)) = projH _ (suDiagT h hij _)
  rw [uFieldAut_proj]
  congr 1
  apply Subtype.ext
  exact glAut_diagU_uDiagVec hij φ (c : Kˣ)

end Hom

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
