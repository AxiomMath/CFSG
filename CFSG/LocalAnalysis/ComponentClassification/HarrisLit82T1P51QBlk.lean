module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveCoordinatesMatrix
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG.ComponentClassification.CatalogueBProjectiveCoordinates
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {n r s : ℕ}

@[expose] def blockConj (β : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K))) :
    GL (Fin r) K × GL (Fin s) K →* GL (Fin n) K where
  toFun x := matrixActionEquiv.symm
    (β.trans (((matrixActionEquiv x.1).prodCongr (matrixActionEquiv x.2)).trans β.symm))
  map_one' := by
    apply matrixActionEquiv.injective
    rw [matrixActionEquiv_apply_symm_apply, map_one]
    ext v
    simp
  map_mul' x y := by
    apply matrixActionEquiv.injective
    rw [map_mul, matrixActionEquiv_apply_symm_apply, matrixActionEquiv_apply_symm_apply,
      matrixActionEquiv_apply_symm_apply]
    ext v
    simp [map_mul]

variable (β : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K)))

theorem blockConj_mulVec (x : GL (Fin r) K × GL (Fin s) K) (v : Fin n → K) :
    ((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v =
      β.symm ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ (β v).1,
        (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ (β v).2) := by
  change (matrixActionEquiv.symm _ : GL (Fin n) K).val.mulVec v = _
  rw [matrixActionEquiv_symm_mulVec]
  rfl

theorem apply_blockConj_mulVec (x : GL (Fin r) K × GL (Fin s) K) (v : Fin n → K) :
    β (((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ (β v).1,
        (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ (β v).2) := by
  rw [blockConj_mulVec, LinearEquiv.apply_symm_apply]

theorem det_blockConj (x : GL (Fin r) K × GL (Fin s) K) :
    ((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det =
      (x.1 : Matrix (Fin r) (Fin r) K).det * (x.2 : Matrix (Fin s) (Fin s) K).det := by
  have h1 : Matrix.toLin' ((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      β.symm.toLinearMap ∘ₗ ((Matrix.toLin' (x.1 : Matrix (Fin r) (Fin r) K)).prodMap
        (Matrix.toLin' (x.2 : Matrix (Fin s) (Fin s) K))) ∘ₗ β.toLinearMap := by
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, blockConj_mulVec]
    rfl
  rw [← LinearMap.det_toLin', h1]
  have h2 := LinearMap.det_conj ((Matrix.toLin' (x.1 : Matrix (Fin r) (Fin r) K)).prodMap
    (Matrix.toLin' (x.2 : Matrix (Fin s) (Fin s) K))) β.symm
  rw [LinearEquiv.symm_symm] at h2
  rw [h2, LinearMap.det_prodMap, LinearMap.det_toLin', LinearMap.det_toLin']

theorem blockConj_injective : Function.Injective (blockConj β) := by
  intro x y hxy
  have h1 : ∀ w : (Fin r → K) × (Fin s → K),
      ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ w.1, (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ w.2) =
      ((y.1 : Matrix (Fin r) (Fin r) K) *ᵥ w.1, (y.2 : Matrix (Fin s) (Fin s) K) *ᵥ w.2) := by
    intro w
    have := apply_blockConj_mulVec β x (β.symm w)
    rw [hxy, apply_blockConj_mulVec, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine Prod.ext (Units.ext (Matrix.ext_iff_mulVec.mpr fun u => ?_))
    (Units.ext (Matrix.ext_iff_mulVec.mpr fun u => ?_))
  · exact congrArg Prod.fst (h1 (u, 0))
  · exact congrArg Prod.snd (h1 (0, u))

@[expose] def blockScalar (c₁ c₂ : Kˣ) : GL (Fin n) K :=
  blockConj β (GeneralLinearGroup.scalar (Fin r) c₁, GeneralLinearGroup.scalar (Fin s) c₂)

theorem apply_blockScalar_mulVec (c₁ c₂ : Kˣ) (v : Fin n → K) :
    β (((blockScalar β c₁ c₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) =
      ((c₁ : K) • (β v).1, (c₂ : K) • (β v).2) := by
  rw [blockScalar, apply_blockConj_mulVec]
  simp [GeneralLinearGroup.coe_scalar, scalar_apply, ← smul_one_eq_diagonal, smul_mulVec]

theorem blockPreserving_of_commute {c₁ c₂ : Kˣ} (hc : (c₁ : K) ≠ c₂) {g : GL (Fin n) K}
    (hg : g * blockScalar β c₁ c₂ = blockScalar β c₁ c₂ * g) :
    (∀ u, (β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm (u, 0))).2 = 0) ∧
      ∀ y, (β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm (0, y))).1 = 0 := by
  have hD : ∀ v, ((blockScalar β c₁ c₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      ((g : Matrix (Fin n) (Fin n) K) *ᵥ v) = (g : Matrix (Fin n) (Fin n) K) *ᵥ
        (((blockScalar β c₁ c₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v) := by
    intro v
    rw [mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hg]
  have hsub : (c₁ : K) - c₂ ≠ 0 := sub_ne_zero.mpr hc
  constructor
  · intro u
    have h1 := congrArg β (hD (β.symm (u, 0)))
    have h2 : ((blockScalar β c₁ c₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        β.symm (u, 0) = (c₁ : K) • β.symm (u, 0) := by
      apply β.injective
      rw [apply_blockScalar_mulVec, map_smul, LinearEquiv.apply_symm_apply]
      simp
    rw [h2, mulVec_smul, apply_blockScalar_mulVec, map_smul] at h1
    have h3 := congrArg Prod.snd h1
    simp only [Prod.smul_snd] at h3
    have h4 : ((c₁ : K) - c₂) • (β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm (u, 0))).2 = 0 := by
      rw [sub_smul, h3, sub_self]
    exact (smul_eq_zero.mp h4).resolve_left hsub
  · intro y
    have h1 := congrArg β (hD (β.symm (0, y)))
    have h2 : ((blockScalar β c₁ c₂ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        β.symm (0, y) = (c₂ : K) • β.symm (0, y) := by
      apply β.injective
      rw [apply_blockScalar_mulVec, map_smul, LinearEquiv.apply_symm_apply]
      simp
    rw [h2, mulVec_smul, apply_blockScalar_mulVec, map_smul] at h1
    have h3 := congrArg Prod.fst h1
    simp only [Prod.smul_fst] at h3
    have h4 : ((c₂ : K) - c₁) • (β ((g : Matrix (Fin n) (Fin n) K) *ᵥ β.symm (0, y))).1 = 0 := by
      rw [sub_smul, h3, sub_self]
    exact (smul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr (Ne.symm hc))

theorem block_mulVec {g : Matrix (Fin n) (Fin n) K}
    (h₁ : ∀ u, (β (g *ᵥ β.symm (u, 0))).2 = 0) (h₂ : ∀ y, (β (g *ᵥ β.symm (0, y))).1 = 0)
    (v : Fin n → K) :
    β (g *ᵥ v) = (LinearMap.toMatrix' ((LinearMap.fst K _ _) ∘ₗ β.toLinearMap ∘ₗ
        (Matrix.toLin' g) ∘ₗ β.symm.toLinearMap ∘ₗ (LinearMap.inl K _ _)) *ᵥ (β v).1,
      LinearMap.toMatrix' ((LinearMap.snd K _ _) ∘ₗ β.toLinearMap ∘ₗ
        (Matrix.toLin' g) ∘ₗ β.symm.toLinearMap ∘ₗ (LinearMap.inr K _ _)) *ᵥ (β v).2) := by
  have hv : v = β.symm ((β v).1, 0) + β.symm (0, (β v).2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, LinearEquiv.symm_apply_apply]
  conv_lhs => rw [hv]
  rw [mulVec_add, map_add, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, h₂, add_zero]
    rfl
  · simp only [Prod.snd_add, h₁, zero_add]
    rfl

theorem exists_blockConj_eq_of_commute {c₁ c₂ : Kˣ} (hc : (c₁ : K) ≠ c₂) {g : GL (Fin n) K}
    (hg : g * blockScalar β c₁ c₂ = blockScalar β c₁ c₂ * g) :
    ∃ x : GL (Fin r) K × GL (Fin s) K, blockConj β x = g := by
  have hg' : g⁻¹ * blockScalar β c₁ c₂ = blockScalar β c₁ c₂ * g⁻¹ :=
    (Commute.inv_left (hg : Commute g (blockScalar β c₁ c₂))).eq
  obtain ⟨h₁, h₂⟩ := blockPreserving_of_commute β hc hg
  obtain ⟨h₁', h₂'⟩ := blockPreserving_of_commute β hc hg'
  set G := (g : Matrix (Fin n) (Fin n) K)
  set G' := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hGG : G * G' = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG'G : G' * G = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set x₁ := LinearMap.toMatrix' ((LinearMap.fst K _ _) ∘ₗ β.toLinearMap ∘ₗ
    (Matrix.toLin' G) ∘ₗ β.symm.toLinearMap ∘ₗ (LinearMap.inl K _ _))
  set x₂ := LinearMap.toMatrix' ((LinearMap.snd K _ _) ∘ₗ β.toLinearMap ∘ₗ
    (Matrix.toLin' G) ∘ₗ β.symm.toLinearMap ∘ₗ (LinearMap.inr K _ _))
  set y₁ := LinearMap.toMatrix' ((LinearMap.fst K _ _) ∘ₗ β.toLinearMap ∘ₗ
    (Matrix.toLin' G') ∘ₗ β.symm.toLinearMap ∘ₗ (LinearMap.inl K _ _))
  set y₂ := LinearMap.toMatrix' ((LinearMap.snd K _ _) ∘ₗ β.toLinearMap ∘ₗ
    (Matrix.toLin' G') ∘ₗ β.symm.toLinearMap ∘ₗ (LinearMap.inr K _ _))
  have hG := block_mulVec β h₁ h₂
  have hG' := block_mulVec β h₁' h₂'
  have hcomp : ∀ w : (Fin r → K) × (Fin s → K),
      (x₁ *ᵥ (y₁ *ᵥ w.1), x₂ *ᵥ (y₂ *ᵥ w.2)) = w ∧ (y₁ *ᵥ (x₁ *ᵥ w.1), y₂ *ᵥ (x₂ *ᵥ w.2)) = w
      := by
    intro w
    constructor
    · have := hG (G' *ᵥ β.symm w)
      rw [mulVec_mulVec, hGG, one_mulVec, LinearEquiv.apply_symm_apply, hG',
        LinearEquiv.apply_symm_apply] at this
      exact this.symm
    · have := hG' (G *ᵥ β.symm w)
      rw [mulVec_mulVec, hG'G, one_mulVec, LinearEquiv.apply_symm_apply, hG,
        LinearEquiv.apply_symm_apply] at this
      exact this.symm
  have hx₁ : x₁ * y₁ = 1 := Matrix.ext_iff_mulVec.mpr fun u => by
    rw [← mulVec_mulVec, one_mulVec]
    exact congrArg Prod.fst ((hcomp (u, 0)).1)
  have hy₁ : y₁ * x₁ = 1 := Matrix.ext_iff_mulVec.mpr fun u => by
    rw [← mulVec_mulVec, one_mulVec]
    exact congrArg Prod.fst ((hcomp (u, 0)).2)
  have hx₂ : x₂ * y₂ = 1 := Matrix.ext_iff_mulVec.mpr fun u => by
    rw [← mulVec_mulVec, one_mulVec]
    exact congrArg Prod.snd ((hcomp (0, u)).1)
  have hy₂ : y₂ * x₂ = 1 := Matrix.ext_iff_mulVec.mpr fun u => by
    rw [← mulVec_mulVec, one_mulVec]
    exact congrArg Prod.snd ((hcomp (0, u)).2)
  refine ⟨(⟨x₁, y₁, hx₁, hy₁⟩, ⟨x₂, y₂, hx₂, hy₂⟩), Units.ext
    (Matrix.ext_iff_mulVec.mpr fun v => β.injective ?_)⟩
  rw [apply_blockConj_mulVec, hG]

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem gramForm_blockConj (F : ((Fin r → K) × (Fin s → K)) → ((Fin r → K) × (Fin s → K)) → K)
    (hF : ∀ v w, gramForm h (1 : Matrix (Fin n) (Fin n) K) v w = F (β v) (β w))
    (x : GL (Fin r) K × GL (Fin s) K)
    (hx : ∀ u u', F ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ u.1,
      (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ u.2) ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ u'.1,
        (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ u'.2) = F u u')
    (v w : Fin n → K) :
    gramForm h (1 : Matrix (Fin n) (Fin n) K)
      (((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v)
      (((blockConj β x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w) =
    gramForm h (1 : Matrix (Fin n) (Fin n) K) v w := by
  rw [hF, hF, apply_blockConj_mulVec, apply_blockConj_mulVec, hx]

theorem blockConj_mem_gramSU
    (F : ((Fin r → K) × (Fin s → K)) → ((Fin r → K) × (Fin s → K)) → K)
    (hF : ∀ v w, gramForm h (1 : Matrix (Fin n) (Fin n) K) v w = F (β v) (β w))
    (x : GL (Fin r) K × GL (Fin s) K)
    (hx : ∀ u u', F ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ u.1,
      (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ u.2) ((x.1 : Matrix (Fin r) (Fin r) K) *ᵥ u'.1,
        (x.2 : Matrix (Fin s) (Fin s) K) *ᵥ u'.2) = F u u')
    (hdet : (x.1 : Matrix (Fin r) (Fin r) K).det * (x.2 : Matrix (Fin s) (Fin s) K).det = 1) :
    blockConj β x ∈ gramSU h (1 : Matrix (Fin n) (Fin n) K) :=
  mem_gramSU_iff_isometry.mpr ⟨gramForm_blockConj β h F hF x hx, by rw [det_blockConj, hdet]⟩

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
