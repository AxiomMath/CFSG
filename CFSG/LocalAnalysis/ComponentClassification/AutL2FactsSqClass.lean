module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldInv
public import CFSG.Assembly.ComponentTypeDefs

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped commutatorElement

universe u

variable {F : Type u} [Field F] [Finite F]

theorem ringAut_comm (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  have := isCyclic_ringAut F
  exact IsCyclic.commGroup.mul_comm σ τ

theorem isSquare_mul_iff {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSquare (a * b) ↔ (IsSquare a ↔ IsSquare b) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha hb), ← quadraticChar_one_iff_isSquare ha,
    ← quadraticChar_one_iff_isSquare hb, map_mul]
  rcases quadraticChar_dichotomy ha with h1 | h1 <;>
    rcases quadraticChar_dichotomy hb with h2 | h2 <;> simp [h1, h2]

omit [Finite F] in
theorem isSquare_ringEquiv_iff (σ : F ≃+* F) (a : F) : IsSquare (σ a) ↔ IsSquare a := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨σ.symm r, by rw [← map_mul, ← hr, RingEquiv.symm_apply_apply]⟩
  · rintro ⟨r, hr⟩
    exact ⟨σ r, by rw [hr, map_mul]⟩

abbrev SqLeft (x : PGammaL2 F) : Prop :=
  x.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range

theorem sqLeft_mul (x y : PGammaL2 F) : SqLeft (x * y) ↔ (SqLeft x ↔ SqLeft y) := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective x.left
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective y.left
  have hxy : (x * y).left =
      Matrix.ProjGenLinGroup.mk (A * Matrix.GeneralLinearGroup.map x.right.toRingHom B) := by
    rw [SemidirectProduct.mul_left, ← hA, ← hB, pgl2FieldAut_mk, ← map_mul]
  have hd : ((A * Matrix.GeneralLinearGroup.map x.right.toRingHom B : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F).det =
      (A : Matrix (Fin 2) (Fin 2) F).det * x.right (B : Matrix (Fin 2) (Fin 2) F).det := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul]
    congr 1
    exact (RingHom.map_det x.right.toRingHom (B : Matrix (Fin 2) (Fin 2) F)).symm
  have hB0 : x.right (B : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [map_ne_zero]
    exact B.det_ne_zero
  simp only [SqLeft]
  rw [hxy, ← hA, ← hB, pgl2_mk_mem_psl2_range_iff_det_isSquare,
    pgl2_mk_mem_psl2_range_iff_det_isSquare, pgl2_mk_mem_psl2_range_iff_det_isSquare,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, hd, isSquare_mul_iff A.det_ne_zero hB0,
    isSquare_ringEquiv_iff]

omit [Finite F] in
theorem sqLeft_one : SqLeft (1 : PGammaL2 F) := one_mem _

theorem sqLeft_inv (x : PGammaL2 F) : SqLeft x⁻¹ ↔ SqLeft x := by
  have h := sqLeft_mul x x⁻¹
  rw [mul_inv_cancel] at h
  have h1 := h.mp sqLeft_one
  exact h1.symm

omit [Finite F] in
theorem mem_pslRange_iff (g : PGammaL2 F) :
    g ∈ pGammaL2PSLRange F ↔ g.right = 1 ∧ SqLeft g := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨rfl, s, rfl⟩
  · rintro ⟨h1, s, hs⟩
    refine ⟨s, ?_⟩
    change SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL s) = g
    rw [hs]
    exact SemidirectProduct.ext rfl (by rw [SemidirectProduct.right_inl, h1])

theorem commutator_mem_pslRange (x y : PGammaL2 F) : ⁅x, y⁆ ∈ pGammaL2PSLRange F := by
  rw [mem_pslRange_iff, commutatorElement_def]
  refine ⟨?_, ?_⟩
  · simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [ringAut_comm x.right y.right]
    group
  · rw [sqLeft_mul, sqLeft_mul, sqLeft_mul, sqLeft_inv, sqLeft_inv]
    tauto

theorem conj_mem_of_pslRange_le {K : Subgroup (PGammaL2 F)} (hK : pGammaL2PSLRange F ≤ K)
    (g : PGammaL2 F) {k : PGammaL2 F} (hk : k ∈ K) : g * k * g⁻¹ ∈ K := by
  have : g * k * g⁻¹ = ⁅g, k⁆ * k := by rw [commutatorElement_def]; group
  rw [this]
  exact K.mul_mem (hK (commutator_mem_pslRange g k)) hk

theorem right_conj (b x : PGammaL2 F) : (b * x * b⁻¹).right = x.right := by
  simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
  rw [ringAut_comm b.right x.right]
  group

theorem mul_mem_pslRange_of_not {g h : PGammaL2 F} (hg1 : g.right = 1) (hh1 : h.right = 1)
    (hg : ¬ SqLeft g) (hh : ¬ SqLeft h) : g * h ∈ pGammaL2PSLRange F := by
  rw [mem_pslRange_iff, sqLeft_mul]
  refine ⟨?_, by tauto⟩
  simp [hg1, hh1]

end CFSG.ComponentClassification.AutL2Facts
