module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUf

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem map_bar_real (M : Matrix (Fin 4) (Fin 4) h.fixedField) :
    (M.map h.fixedField.subtype).map h.bar = M.map h.fixedField.subtype := by
  ext i j
  exact (M i j).2

variable {δ : h.fixedFieldˣ} (h2 : (2 : h.fixedField) ≠ 0)

theorem y_mem_SU (hδ : ¬ IsSquare (δ : h.fixedField)) (h3 : 2 < Nat.card h.fixedField)
    {d : h.fixedFieldˣ} (P : GL (Fin 4) K)
    (hPP : uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) =
      ((d : h.fixedField) : K) • (gramQ (δ : h.fixedField)).map h.fixedField.subtype)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) :
    P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4 := by
  have : Finite K := h.finite
  set U : Matrix (Fin 4) (Fin 4) K :=
    (Umat δ h2 g : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype with hU
  have hUc : ((GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = U := rfl
  have hPi : (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hPi' : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [mem_unitarySU_iff h]
  constructor
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, hPi,
      det_one, one_mul, hUc, hU]
    change (h.fixedField.subtype.mapMatrix
      (Umat δ h2 g : Matrix (Fin 4) (Fin 4) h.fixedField)).det = 1
    rw [← RingHom.map_det, det_Umat δ h2 hδ h3 g, map_one]
  · have hUT : uStar h U = Uᵀ := by rw [uStar, hU, map_bar_real]
    have hG : Uᵀ * (gramQ (δ : h.fixedField)).map h.fixedField.subtype * U =
        (gramQ (δ : h.fixedField)).map h.fixedField.subtype := by
      rw [hU, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, Umat_gram]
    change uStar h ((P : Matrix (Fin 4) (Fin 4) K) * U * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
      ((P : Matrix (Fin 4) (Fin 4) K) * U * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) = 1
    rw [uStar_mul, uStar_mul, hUT]
    calc uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) * (Uᵀ * uStar h (P : Matrix (Fin 4) (Fin 4) K)) *
          ((P : Matrix (Fin 4) (Fin 4) K) * U * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K))
        = uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (Uᵀ * (uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) * U) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by simp only [Matrix.mul_assoc]
      _ = uStar h (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) *
            (uStar h (P : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K)) *
            (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
          rw [hPP, Matrix.mul_smul, Matrix.smul_mul, hG]
      _ = uStar h ((P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) *
            ((P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K)) := by
          rw [uStar_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPi', uStar_one, Matrix.one_mul]

@[expose] def yHom (P : GL (Fin 4) K)
    (hmem : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4) :
    Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →* unitarySU p f K 4 :=
  ((MulAut.conj P).toMonoidHom.comp
    ((GeneralLinearGroup.map h.fixedField.subtype).comp (Umat δ h2))).codRestrict _ hmem

theorem coe_yHom (P : GL (Fin 4) K)
    (hmem : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) :
    ((yHom h h2 P hmem g : unitarySU p f K 4) : GL (Fin 4) K) =
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ := rfl

theorem yHom_real (P : GL (Fin 4) K)
    (hmem : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)),
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹ ∈ unitarySU p f K 4)
    {A : GL (Fin 4) K}
    (hAP : (A : Matrix (Fin 4) (Fin 4) K) * (P : Matrix (Fin 4) (Fin 4) K).map h.bar = P)
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))) :
    A * GeneralLinearGroup.map h.bar ((yHom h h2 P hmem g : unitarySU p f K 4) : GL (Fin 4) K) *
      A⁻¹ = (yHom h h2 P hmem g : unitarySU p f K 4) := by
  have hAP' : A * GeneralLinearGroup.map h.bar P = P := Units.ext hAP
  have hU : GeneralLinearGroup.map h.bar
      (GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g)) =
        GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) :=
    Units.ext (map_bar_real h _)
  rw [coe_yHom, map_mul, map_mul, map_inv, hU]
  calc A * (GeneralLinearGroup.map h.bar P *
        GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) *
        (GeneralLinearGroup.map h.bar P)⁻¹) * A⁻¹
      = (A * GeneralLinearGroup.map h.bar P) *
          GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) *
          (A * GeneralLinearGroup.map h.bar P)⁻¹ := by group
    _ = _ := by rw [hAP']

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
