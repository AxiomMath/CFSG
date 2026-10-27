module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OCUa
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OILd
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4OIUf

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace OIU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  UnitaryOut StabU DiagU ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank LinearFlag
  CFSG.ComponentClassification.CatalogueBUnitaryB CFSG.LinearGroups
  CFSG.ComponentClassification.OddSelector
  CFSG.ComponentClassification.CatalogueBOrthogonalFourNonsplit

section Kernel

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem rowOHom_eq_one_iff {m : ℕ} (h2 : (2 : k) ≠ 0) {δ : kˣ} (hδ : ¬ IsSquare (δ : k))
    (ψ : (Fin m → k) ≃ₗ[k] hermitianSubmodule (δ : k))
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) :
    rowOHom δ ψ g = 1 ↔ g = 1 ∨ g = -1 := by
  have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
  rw [← specialRho_eq_one_iff_sign (δ : k) h2]
  constructor
  · intro h
    apply Subtype.ext
    apply linearConjGL_injective ψ
    rw [Subgroup.coe_one, map_one]
    exact h
  · intro h
    change linearConjGL ψ (specialRho (δ : k) h2 g).val = 1
    rw [h]
    exact map_one _

theorem eq_one_or_neg_one_of_rowOHom_scalar (hodd : Odd (Nat.card k)) {δ : kˣ}
    (hδ : ¬ IsSquare (δ : k)) (ψ : (Fin 4 → k) ≃ₗ[k] hermitianSubmodule (δ : k))
    (g : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) (c : kˣ)
    (hc : rowOHom δ ψ g = GeneralLinearGroup.scalar (Fin 4) c) : g = 1 ∨ g = -1 := by
  classical
  have h2 : (2 : k) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have : Fact (¬ IsSquare (δ : k)) := ⟨hδ⟩
  have : Finite (extension (δ : k)) :=
    Finite.of_equiv _ (QuadraticAlgebra.equivProd (δ : k) 0).symm
  have hone : ∀ g, rowOHom δ ψ g = 1 ↔ g = 1 ∨ g = -1 := rowOHom_eq_one_iff h2 hδ ψ
  have hE9 : 9 ≤ Nat.card (extension (δ : k)) := by
    rw [extension_card]
    have := ProjectiveEigenspace.three_le_card_of_two_ne_zero h2
    nlinarith
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) :=
    CatalogueBGeneralLinear.specialLinear_perfect 2 (extension (δ : k)) le_rfl
      (Or.inr (by omega)) (Or.inr (by omega))
  have hcen : (rowOHom δ ψ).rangeRestrict g ∈ Subgroup.center (rowOHom δ ψ).range := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simp only [Subgroup.coe_mul, MonoidHom.coe_rangeRestrict]
    rw [hc]
    exact (GeneralLinearGroup.scalar_commute c (y : GL (Fin 4) k)).symm
  have hkerc : (rowOHom δ ψ).rangeRestrict.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (extension (δ : k))) := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker, hone] at hx
    rw [mem_center_sl_two_iff]
    exact hx
  exact (mem_center_sl_two_iff g).mp (mem_center_of_map_mem_center _ hkerc hcen)

end Kernel

section Coords

variable {k : Type} [Field k] (δ : kˣ) (h2 : (2 : k) ≠ 0)

theorem Umat_uE_one : (Umat δ h2 (OIL.uE (δ : k) 1) : Matrix (Fin 4) (Fin 4) k) = OIL.mU1 :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Umat_mulVec, OIL.coord_uE_one, OIL.mU1_mulVec])

theorem Umat_uE_omega :
    (Umat δ h2 (OIL.uE (δ : k) ⟨0, 1⟩) : Matrix (Fin 4) (Fin 4) k) = OIL.mUw (δ : k) :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Umat_mulVec, OIL.coord_uE_omega,
      OIL.mUw_mulVec])

theorem Umat_lE_one : (Umat δ h2 (OIL.lE (δ : k) 1) : Matrix (Fin 4) (Fin 4) k) = OIL.mL1 :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Umat_mulVec, OIL.coord_lE_one, OIL.mL1_mulVec])

end Coords

section Over

variable {k₀ K : Type} [Field k₀] [Field K] (ι : k₀ →+* K)

theorem map_mU1 : (OIL.mU1 : Matrix (Fin 4) (Fin 4) k₀).map ι = OIL.mU1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [OIL.mU1, map_ofNat]

theorem map_mUw (δ : k₀) : (OIL.mUw δ).map ι = OIL.mUw (ι δ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [OIL.mUw, map_ofNat]

theorem map_mL1 : (OIL.mL1 : Matrix (Fin 4) (Fin 4) k₀).map ι = OIL.mL1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [OIL.mL1, map_ofNat]

end Over

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_smul_one_of_comm_y (hp2 : p ≠ 2) {δ : h.fixedFieldˣ} (h2 : (2 : h.fixedField) ≠ 0)
    (P : GL (Fin 4) K) (y : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →*
      unitarySU p f K 4)
    (hy : ∀ g, ((y g : unitarySU p f K 4) : GL (Fin 4) K) =
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹) (M : GL (Fin 4) K)
    (hM : ∀ g ∈ ({OIL.uE (δ : h.fixedField) 1, OIL.uE (δ : h.fixedField) ⟨0, 1⟩,
      OIL.lE (δ : h.fixedField) 1} : Set _), M * (y g : GL (Fin 4) K) = (y g : GL (Fin 4) K) * M) :
    ∃ c : K, (M : Matrix (Fin 4) (Fin 4) K) = c • 1 := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_odd h hp2
  set N : Matrix (Fin 4) (Fin 4) K := ((P⁻¹ * M * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with hN
  have key : ∀ g, M * (y g : GL (Fin 4) K) = (y g : GL (Fin 4) K) * M →
      N * (Umat δ h2 g : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype =
        (Umat δ h2 g : Matrix (Fin 4) (Fin 4) h.fixedField).map h.fixedField.subtype * N := by
    intro g hg
    rw [hy] at hg
    have h1 : P⁻¹ * M * P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) =
        GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * (P⁻¹ * M * P) := by
      calc P⁻¹ * M * P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g)
          = P⁻¹ * (M * (P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹)) *
              P := by group
        _ = P⁻¹ * ((P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹) * M) *
              P := by rw [hg]
        _ = _ := by group
    exact congrArg Units.val h1
  have hU1 := key (OIL.uE (δ : h.fixedField) 1) (hM _ (by simp))
  have hUw := key (OIL.uE (δ : h.fixedField) ⟨0, 1⟩) (hM _ (by simp))
  have hL1 := key (OIL.lE (δ : h.fixedField) 1) (hM _ (by simp))
  rw [Umat_uE_one, map_mU1] at hU1
  rw [Umat_uE_omega, map_mUw] at hUw
  rw [Umat_lE_one, map_mL1] at hL1
  have hS := OIL.schur_matrix h2K hU1 hUw hL1
  refine ⟨N 0 0, ?_⟩
  have hPi : (P : Matrix (Fin 4) (Fin 4) K) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (M : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) * N *
        (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [hN, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPi,
          Matrix.one_mul, Matrix.mul_assoc, hPi, Matrix.mul_one]
    _ = (P : Matrix (Fin 4) (Fin 4) K) * (N 0 0 • 1) * (↑P⁻¹ : Matrix (Fin 4) (Fin 4) K) := by
        rw [← hS]
    _ = N 0 0 • 1 := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPi]

theorem y_pow_p {δ : h.fixedFieldˣ}
    (y : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →* unitarySU p f K 4)
    {u : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField))}
    (hu : u ∈ ({OIL.uE (δ : h.fixedField) 1, OIL.uE (δ : h.fixedField) ⟨0, 1⟩,
      OIL.lE (δ : h.fixedField) 1} : Set _)) : y u ^ p = 1 := by
  have : CharP K p := h.charP
  have : CharP h.fixedField p := Subfield.charP h.fixedField p
  rw [← map_pow]
  rcases hu with rfl | rfl | rfl
  · rw [OIL.uE_pow_char, map_one]
  · rw [OIL.uE_pow_char, map_one]
  · rw [OIL.lE_pow_char, map_one]

theorem eq_one_of_isCU_fix (hp2 : p ≠ 2) {δ : h.fixedFieldˣ} (h2 : (2 : h.fixedField) ≠ 0)
    (P : GL (Fin 4) K) (y : Matrix.SpecialLinearGroup (Fin 2) (extension (δ : h.fixedField)) →*
      unitarySU p f K 4)
    (hy : ∀ g, ((y g : unitarySU p f K 4) : GL (Fin 4) K) =
      P * GeneralLinearGroup.map h.fixedField.subtype (Umat δ h2 g) * P⁻¹) {M : GL (Fin 4) K}
    {χ : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hχ : IsCU h M χ)
    (hfix : ∀ g, χ (thU p f K (y g)) = thU p f K (y g)) : χ = 1 := by
  have hcomm : ∀ u ∈ ({OIL.uE (δ : h.fixedField) 1, OIL.uE (δ : h.fixedField) ⟨0, 1⟩,
      OIL.lE (δ : h.fixedField) 1} : Set _),
      M * (y u : GL (Fin 4) K) = (y u : GL (Fin 4) K) * M := by
    intro u hu
    have hyp := y_pow_p h y hu
    set w : unitarySU p f K 4 := ⟨_, conj_mem_SU h hχ.1 (y u)⟩ with hw
    have hwp : w ^ p = 1 := by
      apply Subtype.ext
      rw [SubmonoidClass.coe_pow, hw]
      change (M * (y u : GL (Fin 4) K) * M⁻¹) ^ p = 1
      rw [conj_pow, ← SubmonoidClass.coe_pow, hyp, OneMemClass.coe_one, mul_one, mul_inv_cancel]
    have h1 : thU p f K w = thU p f K (y u) := by
      rw [← hχ.apply h (y u), hfix]
    have h2' := OCU.eq_of_thU_eq h hp2 hyp hwp h1
    have h3 : M * (y u : GL (Fin 4) K) * M⁻¹ = y u := congrArg Subtype.val h2'
    calc M * (y u : GL (Fin 4) K) = M * (y u : GL (Fin 4) K) * M⁻¹ * M := by group
      _ = _ := by rw [h3]
  obtain ⟨c, hc⟩ := eq_smul_one_of_comm_y h hp2 h2 P y hy M hcomm
  exact hχ.unique h (isCU_one_of_eq_smul h hχ.1 hc)

end OIU

end CFSG.ComponentClassification.CatFactsL4U4
