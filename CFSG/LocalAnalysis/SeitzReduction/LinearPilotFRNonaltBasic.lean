module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleForms
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoordinateLinear
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRigidityFieldRigid
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.SeitzReduction.LinearPilot

namespace Nonalt

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FourGroupEvenCanonical
open CFSG.ComponentClassification.UnbalancedCatalog.NonalternatingRadical

variable {n : ℕ} {K : Type} [Field K]

section Orth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coe_inv_eq_transpose {A : SpecialLinearGroup ι K}
    (h : (A : Matrix ι ι K)ᵀ * A = 1) :
    ((A⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) =
      (A : Matrix ι ι K)ᵀ := by
  have h2 : (A : Matrix ι ι K) * (A : Matrix ι ι K)ᵀ = 1 :=
    mul_eq_one_comm.mp h
  calc ((A⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K)
      = ((A⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) *
          ((A : Matrix ι ι K) * (A : Matrix ι ι K)ᵀ) := by
        rw [h2, Matrix.mul_one]
    _ = (A : Matrix ι ι K)ᵀ := by
        have h3 : ((A⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) *
            (A : Matrix ι ι K) = 1 := by
          rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
            Matrix.SpecialLinearGroup.coe_one]
        rw [← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem transpose_mul_self_mul {A B : SpecialLinearGroup ι K}
    (hA : (A : Matrix ι ι K)ᵀ * A = 1)
    (hB : (B : Matrix ι ι K)ᵀ * B = 1) :
    ((A * B : SpecialLinearGroup ι K) : Matrix ι ι K)ᵀ *
      ((A * B : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (A : Matrix ι ι K),
    hA, Matrix.one_mul, hB]

theorem transpose_mul_self_inv {A : SpecialLinearGroup ι K}
    (hA : (A : Matrix ι ι K)ᵀ * A = 1) :
    ((A⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K)ᵀ *
      ((A⁻¹ : SpecialLinearGroup ι K) : Matrix ι ι K) = 1 := by
  rw [coe_inv_eq_transpose hA, transpose_transpose]
  exact mul_eq_one_comm.mp hA

theorem toGL_mem_matrixIsometryGroup {A : SpecialLinearGroup ι K}
    (hA : (A : Matrix ι ι K)ᵀ * A = 1) :
    Matrix.SpecialLinearGroup.toGL A ∈ matrixIsometryGroup (1 : Matrix ι ι K) := by
  rw [mem_matrixIsometryGroup, Matrix.mul_one]
  exact hA

variable (K ι) in
@[expose] def orthSL : Subgroup (SpecialLinearGroup ι K) where
  carrier := {A | (A : Matrix ι ι K)ᵀ * A = 1}
  mul_mem' hA hB := transpose_mul_self_mul hA hB
  one_mem' := by
    change ((1 : SpecialLinearGroup ι K) : Matrix ι ι K)ᵀ * ((1 : SpecialLinearGroup ι K) :
      Matrix ι ι K) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, transpose_one, Matrix.one_mul]
  inv_mem' hA := transpose_mul_self_inv hA

end Orth

section Defs

@[expose] def radical (i : Fin n) : Subgroup (projectiveSL n K) :=
  ((radicalGroup (K := K) i).comap (Matrix.SpecialLinearGroup.toGL)).map (proj n K)

@[expose] def levi0 (i : Fin n) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {A | (A : Matrix (Fin n) (Fin n) K)ᵀ * A = 1 ∧
    (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = Pi.single i 1}
  mul_mem' {A B} hA hB :=
    ⟨transpose_mul_self_mul hA.1 hB.1, by
      rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, hB.2, hA.2]⟩
  one_mem' := ⟨by rw [Matrix.SpecialLinearGroup.coe_one, transpose_one, Matrix.one_mul],
    by rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]⟩
  inv_mem' {A} hA := ⟨transpose_mul_self_inv hA.1, by
    rw [coe_inv_eq_transpose hA.1]
    calc (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ Pi.single i 1 =
        (A : Matrix (Fin n) (Fin n) K)ᵀ *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1) := by
          rw [hA.2]
      _ = Pi.single i 1 := by rw [mulVec_mulVec, hA.1, one_mulVec]⟩

@[expose] def levi (i : Fin n) : Subgroup (projectiveSL n K) :=
  (levi0 (K := K) i).map (proj n K)

end Defs

section Fix

theorem proj_mem_autFixSubgroup_dualAut {A : SpecialLinearGroup (Fin n) K}
    (hA : (A : Matrix (Fin n) (Fin n) K)ᵀ * A = 1) :
    proj n K A ∈ autFixSubgroup (dualAut n K) := by
  rw [mem_autFixSubgroup, dualAut_proj]
  congr 1
  apply Subtype.ext
  change ((A⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ = A
  rw [coe_inv_eq_transpose hA, transpose_transpose]

theorem levi_le (i : Fin n) : levi (K := K) i ≤ autFixSubgroup (dualAut n K) := by
  rintro _ ⟨A, hA, rfl⟩
  exact proj_mem_autFixSubgroup_dualAut hA.1

variable [CharP K 2]

theorem radical_mul_self (hn : Even n) {i : Fin n} {x : projectiveSL n K} (hx : x ∈ radical i) :
    x * x = 1 := by
  obtain ⟨A, hA, rfl⟩ := hx
  have h : A * A = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_one]
    exact mul_self_of_mem_radicalGroup hn hA
  rw [← map_mul, h, map_one]

theorem radical_comm (hn : Even n) {i : Fin n} {x y : projectiveSL n K} (hx : x ∈ radical i)
    (hy : y ∈ radical i) : x * y = y * x := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨B, hB, rfl⟩ := hy
  have h : A * B = B * A := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul]
    exact radicalGroup_comm hn hA hB
  rw [← map_mul, h, map_mul]

theorem isPGroup_radical (hn : Even n) (i : Fin n) : IsPGroup 2 (radical (K := K) i) := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simp only [pow_one, OneMemClass.coe_one, sq]
  exact radical_mul_self hn x.2

theorem card_radical_le [Finite K] (hn : Even n) (i : Fin n) :
    Nat.card (radical (K := K) i) ≤ Nat.card K ^ (n - 1) := by
  have : Finite (GL (Fin n) K) := Finite.of_injective Units.val Units.val_injective
  rw [← card_radicalGroup hn i]
  have h1 := Subgroup.card_map_dvd ((radicalGroup (K := K) i).comap
    (Matrix.SpecialLinearGroup.toGL)) (proj n K)
  have h2 := Subgroup.card_comap_dvd_of_injective (radicalGroup (K := K) i)
    (Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective
  exact (Nat.le_of_dvd Nat.card_pos h1).trans (Nat.le_of_dvd Nat.card_pos h2)

theorem disjoint_radical_levi (hn : Even n) (i : Fin n) :
    Disjoint (radical (K := K) i) (levi (K := K) i) := by
  rw [Subgroup.disjoint_def]
  rintro x ⟨A, hA, rfl⟩ ⟨B, hB, hBA⟩
  obtain ⟨v, hv, c, hc⟩ := (mem_radicalGroup hn).1 hA
  have hc' : (A : Matrix (Fin n) (Fin n) K) = radicalMatrix v c := hc
  obtain ⟨l, -, hl⟩ := mem_scalars.1 (proj_eq_proj_iff.1 hBA)
  have hAB : (A : Matrix (Fin n) (Fin n) K) =
      (B : Matrix (Fin n) (Fin n) K) * scalar (Fin n) (l : K) := by
    rw [← hl, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have hAe : (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 = (l : K) • Pi.single i 1 := by
    have hs : scalar (Fin n) (l : K) *ᵥ (Pi.single i 1 : Fin n → K) =
        (l : K) • Pi.single i 1 := by
      funext j
      rw [scalar_apply, mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    rw [hAB, ← mulVec_mulVec, hs, mulVec_smul, hB.2]
  rw [hc', radicalMatrix_mulVec_single hv] at hAe
  have hdec : c • onesVec + v + (1 : K) • Pi.single i 1 =
      (0 : K) • onesVec + 0 + (l : K) • Pi.single i 1 := by
    rw [zero_smul, add_zero, zero_add, one_smul, ← hAe]
    abel
  obtain ⟨hc0, hv0, -⟩ := decomp_unique hn hv (zero_mem _) hdec
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [hc', hc0, hv0, radicalMatrix_zero]
    rfl
  rw [hA1, map_one]

variable [Finite K]

theorem mem_autFixSubgroup_dualAut_iff (hn3 : 3 ≤ n) {x : projectiveSL n K} :
    x ∈ autFixSubgroup (dualAut n K) ↔
      ∃ A : SpecialLinearGroup (Fin n) K, (A : Matrix (Fin n) (Fin n) K)ᵀ * A = 1 ∧
        proj n K A = x := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨B, rfl⟩ := proj_surjective n K x
    have hcomm : Commute (dualAut n K) (conjAut n K (Matrix.SpecialLinearGroup.toGL B)) := by
      rw [conjAut_toGL]
      have h := CFSG.RankThree.CASymplecticSubfield.mul_conj_eq (dualAut n K) (proj n K B)
      rw [show dualAut n K (proj n K B) = proj n K B from hx] at h
      exact h
    obtain ⟨g, hg, hgB⟩ := (commute_dualAut_conjAut_iff hn3 _).mp hcomm
    have hg' : g ∈ matrixIsometryGroup (1 : Matrix (Fin n) (Fin n) K) := hg
    have hdet : (g : Matrix (Fin n) (Fin n) K).det = 1 :=
      CFSG.ComponentClassification.UnbalancedCatalog.det_eq_one_of_mem_matrixIsometryGroup
        (C := 1) (by rw [Units.val_one]; exact hg')
    set A : SpecialLinearGroup (Fin n) K := ⟨g, hdet⟩ with hAdef
    refine ⟨A, ?_, ?_⟩
    · have h := mem_matrixIsometryGroup.mp hg'
      rw [Matrix.mul_one] at h
      exact h
    · have hA : Matrix.SpecialLinearGroup.toGL A = g := Units.ext rfl
      have h2 : MulAut.conj (proj n K A) = MulAut.conj (proj n K B) := by
        rw [← conjAut_toGL, ← conjAut_toGL, hA, hgB]
      exact ProjectivePlane.conj_injective_projectiveSL (F := K) hn3 h2
  · rintro ⟨A, hA, rfl⟩
    exact proj_mem_autFixSubgroup_dualAut hA

theorem le_normalizer_radical (hn : Even n) (hn3 : 3 ≤ n) (i : Fin n) :
    autFixSubgroup (dualAut n K) ≤ normalizer (radical (K := K) i : Set (projectiveSL n K)) := by
  have key : ∀ x ∈ autFixSubgroup (dualAut n K), ∀ y ∈ radical (K := K) i,
      x * y * x⁻¹ ∈ radical (K := K) i := by
    intro x hx y hy
    obtain ⟨A, hA, rfl⟩ := (mem_autFixSubgroup_dualAut_iff hn3).1 hx
    obtain ⟨B, hB, rfl⟩ := hy
    refine ⟨A * B * A⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change Matrix.SpecialLinearGroup.toGL (A * B * A⁻¹) ∈ radicalGroup i
    rw [map_mul, map_mul, map_inv]
    exact CFSG.ComponentClassification.OutcomeLocal.conj_mem_radicalGroup hn
      (toGL_mem_matrixIsometryGroup hA) hB
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key x hx y, fun h => ?_⟩
  have := key x⁻¹ (inv_mem hx) _ h
  simpa [mul_assoc] using this

theorem exists_radical_mul_levi (hn : Even n) (hn3 : 3 ≤ n) (i : Fin n) {x : projectiveSL n K}
    (hx : x ∈ autFixSubgroup (dualAut n K)) :
    ∃ ρ ∈ radical (K := K) i, ∃ s ∈ levi (K := K) i, ρ * s = x := by
  obtain ⟨A, hA, rfl⟩ := (mem_autFixSubgroup_dualAut_iff hn3).1 hx
  set y : Fin n → K := (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 - Pi.single i 1 with hy
  have hy0 : onesVec ⬝ᵥ y = 0 := by
    have h := onesVec_dotProduct_mulVec_of_mem (toGL_mem_matrixIsometryGroup hA)
      (Pi.single i (1 : K))
    rw [hy, dotProduct_sub]
    exact sub_eq_zero.mpr h
  set ρGL : GL (Fin n) K := radicalGL hn hy0 (y i) with hρGL
  have hρR : ρGL ∈ radicalGroup i := mem_radicalGroup_of_dotProduct hn hy0 rfl
  have hdet : (ρGL : Matrix (Fin n) (Fin n) K).det = 1 :=
    CFSG.ComponentClassification.UnbalancedCatalog.det_eq_one_of_mem_matrixIsometryGroup
      (C := 1) (by rw [Units.val_one]; exact radicalGroup_le hn i hρR)
  set ρ : SpecialLinearGroup (Fin n) K := ⟨ρGL, hdet⟩ with hρ
  have hρGL' : Matrix.SpecialLinearGroup.toGL ρ = ρGL := Units.ext rfl
  have hρmat : (ρ : Matrix (Fin n) (Fin n) K) = radicalMatrix y (y i) := rfl
  have hρρ : (ρ : Matrix (Fin n) (Fin n) K)ᵀ * ρ = 1 := by
    rw [hρmat, radicalMatrix_transpose]
    exact radicalMatrix_mul_self hn hy0 _
  have hρe : (ρ : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 =
      (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 := by
    have h2 : (y i) • (onesVec : Fin n → K) + (y i) • onesVec = 0 := by
      rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]
    rw [hρmat, radicalMatrix_mulVec, dotProduct_single_one, onesVec_dotProduct_single, one_smul,
      mul_one]
    calc Pi.single i 1 + y i • onesVec + y + y i • onesVec
        = Pi.single i 1 + y + (y i • onesVec + y i • onesVec) := by abel
      _ = (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i 1 := by rw [h2, add_zero, hy]; abel
  have hρmem : ρ ∈ (radicalGroup (K := K) i).comap Matrix.SpecialLinearGroup.toGL := by
    rw [Subgroup.mem_comap, hρGL']
    exact hρR
  refine ⟨proj n K ρ, ⟨ρ, hρmem, rfl⟩,
    proj n K (ρ⁻¹ * A), ⟨ρ⁻¹ * A, ⟨transpose_mul_self_mul (transpose_mul_self_inv hρρ) hA, ?_⟩,
      rfl⟩, by rw [← map_mul, mul_inv_cancel_left]⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← hρe, mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    one_mulVec]

end Fix

end Nonalt

end CFSG.SeitzReduction.LinearPilot
