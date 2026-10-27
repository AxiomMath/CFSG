module

public import CFSG.LieType.Sp6Spin.Model
public import CFSG.RankThree.PartOne.AUTSL.OmegaDickson

public section

namespace CFSG.LieType.Sp6Spin

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LieType.Universal.Spin (toStdD)
open QuadraticMap
open scoped Matrix

section FieldOnly

variable {K : Type} [Field K] [CharP K 2]

theorem polar_pvec_eq_zero_of_X8_mulVec_eq {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j)
    {s t : Bool} (h : toStdD 4 γ = lv i j s t) {c : K} (hc : c ≠ 0) {w : Fin (2 * 4) → K}
    (hw : ((X8 γ c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w = w) :
    polar (coordinateQuadPlus 4 K) w (AutOm.pvec i s) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec j t) = 0 := by
  have hmain : AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec (K := K) j t)
      (c • AutOm.pvec (K := K) i s) w = w := (X8_mulVec hij h c w).symm.trans hw
  rw [AutOm.eichlerC, QuadraticMap.map_smul, AutOm.form_pvec, smul_zero, zero_mul,
    zero_smul, sub_zero] at hmain
  have hAB : polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) j t) •
        (c • AutOm.pvec (K := K) i s) =
      polar (coordinateQuadPlus 4 K) w (c • AutOm.pvec (K := K) i s) •
        AutOm.pvec (K := K) j t := by
    rw [add_sub_assoc] at hmain
    exact sub_eq_zero.1 (add_left_cancel (by rw [add_zero]; exact hmain))
  have hEq : (polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) j t) * c) •
        AutOm.pvec (K := K) i s =
      (c * polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) i s)) •
        AutOm.pvec (K := K) j t := by
    rw [QuadraticMap.polar_smul_right, smul_eq_mul, smul_smul] at hAB
    exact hAB
  constructor
  · have h3 := congrArg (fun z =>
      polar (coordinateQuadPlus 4 K) z (AutOm.pvec (K := K) j (!t))) hEq
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, AutOm.polar_pvec,
      AutOm.polar_pvec] at h3
    simp [hij, Bool.not_not, smul_eq_mul] at h3
    exact h3.resolve_left hc
  · have h3 := congrArg (fun z =>
      polar (coordinateQuadPlus 4 K) z (AutOm.pvec (K := K) i (!s))) hEq
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, AutOm.polar_pvec,
      AutOm.polar_pvec] at h3
    simp [hij.symm, Bool.not_not, smul_eq_mul] at h3
    exact h3.resolve_right hc

private theorem X8_rootC_mulVec {K : Type} [Field K] [CharP K 2] (y : Fin (2 * 4) → K)
    (hy : polar (coordinateQuadPlus 4 K) y (AutOm.pvec (K := K) 3 true) = 0) :
    ((X8 (K := K) rootC 1 : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y =
      y + polar (coordinateQuadPlus 4 K) y (AutOm.pvec (K := K) 0 false) •
        AutOm.pvec (K := K) 3 true := by
  rw [show rootC = fromStd (lv 0 3 false true) from by decide]
  rw [X8_mulVec (by decide : (0 : Fin 4) ≠ 3) (s := false) (t := true)
    (toStdD_fromStd_lv 0 3 false true (by decide)) (1 : K)]
  simp only [AutOm.eichlerC, QuadraticMap.map_smul, AutOm.form_pvec, smul_zero, zero_mul,
    zero_smul, QuadraticMap.polar_smul_right, one_smul, hy, sub_zero, add_zero,
    sub_eq_add_neg, neg_smul, CharTwo.neg_eq]

private theorem X8_rootD_mulVec {K : Type} [Field K] [CharP K 2] (y : Fin (2 * 4) → K)
    (hy : polar (coordinateQuadPlus 4 K) y (AutOm.pvec (K := K) 3 true) = 0) :
    ((X8 (K := K) rootD 1 : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y =
      y + polar (coordinateQuadPlus 4 K) y (AutOm.pvec (K := K) 0 true) •
        AutOm.pvec (K := K) 3 true := by
  rw [show rootD = fromStd (lv 0 3 true true) from by decide]
  rw [X8_mulVec (by decide : (0 : Fin 4) ≠ 3) (s := true) (t := true)
    (toStdD_fromStd_lv 0 3 true true (by decide)) (1 : K)]
  simp only [AutOm.eichlerC, QuadraticMap.map_smul, AutOm.form_pvec, smul_zero, zero_mul,
    zero_smul, QuadraticMap.polar_smul_right, one_smul, hy, sub_zero, add_zero,
    sub_eq_add_neg, neg_smul, CharTwo.neg_eq]

private theorem X8_rootD_pvec {K : Type} [Field K] [CharP K 2] :
    ((X8 (K := K) rootD 1 : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ AutOm.pvec (K := K) 3 true =
      AutOm.pvec (K := K) 3 true := by
  rw [show rootD = fromStd (lv 0 3 true true) from by decide]
  rw [X8_mulVec (by decide : (0 : Fin 4) ≠ 3) (s := true) (t := true)
    (toStdD_fromStd_lv 0 3 true true (by decide)) (1 : K)]
  simp only [AutOm.eichlerC, QuadraticMap.map_smul, AutOm.form_pvec, smul_zero, zero_mul,
    zero_smul, QuadraticMap.polar_smul_right, one_smul, AutOm.polar_pvec_self,
    AutOm.polar_pvec_of_ne (by decide : (3 : Fin 4) ≠ 0), sub_zero, add_zero]

end FieldOnly

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem polar_pvec_eq_zero_of_mem_fixRho {w : Fin (2 * 4) → K}
    (hw : ∀ g ∈ fixRho K,
      ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w = w)
    {i j : Fin 4} (hij : i ≠ j) (hi : i ≠ 0) (hj : j ≠ 0) (s t : Bool) :
    polar (coordinateQuadPlus 4 K) w (AutOm.pvec i s) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec j t) = 0 :=
  polar_pvec_eq_zero_of_X8_mulVec_eq hij (roots_check i j s t hij).1 one_ne_zero
    (hw _ (X8_mem_fixRho hij (roots_check i j s t hij).1 hi hj 1))

theorem exists_eq_smul_of_forall_fixRho {w : Fin (2 * 4) → K}
    (hw : ∀ g ∈ fixRho K,
      ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w = w) :
    ∃ a : K, w = a • (AutOm.pvec 0 true + AutOm.pvec 0 false) := by
  have hzero : ∀ (k : Fin 4), k ≠ 0 → ∀ b : Bool,
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) k b) = 0 := by
    intro k hk b
    fin_cases k
    · exact absurd rfl hk
    · exact (polar_pvec_eq_zero_of_mem_fixRho (K := K) hw (i := 1) (j := 2) (by decide)
        (by decide) (by decide) b false).1
    · exact (polar_pvec_eq_zero_of_mem_fixRho (K := K) hw (i := 2) (j := 1) (by decide)
        (by decide) (by decide) b false).1
    · exact (polar_pvec_eq_zero_of_mem_fixRho (K := K) hw (i := 3) (j := 1) (by decide)
        (by decide) (by decide) b false).1
  set a : K := polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 0 false) with ha
  set b : K := polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 0 true) with hb
  have hweq : w = a • AutOm.pvec (K := K) 0 true + b • AutOm.pvec (K := K) 0 false := by
    have hcoord : ∀ k r, polar (coordinateQuadPlus 4 K)
        (w - (a • AutOm.pvec (K := K) 0 true +
          b • AutOm.pvec (K := K) 0 false)) (AutOm.pvec (K := K) k r) = 0 := by
      intro k r
      rw [QuadraticMap.polar_sub_left, QuadraticMap.polar_add_left,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left]
      by_cases hk : k = 0
      · subst hk
        cases r
        · rw [AutOm.polar_pvec, AutOm.polar_pvec]
          simp [ha, hb, smul_eq_mul]
        · rw [AutOm.polar_pvec, AutOm.polar_pvec]
          simp [ha, hb, smul_eq_mul]
      · rw [hzero k hk r, AutOm.polar_pvec_of_ne (Ne.symm hk),
          AutOm.polar_pvec_of_ne (Ne.symm hk)]
        simp
    exact sub_eq_zero.1 (AutOm.eq_zero_of_polar_pvec hcoord)
  have h3zero : polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 3 true) = 0 :=
    hzero 3 (by decide) true
  have hCval := X8_rootC_mulVec (K := K) w h3zero
  have hDval := X8_rootD_mulVec (K := K) w h3zero
  have hYact : ((Y (K := K) 1 : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w =
      w + (a + b) • AutOm.pvec (K := K) 3 true := by
    rw [Y, Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hCval,
      Matrix.mulVec_add, Matrix.mulVec_smul, hDval, X8_rootD_pvec, add_smul]
    abel
  have hfixY : w + (a + b) • AutOm.pvec (K := K) 3 true = w := by
    rw [← hYact]
    exact hw (Y (K := K) 1) (Y_mem_fixRho (K := K) 1)
  have hsum : (a + b) • (AutOm.pvec (K := K) 3 true : Fin (2 * 4) → K) = 0 := by
    exact add_left_cancel (by rw [add_zero]; exact hfixY)
  have hcoef : a + b = 0 := by
    have hp : polar (coordinateQuadPlus 4 K)
        ((a + b) • AutOm.pvec (K := K) 3 true) (AutOm.pvec (K := K) 3 false) =
        polar (coordinateQuadPlus 4 K) (0 : Fin (2 * 4) → K)
          (AutOm.pvec (K := K) 3 false) := by rw [hsum]
    rw [QuadraticMap.polar_smul_left, AutOm.polar_pvec, QuadraticMap.polar_zero_left,
      smul_eq_mul] at hp
    simpa using hp
  have hba : b = a := by
    have hb' : b = -a := eq_neg_of_add_eq_zero_right hcoef
    rwa [CharTwo.neg_eq] at hb'
  exact ⟨a, by rw [hweq, hba, smul_add]⟩

theorem mem_fixRho_of_mem_normalizer {g : Om8 K}
    (hg : g ∈ Subgroup.normalizer (fixRho K : Set (Om8 K))) : g ∈ fixRho K := by
  have hfix : ∀ f ∈ fixRho K,
      ((f : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false)) =
        ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false) := by
    intro f hf
    have hmem : g⁻¹ * f * g ∈ fixRho K :=
      (Subgroup.mem_normalizer_iff''.1 hg f).1 hf
    have hgv : (((g⁻¹ * f * g : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false) =
        AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false :=
      (mem_fixRho_iff (g⁻¹ * f * g)).1 hmem
    have hconj : f * g = g * (g⁻¹ * f * g) := by group
    calc ((f : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false))
        = (((f * g : Om8 K) : GL (Fin (2 * 4)) K) :
            Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
              (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false) := by
          rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      _ = (((g * (g⁻¹ * f * g) : Om8 K) : GL (Fin (2 * 4)) K) :
            Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
              (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false) := by
          rw [hconj]
      _ = ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            ((((g⁻¹ * f * g : Om8 K) : GL (Fin (2 * 4)) K) :
              Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
                (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false)) := by
          rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      _ = ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
            (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false) := by rw [hgv]
  obtain ⟨a, ha⟩ := exists_eq_smul_of_forall_fixRho hfix
  have hv : AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false =
      CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four := by
    rw [AutOm.plusUnitVector_eq one_le_four]
    congr 2 <;> exact Fin.ext rfl
  have hQv : coordinateQuadPlus 4 K
      (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false) = 1 := by
    rw [hv]
    exact AutOm.plusUnitVector_form one_le_four
  have hQgv : coordinateQuadPlus 4 K
      (((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false)) = 1 := by
    rw [CFSG.RankThree.PartOne.AUTSL.map_mulVec_of_mem
      (matrixDerived_le_isometries _ g.2), hQv]
  have hQa : a * a = 1 := by
    have h := congrArg (coordinateQuadPlus 4 K) ha
    rw [hQgv, QuadraticMap.map_smul, hQv] at h
    simpa [smul_eq_mul] using h.symm
  have ha1 : a = 1 := by
    rcases mul_self_eq_one_iff.1 hQa with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  rw [mem_fixRho_iff, ha, ha1, one_smul]

private theorem X8_mem_spinSeven_of_tri {γ δ : Fin 4 → ℤ} (hδ : δ ∈ rootsD4)
    (htri : tri δ = γ) (hfix : X8 (K := K) δ 1 ∈ fixRho K) :
    X8 (K := K) γ 1 ∈ spinSeven K := by
  rw [spinSeven_eq, Subgroup.mem_map]
  refine ⟨X8 (K := K) δ 1, hfix, ?_⟩
  change theta (X8 (K := K) δ 1) = X8 (K := K) γ 1
  rw [theta_X8 hδ, htri]

private theorem polar_pvec_eq_zero_of_mem_spinSeven {w : Fin (2 * 4) → K}
    (hw : ∀ g ∈ spinSeven K,
      ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w = w)
    {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (hγ : X8 (K := K) γ 1 ∈ spinSeven K) :
    polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) i s) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) j t) = 0 :=
  polar_pvec_eq_zero_of_X8_mulVec_eq hij h one_ne_zero (hw _ hγ)

theorem eq_zero_of_forall_spinSeven {w : Fin (2 * 4) → K}
    (hw : ∀ g ∈ spinSeven K,
      ((g : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ w = w) :
    w = 0 := by
  have hC : polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 0 false) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 3 true) = 0 := by
    have hto : toStdD 4 (tri (tri (fromStd (lv 0 3 false true)))) = lv 1 2 true false :=
      by decide
    have hδ : tri (tri (fromStd (lv 0 3 false true))) ∈ rootsD4 :=
      mem_rootsD4_iff.2 ⟨1, 2, by decide, true, false, hto⟩
    have hδfix : X8 (K := K) (tri (tri (fromStd (lv 0 3 false true)))) 1 ∈ fixRho K :=
      X8_mem_fixRho (by decide : (1 : Fin 4) ≠ 2) hto (by decide) (by decide) 1
    have hγ : X8 (K := K) (fromStd (lv 0 3 false true)) 1 ∈ spinSeven K :=
      X8_mem_spinSeven_of_tri hδ (tri_tri_tri _) hδfix
    exact polar_pvec_eq_zero_of_mem_spinSeven hw (by decide)
      (toStdD_fromStd_lv 0 3 false true (by decide)) hγ
  have hCm : polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 0 true) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 3 false) = 0 := by
    have hto : toStdD 4 (tri (tri (fromStd (lv 0 3 true false)))) = lv 1 2 false true :=
      by decide
    have hδ : tri (tri (fromStd (lv 0 3 true false))) ∈ rootsD4 :=
      mem_rootsD4_iff.2 ⟨1, 2, by decide, false, true, hto⟩
    have hδfix : X8 (K := K) (tri (tri (fromStd (lv 0 3 true false)))) 1 ∈ fixRho K :=
      X8_mem_fixRho (by decide : (1 : Fin 4) ≠ 2) hto (by decide) (by decide) 1
    have hγ : X8 (K := K) (fromStd (lv 0 3 true false)) 1 ∈ spinSeven K :=
      X8_mem_spinSeven_of_tri hδ (tri_tri_tri _) hδfix
    exact polar_pvec_eq_zero_of_mem_spinSeven hw (by decide)
      (toStdD_fromStd_lv 0 3 true false (by decide)) hγ
  have h12t : polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 1 true) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 2 true) = 0 := by
    have hto : toStdD 4 (fromStd (lv 1 2 true true)) = lv 1 2 true true :=
      toStdD_fromStd_lv 1 2 true true (by decide)
    have hδ : fromStd (lv 1 2 true true) ∈ rootsD4 :=
      mem_rootsD4_iff.2 ⟨1, 2, by decide, true, true, hto⟩
    have hδfix : X8 (K := K) (fromStd (lv 1 2 true true)) 1 ∈ fixRho K :=
      X8_mem_fixRho (by decide : (1 : Fin 4) ≠ 2) hto (by decide) (by decide) 1
    have hγ : X8 (K := K) (fromStd (lv 1 2 true true)) 1 ∈ spinSeven K :=
      X8_mem_spinSeven_of_tri hδ (by decide) hδfix
    exact polar_pvec_eq_zero_of_mem_spinSeven hw (by decide) hto hγ
  have h12f : polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 1 false) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (AutOm.pvec (K := K) 2 false) = 0 := by
    have hto : toStdD 4 (fromStd (lv 1 2 false false)) = lv 1 2 false false :=
      toStdD_fromStd_lv 1 2 false false (by decide)
    have hδ : fromStd (lv 1 2 false false) ∈ rootsD4 :=
      mem_rootsD4_iff.2 ⟨1, 2, by decide, false, false, hto⟩
    have hδfix : X8 (K := K) (fromStd (lv 1 2 false false)) 1 ∈ fixRho K :=
      X8_mem_fixRho (by decide : (1 : Fin 4) ≠ 2) hto (by decide) (by decide) 1
    have hγ : X8 (K := K) (fromStd (lv 1 2 false false)) 1 ∈ spinSeven K :=
      X8_mem_spinSeven_of_tri hδ (by decide) hδfix
    exact polar_pvec_eq_zero_of_mem_spinSeven hw (by decide) hto hγ
  refine AutOm.eq_zero_of_polar_pvec fun k r => ?_
  fin_cases k <;> cases r <;>
    simp [hC.1, hC.2, hCm.1, hCm.2, h12t.1, h12t.2, h12f.1, h12f.2]

private theorem mem_fixRho_iff_theta_mem_spinSeven (x : Om8 K) :
    x ∈ fixRho K ↔ theta x ∈ spinSeven K := by
  rw [spinSeven_eq, Subgroup.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [theta.injective hyx] at hy

private theorem mem_spinSeven_of_mem_map_subtype {x : Om8 K}
    (h : ((x : Om8 K) : GL (Fin (2 * 4)) K) ∈
      (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype) :
    x ∈ spinSeven K := by
  rw [Subgroup.mem_map] at h
  obtain ⟨k, hk, hkval⟩ := h
  rwa [Subtype.ext hkval] at hk

private theorem mem_spinSeven_of_normalizer_of_mem_derived {n : GL (Fin (2 * 4)) K}
    (hA : n ∈ matrixDerived (coordinateQuadPlus 4 K))
    (hN : n ∈ Subgroup.normalizer
      ((spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :
        Set (GL (Fin (2 * 4)) K))) :
    n ∈ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype := by
  let N : Om8 K := ⟨n, hA⟩
  have hNs : N ∈ Subgroup.normalizer (spinSeven K : Set (Om8 K)) := by
    rw [Subgroup.mem_normalizer_iff] at hN ⊢
    intro h
    constructor
    · intro hh
      have hhG : ((h : Om8 K) : GL (Fin (2 * 4)) K) ∈
          (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
        Subgroup.mem_map.2 ⟨h, hh, rfl⟩
      obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.1 ((hN _).1 hhG)
      have hEq : N * h * N⁻¹ = k := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv]
        simpa using hkval.symm
      rwa [hEq]
    · intro hh
      have hG : ((N * h * N⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) ∈
          (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
        Subgroup.mem_map.2 ⟨N * h * N⁻¹, hh, rfl⟩
      have hhG : ((h : Om8 K) : GL (Fin (2 * 4)) K) ∈
          (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
        (hN ((h : Om8 K) : GL (Fin (2 * 4)) K)).2
          (by simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hG)
      exact mem_spinSeven_of_mem_map_subtype hhG
  have htheta : theta⁻¹ N ∈ Subgroup.normalizer (fixRho K : Set (Om8 K)) := by
    have h1 : ∀ f : Om8 K,
        theta ((theta⁻¹ N) * f * (theta⁻¹ N)⁻¹) = N * theta f * N⁻¹ := by
      intro f
      rw [map_mul, map_mul, map_inv, MulAut.apply_inv_self]
    rw [Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · intro hf
      rw [mem_fixRho_iff_theta_mem_spinSeven, h1 f]
      exact (Subgroup.mem_normalizer_iff.1 hNs (theta f)).1
        ((mem_fixRho_iff_theta_mem_spinSeven f).1 hf)
    · intro hf
      have hfS : N * theta f * N⁻¹ ∈ spinSeven K := by
        rw [← h1 f]
        exact (mem_fixRho_iff_theta_mem_spinSeven _).1 hf
      exact (mem_fixRho_iff_theta_mem_spinSeven f).2
        ((Subgroup.mem_normalizer_iff.1 hNs (theta f)).2 hfS)
  have hfixN : theta⁻¹ N ∈ fixRho K := mem_fixRho_of_mem_normalizer htheta
  have hNS : N ∈ spinSeven K := by
    have h := (mem_fixRho_iff_theta_mem_spinSeven (theta⁻¹ N)).1 hfixN
    rwa [MulAut.apply_inv_self] at h
  exact Subgroup.mem_map.2 ⟨N, hNS, rfl⟩

private theorem coe_conj_theta_inv_eq {n : GL (Fin (2 * 4)) K} {r : GL (Fin (2 * 4)) K}
    (hr : r = CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus 4 K)
      (AutOm.vPlus one_le_four) (AutOm.plusUnitVector_form_ne_zero one_le_four))
    (hr2 : r * r = 1) {N₀ : Om8 K}
    (hN₀ : ((N₀ : Om8 K) : GL (Fin (2 * 4)) K) = n * r)
    {f : Om8 K} (hf : f ∈ fixRho K) :
    ((N₀ * theta⁻¹ f * N₀⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) =
      n * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) * n⁻¹ := by
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hρf : AutOm.plusRefl (K := K) one_le_four f = f := hf
  have hθf : theta⁻¹ f = AutOm.plusRefl (K := K) one_le_four (theta f) := by
    have h1 : (theta⁻¹ : MulAut (Om8 K)) = AutOm.plusRefl (K := K) one_le_four *
        theta * AutOm.plusRefl (K := K) one_le_four := plusRefl_theta_plusRefl.symm
    rw [h1]
    simp [MulAut.mul_apply, hρf]
  have hpf : ((AutOm.plusRefl (K := K) one_le_four (theta f) : Om8 K) :
      GL (Fin (2 * 4)) K) = r * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) * r⁻¹ := by
    rw [hr, AutOm.plusRefl]
    exact CFSG.RankThree.PartOne.AUTSL.reflAut_apply_val _ _ _
  calc ((N₀ * theta⁻¹ f * N₀⁻¹ : Om8 K) : GL (Fin (2 * 4)) K)
      = ((N₀ : Om8 K) : GL (Fin (2 * 4)) K) *
          ((theta⁻¹ f : Om8 K) : GL (Fin (2 * 4)) K) *
          ((N₀ : Om8 K) : GL (Fin (2 * 4)) K)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    _ = (n * r) * (r * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) * r⁻¹) *
          (r * n⁻¹) := by rw [hN₀, hθf, hpf, mul_inv_rev, hrinv]
    _ = n * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) * n⁻¹ := by
        have hg : (n * r) * (r * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) * r⁻¹) *
            (r * n⁻¹) = n * (r * r) * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) *
              (r * r) * n⁻¹ := by
          rw [hrinv]
          group
        rw [hg, hr2]
        group

private theorem conj_mem_spinSeven_of_mul_reflMat_mem {n : GL (Fin (2 * 4)) K}
    {r : GL (Fin (2 * 4)) K}
    (hr : r = CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus 4 K)
      (AutOm.vPlus one_le_four) (AutOm.plusUnitVector_form_ne_zero one_le_four))
    (hr2 : r * r = 1) {N₀ : Om8 K}
    (hN₀ : ((N₀ : Om8 K) : GL (Fin (2 * 4)) K) = n * r)
    (hN : n ∈ Subgroup.normalizer
      ((spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :
        Set (GL (Fin (2 * 4)) K)))
    {f : Om8 K} (hf : f ∈ fixRho K) :
    N₀ * theta⁻¹ f * N₀⁻¹ ∈ spinSeven K := by
  have hS : ((theta f : Om8 K) : GL (Fin (2 * 4)) K) ∈
      (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
    Subgroup.mem_map.2 ⟨theta f, (mem_fixRho_iff_theta_mem_spinSeven f).1 hf, rfl⟩
  have hconjG : n * ((theta f : Om8 K) : GL (Fin (2 * 4)) K) * n⁻¹ ∈
      (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
    (Subgroup.mem_normalizer_iff.1 hN _).1 hS
  refine mem_spinSeven_of_mem_map_subtype ?_
  rw [coe_conj_theta_inv_eq hr hr2 hN₀ hf]
  exact hconjG

private theorem conj_fixRho_of_conj_spinSeven {N₀ m : Om8 K} (hmθ : theta m = N₀)
    (hconj : ∀ f ∈ fixRho K, N₀ * theta⁻¹ f * N₀⁻¹ ∈ spinSeven K) :
    ∀ s ∈ spinSeven K, m * s * m⁻¹ ∈ fixRho K := by
  have hθ2 : (theta : MulAut (Om8 K)) * theta = theta⁻¹ := by
    have h := theta_cube (K := K)
    rw [pow_three] at h
    exact eq_inv_of_mul_eq_one_left h
  intro s hs
  rw [spinSeven_eq, Subgroup.mem_map] at hs
  obtain ⟨f, hf, rfl⟩ := hs
  have hθθ : theta (theta f) = theta⁻¹ f := by
    rw [← MulAut.mul_apply, hθ2]
  have h1 : theta (m * theta f * m⁻¹) = N₀ * theta⁻¹ f * N₀⁻¹ := by
    rw [map_mul, map_mul, map_inv, hmθ, hθθ]
  refine (mem_fixRho_iff_theta_mem_spinSeven _).2 ?_
  change theta (m * theta f * m⁻¹) ∈ spinSeven K
  rw [h1]
  exact hconj f hf

private theorem false_of_conj_fixRho {m : Om8 K}
    (hmconj : ∀ s ∈ spinSeven K, m * s * m⁻¹ ∈ fixRho K) : False := by
  let v : Fin (2 * 4) → K := AutOm.vPlus one_le_four
  have hv1 : coordinateQuadPlus 4 K v = 1 := AutOm.plusUnitVector_form one_le_four
  have hvne : v ≠ 0 := by
    intro h
    rw [h, QuadraticMap.map_zero] at hv1
    exact zero_ne_one hv1
  have hvp : v = AutOm.pvec (K := K) 0 true + AutOm.pvec (K := K) 0 false := by
    rw [show v = CFSG.SeitzReduction.OmegaPilot.plusUnitVector one_le_four from rfl]
    rw [AutOm.plusUnitVector_eq one_le_four]
    congr 2 <;> exact Fin.ext rfl
  have hfixall : ∀ s ∈ spinSeven K,
      ((s : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v := by
    intro s hs
    have hv' := (mem_fixRho_iff (m * s * m⁻¹)).1 (hmconj s hs)
    rw [← hvp] at hv'
    have h1 : ((m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
        (((s : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
            Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) = v := by
      have h2 := hv'
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec] at h2
      exact h2
    have hcancel : ∀ y : Fin (2 * 4) → K,
        (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
          (((m : GL (Fin (2 * 4)) K) :
            Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y) = y := by
      intro y
      rw [Matrix.mulVec_mulVec]
      rw [show (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
          ((m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 from ?_]
      · rw [Matrix.one_mulVec]
      · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
          Units.val_one]
    have h1' := congrArg (fun z => (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ z) h1
    simpa only [hcancel] using h1'
  have hw0 : (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = 0 :=
    eq_zero_of_forall_spinSeven fun s hs => hfixall s hs
  have hmm : ((m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ
      (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = v := by
    rw [Matrix.mulVec_mulVec]
    rw [show ((m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        (((m⁻¹ : Om8 K) : GL (Fin (2 * 4)) K) :
          Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) = 1 from ?_]
    · rw [Matrix.one_mulVec]
    · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one]
  rw [hw0, Matrix.mulVec_zero] at hmm
  exact hvne hmm.symm

private theorem not_mem_derived_mul_reflMat_of_mem_normalizer {n : GL (Fin (2 * 4)) K}
    (hN : n ∈ Subgroup.normalizer
      ((spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :
        Set (GL (Fin (2 * 4)) K)))
    (hB : n * CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus 4 K)
      (AutOm.vPlus one_le_four) (AutOm.plusUnitVector_form_ne_zero one_le_four) ∈
        matrixDerived (coordinateQuadPlus 4 K)) : False := by
  let r : GL (Fin (2 * 4)) K :=
    CFSG.RankThree.PartOne.AUTSL.reflMat (coordinateQuadPlus 4 K) (AutOm.vPlus one_le_four)
      (AutOm.plusUnitVector_form_ne_zero one_le_four)
  have hr2 : r * r = 1 :=
    CFSG.RankThree.PartOne.AUTSL.reflMat_mul_self (AutOm.vPlus one_le_four)
      (AutOm.plusUnitVector_form_ne_zero one_le_four)
  let N₀ : Om8 K := ⟨n * r, hB⟩
  let m : Om8 K := theta⁻¹ N₀
  have hmθ : theta m = N₀ := MulAut.apply_inv_self (Om8 K) theta N₀
  have hconj : ∀ f ∈ fixRho K, N₀ * theta⁻¹ f * N₀⁻¹ ∈ spinSeven K := fun f hf =>
    conj_mem_spinSeven_of_mul_reflMat_mem (r := r) rfl hr2 rfl hN hf
  exact false_of_conj_fixRho (conj_fixRho_of_conj_spinSeven hmθ hconj)

theorem mem_spinSeven_of_mem_normalizer {n : GL (Fin (2 * 4)) K}
    (hn : ∀ v, coordinateQuadPlus 4 K ((n : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
      coordinateQuadPlus 4 K v)
    (hN : n ∈ Subgroup.normalizer
      ((spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :
        Set (GL (Fin (2 * 4)) K))) :
    n ∈ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype := by
  have hnIso : n ∈ matrixIsometries (coordinateQuadPlus 4 K) := by
    rw [mem_matrixIsometries_iff]
    intro v
    rw [matrixLinearEquiv_apply]
    exact hn v
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  rcases CFSG.RankThree.PartOne.AUTSL.mem_or_mul_reflMat_mem hnd hT hnIso
    (AutOm.vPlus one_le_four)
    (AutOm.plusUnitVector_form_ne_zero one_le_four) with hA | hB
  · exact mem_spinSeven_of_normalizer_of_mem_derived hA hN
  · exact (not_mem_derived_mul_reflMat_of_mem_normalizer hN hB).elim

theorem spinNormalizer :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      ∀ g : GL (Fin (2 * 4)) K,
        (∀ v : Fin (2 * 4) → K,
          coordinateQuadPlus 4 K ((g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
            coordinateQuadPlus 4 K v) →
        (∀ M ∈ spinSeven K,
          g * (M : GL (Fin (2 * 4)) K) * g⁻¹ ∈
            (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype) →
        g ∈ (spinSeven K).map (matrixDerived (coordinateQuadPlus 4 K)).subtype := by
  intro K _ _ _ _ g hg hconj
  refine mem_spinSeven_of_mem_normalizer hg (Subgroup.mem_normalizer_fintype ?_)
  rintro _ ⟨M, hM, rfl⟩
  exact hconj M hM

end CFSG.LieType.Sp6Spin
