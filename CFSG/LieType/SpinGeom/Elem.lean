module

public import CFSG.LieType.SpinGeom.Frame
public import CFSG.LieType.Sp6Spin.Model
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck

public section

namespace CFSG.LieType.SpinGeom

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.Sp6Spin
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear QuadraticMap
open CFSG.LieType.Universal.Spin (toStdD)
open scoped Matrix

section Eichler

variable {K : Type} [Field K] [CharP K 2]

theorem X8_mulVec_eich {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (h : toStdD 4 γ = lv i j s t) (c : K) (y : Fin (2 * 4) → K) :
    ((X8 γ c : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y =
      y + (c * polar (coordinateQuadPlus 4 K) y (AutOm.pvec j t)) • AutOm.pvec i s +
        (c * polar (coordinateQuadPlus 4 K) y (AutOm.pvec i s)) • AutOm.pvec j t := by
  rw [X8_mulVec hij h c y, AutOm.eichlerC, QuadraticMap.map_smul, quad_pvec, smul_zero,
    zero_mul, zero_smul, sub_zero, polar_smul_right, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
  module

end Eichler

section Membership

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem X8_mem_spinSeven {γ : Fin 4 → ℤ} (hγ : γ ∈ rootsD4) {i j : Fin 4} (hij : i ≠ j)
    {s t : Bool} (h : toStdD 4 (tri (tri γ)) = lv i j s t) (hi : i ≠ 0) (hj : j ≠ 0) (c : K) :
    X8 γ c ∈ spinSeven K := by
  rw [spinSeven_eq]
  refine Subgroup.mem_map.2 ⟨X8 (tri (tri γ)) c, X8_mem_fixRho hij h hi hj c, ?_⟩
  change theta (X8 (tri (tri γ)) c) = X8 γ c
  rw [theta_X8 (tri_mem_roots (tri_mem_roots hγ)), tri_tri_tri]

@[expose] def rootAB (a b : Fin 4) : Fin 4 → ℤ :=
  fromStd (lv a b (decide (a ≠ 1)) (!decide (b ≠ 1)))

theorem rootAB_mem {a b : Fin 4} (hab : a ≠ b) : rootAB a b ∈ rootsD4 := by
  obtain ⟨h, -⟩ := roots_check a b (decide (a ≠ 1)) (!decide (b ≠ 1)) hab
  exact mem_rootsD4_iff.2 ⟨a, b, hab, decide (a ≠ 1), !decide (b ≠ 1), h⟩

theorem toStdD_rootAB {a b : Fin 4} (hab : a ≠ b) :
    toStdD 4 (rootAB a b) = lv a b (decide (a ≠ 1)) (!decide (b ≠ 1)) :=
  (roots_check a b (decide (a ≠ 1)) (!decide (b ≠ 1)) hab).1

theorem tri_tri_rootAB : ∀ a b : Fin 4, a ≠ b → ∃ (i j : Fin 4) (s t : Bool),
    i ≠ j ∧ i ≠ 0 ∧ j ≠ 0 ∧ toStdD 4 (tri (tri (rootAB a b))) = lv i j s t := by
  unfold rootAB
  decide

theorem exists_mem_spinSeven_elemMap (a b : Fin 4) (hab : a ≠ b) (c : K) :
    ∃ h ∈ spinSeven K, ∀ v,
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        elemMap K a b c v := by
  obtain ⟨i, j, s, t, hij, hi, hj, h⟩ := tri_tri_rootAB a b hab
  refine ⟨X8 (rootAB a b) c, X8_mem_spinSeven (rootAB_mem hab) hij h hi hj c, fun v => ?_⟩
  rw [X8_mulVec_eich hab (toStdD_rootAB hab) c v]
  rfl

end Membership

section Long

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def rootEE (a b : Fin 4) : Fin 4 → ℤ :=
  fromStd (lv a b (decide (a ≠ 1)) (decide (b ≠ 1)))

@[expose] def rootFF (c d : Fin 4) : Fin 4 → ℤ :=
  fromStd (lv c d (!decide (c ≠ 1)) (!decide (d ≠ 1)))

theorem toStdD_rootEE {a b : Fin 4} (hab : a ≠ b) :
    toStdD 4 (rootEE a b) = lv a b (decide (a ≠ 1)) (decide (b ≠ 1)) :=
  (roots_check a b (decide (a ≠ 1)) (decide (b ≠ 1)) hab).1

theorem toStdD_rootFF {c d : Fin 4} (hcd : c ≠ d) :
    toStdD 4 (rootFF c d) = lv c d (!decide (c ≠ 1)) (!decide (d ≠ 1)) :=
  (roots_check c d (!decide (c ≠ 1)) (!decide (d ≠ 1)) hcd).1

omit [Finite K] in
theorem X8_rootEE_mulVec {a b : Fin 4} (hab : a ≠ b) (m : K) (y : Fin (2 * 4) → K) :
    ((X8 (rootEE a b) m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y =
      y + (m * polar (coordinateQuadPlus 4 K) y (frameE K b)) • frameE K a +
        (m * polar (coordinateQuadPlus 4 K) y (frameE K a)) • frameE K b := by
  rw [X8_mulVec_eich hab (toStdD_rootEE hab) m y]
  rfl

omit [Finite K] in
theorem X8_rootFF_mulVec {c d : Fin 4} (hcd : c ≠ d) (m : K) (y : Fin (2 * 4) → K) :
    ((X8 (rootFF c d) m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ y =
      y + (m * polar (coordinateQuadPlus 4 K) y (frameF K d)) • frameF K c +
        (m * polar (coordinateQuadPlus 4 K) y (frameF K c)) • frameF K d := by
  rw [X8_mulVec_eich hcd (toStdD_rootFF hcd) m y]
  rfl

omit [Finite K] in
theorem X8_long_mulVec {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hac : a ≠ c) (had : a ≠ d) (m : K) (v : Fin (2 * 4) → K) :
    (((X8 (rootEE a b) m * X8 (rootFF c d) m : Om8 K) : GL (Fin (2 * 4)) K) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v = longMap K a b c d m v := by
  have hmul : (((X8 (rootEE a b) m * X8 (rootFF c d) m : Om8 K) : GL (Fin (2 * 4)) K) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      ((X8 (rootEE a b) m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
        ((X8 (rootFF c d) m : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := rfl
  rw [hmul, ← Matrix.mulVec_mulVec, X8_rootFF_mulVec hcd, X8_rootEE_mulVec hab]
  have h1 : polar (coordinateQuadPlus 4 K)
      (v + (m * polar (coordinateQuadPlus 4 K) v (frameF K d)) • frameF K c +
        (m * polar (coordinateQuadPlus 4 K) v (frameF K c)) • frameF K d) (frameE K b) =
        coordY K v b := by
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, polar_frameF_frameE,
      polar_frameF_frameE, if_neg hbc.symm, if_neg hbd.symm]
    simp [coordY]
  have h2 : polar (coordinateQuadPlus 4 K)
      (v + (m * polar (coordinateQuadPlus 4 K) v (frameF K d)) • frameF K c +
        (m * polar (coordinateQuadPlus 4 K) v (frameF K c)) • frameF K d) (frameE K a) =
        coordY K v a := by
    rw [polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, polar_frameF_frameE,
      polar_frameF_frameE, if_neg hac.symm, if_neg had.symm]
    simp [coordY]
  rw [h1, h2]
  unfold longMap coordX coordY
  module

end Long

section LongMem

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem refl0_lv_check : ∀ (j : Fin 4) (s t : Bool), j ≠ 0 →
    refl0 (fromStd (lv 0 j s t)) = fromStd (lv 0 j (!s) t) := by decide

theorem dot_check : ∀ a b c d : Fin 4, (a ≠ b ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) →
    0 ≤ lv a b (decide (a ≠ 1)) (decide (b ≠ 1)) ⬝ᵥ
      lv c d (!decide (c ≠ 1)) (!decide (d ≠ 1)) := by decide

theorem dot_check_pair : ∀ (j : Fin 4) (s t : Bool), j ≠ 0 →
    0 ≤ lv 0 j s t ⬝ᵥ lv 0 j (!s) t := by decide

theorem pair_check : ∀ a b c d : Fin 4, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∃ (j : Fin 4) (s t : Bool), j ≠ 0 ∧
      ((tri (fromStd (lv 0 j s t)) = rootEE a b ∧ tri (refl0 (fromStd (lv 0 j s t))) = rootFF c d) ∨
       (tri (fromStd (lv 0 j s t)) = rootFF c d ∧
        tri (refl0 (fromStd (lv 0 j s t))) = rootEE a b)) := by
  unfold rootEE rootFF
  decide

theorem X8_pair_mem_fixRho {j : Fin 4} (hj : j ≠ 0) (s t : Bool) (c : K) :
    X8 (fromStd (lv 0 j s t)) c * X8 (refl0 (fromStd (lv 0 j s t))) c ∈ fixRho K := by
  have hγ : fromStd (lv 0 j s t) ∈ rootsD4 :=
    mem_rootsD4_iff.2 ⟨0, j, hj.symm, s, t, (roots_check 0 j s t hj.symm).1⟩
  have hcomm : Commute (X8 (fromStd (lv 0 j s t)) c) (X8 (fromStd (lv 0 j (!s) t)) c) := by
    exact commute_X8 (isD4Root_lv 0 j s t hj.symm) (isD4Root_lv 0 j (!s) t hj.symm)
      (dot_check_pair j s t hj) c c
  change AutOm.plusRefl (K := K) one_le_four _ = _
  rw [map_mul, plusRefl_X8 hγ c, plusRefl_X8 (refl0_mem_roots hγ) c, refl0_refl0,
    refl0_lv_check j s t hj]
  exact hcomm.symm.eq

theorem exists_mem_spinSeven_longMap {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (m : K) :
    ∃ h ∈ spinSeven K, ∀ v,
      ((h : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v =
        longMap K a b c d m v := by
  obtain ⟨j, s, t, hj, hcase⟩ := pair_check a b c d hab hcd hac had hbc hbd
  have hγ : fromStd (lv 0 j s t) ∈ rootsD4 :=
    mem_rootsD4_iff.2 ⟨0, j, hj.symm, s, t, (roots_check 0 j s t hj.symm).1⟩
  have hmem : X8 (tri (fromStd (lv 0 j s t))) m * X8 (tri (refl0 (fromStd (lv 0 j s t)))) m ∈
      spinSeven K := by
    rw [spinSeven_eq]
    refine Subgroup.mem_map.2 ⟨_, X8_pair_mem_fixRho hj s t m, ?_⟩
    change theta (X8 (fromStd (lv 0 j s t)) m * X8 (refl0 (fromStd (lv 0 j s t))) m) = _
    rw [map_mul, theta_X8 hγ, theta_X8 (refl0_mem_roots hγ)]
  have hcomm : Commute (X8 (rootEE a b) m) (X8 (rootFF c d) m) :=
    commute_X8 (isD4Root_lv a b _ _ hab) (isD4Root_lv c d _ _ hcd)
      (dot_check a b c d ⟨hab, hcd, hac, had, hbc, hbd⟩) m m
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at hmem
    exact ⟨_, hmem, fun v => X8_long_mulVec hab hcd hbc hbd hac had m v⟩
  · rw [h1, h2] at hmem
    rw [← hcomm.eq] at hmem
    exact ⟨_, hmem, fun v => X8_long_mulVec hab hcd hbc hbd hac had m v⟩

end LongMem

end CFSG.LieType.SpinGeom
