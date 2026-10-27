module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightTrialityAut

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Matrix
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.Universal.Spin
open CFSG.LieType.RootSystem (roots)
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.SymplecticPilot (diagSpEntry diagSpEntry_inl diagSpEntry_inr)

section Diagonal

variable {F : Type} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diag_mul_single_mul_diag (d d' : ι → F) (x y a b : ι) :
    d a * Matrix.single x y (1 : F) a b * d' b = d x * d' y * Matrix.single x y (1 : F) a b := by
  by_cases h : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

theorem diagonal_mul_one_add_smul_mul_diagonal (d d' : ι → F) (hd : ∀ a, d a * d' a = 1)
    (c χ : F) (R : Matrix ι ι F) (hR : ∀ a b, d a * R a b * d' b = χ * R a b) :
    diagonal d * (1 + c • R) * diagonal d' = 1 + (χ * c) • R := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  have h := hR a b
  by_cases hab : a = b
  · subst hab
    simp only [ite_true]
    linear_combination hd a + c * h
  · simp only [hab, ite_false]
    linear_combination c * h

end Diagonal

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem diagSpEntry_plusIdx (u : Fin 4 → Fˣ) (m : Fin 4) (r : Bool) :
    diagSpEntry u (SpinPlus.plusIdx m r) = ((u m ^ boolSign r : Fˣ) : F) := by
  cases r
  · simp [SpinPlus.plusIdx, diagSpEntry_inr]
  · simp [SpinPlus.plusIdx, diagSpEntry_inl]

theorem diagOmega_conj_spinMatrix_x {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (he : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (u : Fin 4 → Fˣ)
    (c : F) :
    diagOmega F 4 u * spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ c) *
        (diagOmega F 4 u)⁻¹ =
      spinMatrix (quadPlus 4 F) (SpinPlus.x 4 F d4_three_le γ
        (((u i ^ boolSign s * u j ^ boolSign t : Fˣ) : F) * c)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← map_inv, diagOmega_coe, diagOmega_coe,
    coe_spinMatrix_spin8X hij he, coe_spinMatrix_spin8X hij he]
  refine diagonal_mul_one_add_smul_mul_diagonal _ _ (fun a => ?_) c _ _ (fun a b => ?_)
  · rcases a with m | m <;> simp
  · have e1 : diagSpEntry u (SpinPlus.plusIdx i s) * diagSpEntry u⁻¹ (SpinPlus.plusIdx j (!t)) =
        ((u i ^ boolSign s * u j ^ boolSign t : Fˣ) : F) := by
      rw [diagSpEntry_plusIdx u i s, diagSpEntry_plusIdx u⁻¹ j (!t), Pi.inv_apply,
        _root_.inv_zpow', boolSign_not, neg_neg, ← Units.val_mul]
    have e2 : diagSpEntry u (SpinPlus.plusIdx j t) * diagSpEntry u⁻¹ (SpinPlus.plusIdx i (!s)) =
        ((u i ^ boolSign s * u j ^ boolSign t : Fˣ) : F) := by
      rw [diagSpEntry_plusIdx u j t, diagSpEntry_plusIdx u⁻¹ i (!s), Pi.inv_apply,
        _root_.inv_zpow', boolSign_not, neg_neg, ← Units.val_mul, mul_comm]
    rw [spin8RootMat, Matrix.add_apply, mul_add, add_mul, mul_add, diag_mul_single_mul_diag,
      diag_mul_single_mul_diag, e1, e2]

@[expose] def corParam (k : Fin 4) (s : Fˣ) : Fin 4 → Fˣ :=
  fun m => s ^ (toStdD 4 (Pi.single k 1) m)

theorem spinMatrix_torusD (k : Fin 4) (s : Fˣ) :
    spinMatrix (quadPlus 4 F) (torusD F d4_three_le k s) = diagOmega F 4 (corParam k s) := by
  apply Units.ext
  rw [diagOmega_coe]
  ext a b
  obtain ⟨m, r, rfl⟩ : ∃ m r, b = SpinPlus.plusIdx m r := by
    rcases b with m | m
    exacts [⟨m, true, rfl⟩, ⟨m, false, rfl⟩]
  rw [spinMatrix_apply, ← (SpinPlus.isCoordFrame_plusFrame d4_three_le).vec_eq m r, torusD,
    HypFrame.spinAction_longTorus_vec, (SpinPlus.isCoordFrame_plusFrame d4_three_le).vec_eq]
  by_cases hab : a = SpinPlus.plusIdx m r
  · subst hab
    simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, Matrix.diagonal_apply_eq,
      diagSpEntry_plusIdx, corParam]
    rw [longCoroot_eq, ← SpinPlus.toStdD_single (by norm_num) k, ← _root_.zpow_mul, mul_comm]
  · simp only [Pi.smul_apply, Pi.single_apply, hab, ite_false, smul_zero,
      Matrix.diagonal_apply_ne _ hab]

theorem spin8Equiv_torusD (k : Fin 4) (s : Fˣ) :
    spin8Equiv F (torusD F d4_three_le k s) = (isHypFrame_plus F 4).frameHom (corParam k s) := by
  rw [spin8Equiv_apply, ← statedOmegaPlusEquiv_diag (by norm_num) (corParam k s)
    (diagOmega_mem_statedOmega_of_one_le (by norm_num) _)]
  congr 1
  exact Subtype.ext (spinMatrix_torusD k s)

theorem frameHom_conj_spin8Equiv_x {γ : Fin 4 → ℤ} {i j : Fin 4} (hij : i ≠ j) {s t : Bool}
    (he : toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) (u : Fin 4 → Fˣ)
    (c : F) :
    (isHypFrame_plus F 4).frameHom u * spin8Equiv F (SpinPlus.x 4 F d4_three_le γ c) *
        ((isHypFrame_plus F 4).frameHom u)⁻¹ =
      spin8Equiv F (SpinPlus.x 4 F d4_three_le γ
        (((u i ^ boolSign s * u j ^ boolSign t : Fˣ) : F) * c)) := by
  rw [← statedOmegaPlusEquiv_diag (by norm_num) u (diagOmega_mem_statedOmega_of_one_le
    (by norm_num) u), spin8Equiv_apply, spin8Equiv_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact diagOmega_conj_spinMatrix_x hij he u c

theorem exists_units_mul_self_eq (v : Fˣ) : ∃ r : Fˣ, r * r = v := by
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' (v : F)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr])⟩

theorem corParam_apply_eq (k m : Fin 4) (s : Fˣ) :
    corParam k s m = s ^ ((![![1, -1, 0, 0], ![0, 1, -1, 0], ![0, 0, 1, -1], ![0, 0, 1, 1]] :
      Fin 4 → Fin 4 → ℤ) k m) := by
  rw [corParam]
  congr 1
  fin_cases k <;> fin_cases m <;> decide

theorem eq_prod_corParam (t : Fin 4 → Fˣ) : ∃ s₀ s₁ s₂ s₃ : Fˣ,
    t = corParam 0 s₀ * corParam 1 s₁ * corParam 2 s₂ * corParam 3 s₃ := by
  obtain ⟨r, hr⟩ := exists_units_mul_self_eq (t 0 * t 1 * t 2 * t 3)
  have hr' : (r : F) * r = t 0 * t 1 * t 2 * t 3 := by
    have h := congrArg Units.val hr
    push_cast at h
    exact h
  refine ⟨t 0, t 0 * t 1, r * (t 3)⁻¹, r, ?_⟩
  funext m
  apply Units.ext
  have h0 := (t 0).ne_zero
  have h1 := (t 1).ne_zero
  have h3 := (t 3).ne_zero
  have hr0 := r.ne_zero
  simp only [Pi.mul_apply, corParam_apply_eq]
  fin_cases m
  · simp
  · simp
  · simp
    field_simp
    linear_combination -hr'
  · simp

end Torus

section Nodes

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] def nodeChar (j : Fin 4) (u : Fin 4 → Fˣ) : Fˣ :=
  u (rootIdxD 4 j) ^ boolSign true * u (rootIdxD' 4 j) ^ boolSign (rootSignD 4 j)

theorem mem_levelParam_pair_iff {a b : Fin 4} (f : Fin 4 → Fˣ) :
    (∀ i ∈ ({a, b} : Finset (Fin 4)), ∀ k ∈ ({a, b} : Finset (Fin 4)), f i = f k) ↔ f a = f b := by
  constructor
  · intro H
    exact H a (by simp) b (by simp)
  · intro h i hi k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi hk
    rcases hi with rfl | rfl <;> rcases hk with rfl | rfl
    all_goals first | rfl | exact h | exact h.symm

theorem mem_signedLevelParam_node_zero (u : Fin 4 → Fˣ) :
    u ∈ signedLevelParam (K := F) (plusNodeSet 4 0) (plusNodeFlip 4 0) ↔ nodeChar 0 u = 1 := by
  have hJ : plusNodeSet 4 0 = {0, 1} := by decide
  have hP : plusNodeFlip 4 0 = ∅ := by decide
  change flipParam F (plusNodeFlip 4 0) u ∈ levelParam (plusNodeSet 4 0) ↔ _
  rw [mem_levelParam, hJ, hP, mem_levelParam_pair_iff]
  simp [flipParam_apply, nodeChar, rootIdxD, rootIdxD', rootSignD, mul_inv_eq_one]

theorem mem_signedLevelParam_node_one (u : Fin 4 → Fˣ) :
    u ∈ signedLevelParam (K := F) (plusNodeSet 4 1) (plusNodeFlip 4 1) ↔ nodeChar 1 u = 1 := by
  have hJ : plusNodeSet 4 1 = {1, 2} := by decide
  have hP : plusNodeFlip 4 1 = ∅ := by decide
  change flipParam F (plusNodeFlip 4 1) u ∈ levelParam (plusNodeSet 4 1) ↔ _
  rw [mem_levelParam, hJ, hP, mem_levelParam_pair_iff]
  simp [flipParam_apply, nodeChar, rootIdxD, rootIdxD', rootSignD, mul_inv_eq_one]

theorem mem_signedLevelParam_node_two (u : Fin 4 → Fˣ) :
    u ∈ signedLevelParam (K := F) (plusNodeSet 4 2) (plusNodeFlip 4 2) ↔ nodeChar 2 u = 1 := by
  have hJ : plusNodeSet 4 2 = {2, 3} := by decide
  have hP : plusNodeFlip 4 2 = ∅ := by decide
  change flipParam F (plusNodeFlip 4 2) u ∈ levelParam (plusNodeSet 4 2) ↔ _
  rw [mem_levelParam, hJ, hP, mem_levelParam_pair_iff]
  simp [flipParam_apply, nodeChar, rootIdxD, rootIdxD', rootSignD, mul_inv_eq_one]

theorem mem_signedLevelParam_node_three (u : Fin 4 → Fˣ) :
    u ∈ signedLevelParam (K := F) (plusNodeSet 4 3) (plusNodeFlip 4 3) ↔ nodeChar 3 u = 1 := by
  have hJ : plusNodeSet 4 3 = {2, 3} := by decide
  have hP : plusNodeFlip 4 3 = {3} := by decide
  change flipParam F (plusNodeFlip 4 3) u ∈ levelParam (plusNodeSet 4 3) ↔ _
  rw [mem_levelParam, hJ, hP, mem_levelParam_pair_iff]
  simp [flipParam_apply, nodeChar, rootIdxD, rootIdxD', rootSignD, eq_inv_iff_mul_eq_one]

theorem mem_signedLevelParam_node_iff (j : Fin 4) (u : Fin 4 → Fˣ) :
    u ∈ signedLevelParam (K := F) (plusNodeSet 4 j) (plusNodeFlip 4 j) ↔ nodeChar j u = 1 := by
  fin_cases j
  · exact mem_signedLevelParam_node_zero u
  · exact mem_signedLevelParam_node_one u
  · exact mem_signedLevelParam_node_two u
  · exact mem_signedLevelParam_node_three u

theorem mem_nodeTorus_iff (j : Fin 4) (y : matrixProjectiveDerived (coordinateQuadPlus 4 F)) :
    y ∈ plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j) ↔
      ∃ u, y = (isHypFrame_plus F 4).frameHom u ∧ nodeChar j u = 1 := by
  rw [plusSignedLevelTorus, plusFrameTorus, (isHypFrame_plus F 4).frameTorusOf_eq_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rfl, (mem_signedLevelParam_node_iff j u).1 hu⟩
  · rintro ⟨u, rfl, hu⟩
    exact ⟨u, (mem_signedLevelParam_node_iff j u).2 hu, rfl⟩

theorem frameHom_commute_x_iff (j : Fin 4) (u : Fin 4 → Fˣ) :
    Commute ((isHypFrame_plus F 4).frameHom u)
        (spin8Equiv F (SpinPlus.x 4 F d4_three_le (Pi.single j 1) 1)) ↔ nodeChar j u = 1 := by
  have hconj := frameHom_conj_spin8Equiv_x (rootIdxD_ne 4 (by norm_num) j)
    (SpinPlus.toStdD_single (by norm_num) j) u (1 : F)
  rw [mul_one] at hconj
  have hroot := (SpinPlus.Φ 4 F d4_three_le).single_mem j
  constructor
  · intro h
    have h' : (isHypFrame_plus F 4).frameHom u *
        spin8Equiv F (SpinPlus.x 4 F d4_three_le (Pi.single j 1) 1) *
        ((isHypFrame_plus F 4).frameHom u)⁻¹ =
          spin8Equiv F (SpinPlus.x 4 F d4_three_le (Pi.single j 1) 1) := by
      rw [h.eq, mul_inv_cancel_right]
    rw [hconj] at h'
    exact Units.ext ((SpinPlus.isParametrization d4_three_le _ hroot).2.2
      ((spin8Equiv F).injective h'))
  · intro h
    have h1 : ((u (rootIdxD 4 j) ^ boolSign true * u (rootIdxD' 4 j) ^ boolSign (rootSignD 4 j) :
        Fˣ) : F) = 1 := by
      rw [← Units.val_one]
      exact congrArg Units.val h
    rw [h1] at hconj
    exact (mul_inv_eq_iff_eq_mul.1 hconj)

theorem plusFourTriality_spin8Equiv (g : spinGroup (quadPlus 4 F)) :
    plusFourTriality F (spin8Equiv F g) = spin8Equiv F (spinGraphAut d4TrialitySym g) := by
  rw [plusFourTriality, plusFourGraphAut_apply, MulEquiv.symm_apply_apply]

theorem exists_plusFourTriality_frameHom (u : Fin 4 → Fˣ) :
    ∃ u', plusFourTriality F ((isHypFrame_plus F 4).frameHom u) =
      (isHypFrame_plus F 4).frameHom u' := by
  obtain ⟨s₀, s₁, s₂, s₃, rfl⟩ := eq_prod_corParam u
  refine ⟨corParam (d4TrialityPerm 0) s₀ * corParam (d4TrialityPerm 1) s₁ *
    corParam (d4TrialityPerm 2) s₂ * corParam (d4TrialityPerm 3) s₃, ?_⟩
  simp only [map_mul, ← spin8Equiv_torusD, plusFourTriality_spin8Equiv, spinGraphAut_torusD]
  rfl

theorem plusFourTriality_mem_nodeTorus {j : Fin 4}
    {y : matrixProjectiveDerived (coordinateQuadPlus 4 F)}
    (hy : y ∈ plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j)) :
    plusFourTriality F y ∈
      plusSignedLevelTorus F (plusNodeSet 4 (d4TrialityPerm j))
        (plusNodeFlip 4 (d4TrialityPerm j)) := by
  obtain ⟨u, rfl, hu⟩ := (mem_nodeTorus_iff j y).1 hy
  obtain ⟨u', hu'⟩ := exists_plusFourTriality_frameHom (F := F) u
  have hroot := (SpinPlus.Φ 4 F d4_three_le).single_mem j
  have hc := ((frameHom_commute_x_iff j u).2 hu).map (plusFourTriality F).toMonoidHom
  change Commute (plusFourTriality F ((isHypFrame_plus F 4).frameHom u))
    (plusFourTriality F (spin8Equiv F (SpinPlus.x 4 F d4_three_le (Pi.single j 1) 1))) at hc
  rw [hu', plusFourTriality_x hroot, fundPerm_single] at hc
  exact (mem_nodeTorus_iff _ _).2 ⟨u', hu', (frameHom_commute_x_iff _ u').1 hc⟩

theorem d4TrialityPerm_apply_three_times (j : Fin 4) :
    d4TrialityPerm (d4TrialityPerm (d4TrialityPerm j)) = j := by
  revert j
  decide

theorem plusFourTriality_apply_three_times (y : matrixProjectiveDerived (coordinateQuadPlus 4 F)) :
    plusFourTriality F (plusFourTriality F (plusFourTriality F y)) = y := by
  have h := congrArg (fun α : MulAut (matrixProjectiveDerived (coordinateQuadPlus 4 F)) => α y)
    (plusFourTriality_pow_three (F := F))
  simpa [pow_succ, MulAut.mul_apply] using h

theorem map_plusFourTriality_nodeTorus (j : Fin 4) :
    (plusSignedLevelTorus F (plusNodeSet 4 j) (plusNodeFlip 4 j)).map
        (plusFourTriality F).toMonoidHom =
      plusSignedLevelTorus F (plusNodeSet 4 (d4TrialityPerm j))
        (plusNodeFlip 4 (d4TrialityPerm j)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact plusFourTriality_mem_nodeTorus hz
  · intro hy
    have h1 := plusFourTriality_mem_nodeTorus hy
    have h2 := plusFourTriality_mem_nodeTorus h1
    rw [d4TrialityPerm_apply_three_times] at h2
    exact ⟨_, h2, plusFourTriality_apply_three_times y⟩

theorem permutesNodeTori_plusFourTriality : PermutesNodeTori (plusFourTriality F) :=
  permutesNodeTori_of_map_eq fun j => ⟨d4TrialityPerm j, map_plusFourTriality_nodeTorus j⟩

end Nodes

end CFSG.SeitzReduction.OmegaPilot
