module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitaryEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogEdge

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (gramSUToSL coe_gramSUToSL gramSUToSL_injective)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer (descendMatrix
  descendMatrix_map fixedField_finite)
open scoped MatrixGroups

section Block

variable {K' : Type} [Field K'] {f : ℕ} (h : UnitaryFieldData 2 f K')

theorem bar_eq_of_unitary_antidiag {a b c d : K'} (h1 : h.bar a * c + h.bar c * a = 0)
    (h2 : h.bar a * d + h.bar c * b = 1) (h3 : h.bar b * c + h.bar d * a = 1)
    (h4 : h.bar b * d + h.bar d * b = 0) (h5 : a * d - b * c = 1) :
    h.bar a = a ∧ h.bar b = b ∧ h.bar c = c ∧ h.bar d = d := by
  have := h.charP
  have h2two : (2 : K') = 0 := CharTwo.two_eq_zero
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-(h.bar a)) * h5 + a * h2 - b * h1
  · linear_combination (-(h.bar b)) * h5 + a * h4 - b * h3 - b * h2two
  · linear_combination (-(h.bar c)) * h5 + d * h1 - c * h2 - c * h2two
  · linear_combination (-(h.bar d)) * h5 + d * h3 - c * h4

theorem map_bar_eq_of_mem_offPlane {g : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'}
    (hu : (g.map h.bar)ᵀ * blockSwapJ (2 * 2) 2 * g = blockSwapJ (2 * 2) 2) (hdet : g.det = 1)
    (hblk : ∀ i j, (i ∉ offPlaneSL 0 ∨ j ∉ offPlaneSL 0) → g i j = (1 : Matrix _ _ K') i j) :
    g.map h.bar = g := by
  have hg : g = !![1, 0, 0, 0; 0, g 1 1, 0, g 1 3; 0, 0, 1, 0; 0, g 3 1, 0, g 3 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hblk, offPlaneSL]
  set a := g 1 1
  set b := g 1 3
  set c := g 3 1
  set d := g 3 3
  rw [hg] at hu hdet
  have h5 : a * d - b * c = 1 := by
    rw [← hdet]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    ring
  have e11 := congrFun (congrFun hu 1) 1
  have e13 := congrFun (congrFun hu 1) 3
  have e31 := congrFun (congrFun hu 3) 1
  have e33 := congrFun (congrFun hu 3) 3
  simp [Matrix.mul_apply, Fin.sum_univ_four, blockSwapJ] at e11 e13 e31 e33
  obtain ⟨ha, hb, hc, hd⟩ := bar_eq_of_unitary_antidiag h (by linear_combination e11)
    (by linear_combination e13) (by linear_combination e31) (by linear_combination e33) h5
  rw [hg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

end Block

section Descend

variable {K' : Type} [Field K'] {f : ℕ} (h : UnitaryFieldData 2 f K') {n : ℕ}

theorem exists_map_subtype_eq_of_map_bar_eq (g : SpecialLinearGroup (Fin n) K')
    (hg : (g : Matrix (Fin n) (Fin n) K').map h.bar = g) :
    ∃ y : SpecialLinearGroup (Fin n) h.fixedField,
      SpecialLinearGroup.map h.fixedField.subtype y = g ∧
      (y : Matrix (Fin n) (Fin n) h.fixedField) = descendMatrix h _ hg := by
  have hdet : (descendMatrix h _ hg).det = 1 := by
    apply Subtype.val_injective
    have h1 := RingHom.map_det h.fixedField.subtype (descendMatrix h _ hg)
    rw [RingHom.mapMatrix_apply, descendMatrix_map] at h1
    rw [Subfield.coe_one]
    exact h1.trans g.2
  refine ⟨⟨_, hdet⟩, ?_, rfl⟩
  apply Subtype.ext
  exact descendMatrix_map h _ hg

end Descend

section Tori

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

@[expose] noncomputable def uStdTorus :
    Subgroup (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) :=
  (rootTorusSp h.fixedField 0).map (uModelSU h hC₀)

@[expose] noncomputable def uTwTorus :
    Subgroup (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) :=
  ((rootTorusSp h.fixedField 0).map tauSp).map (uModelSU h hC₀)

theorem coe_uModelSU_rootTorusHom_zero (κ : h.fixedFieldˣ) :
    (((uModelSU h hC₀ (rootTorusHom h.fixedField 2 0 κ) :
        gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) : GL (Fin (2 * 2)) K') :
          Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
      diagonal ![((κ : h.fixedField) : K'), 1, (((κ⁻¹ : h.fixedFieldˣ) : h.fixedField) : K'),
        1] := by
  rw [coe_uModelSU, coe_spModelSL_rootTorusHom_eq, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [offPlaneSL]

theorem coe_uModelSU_tauSp_rootTorusHom_zero (κ : h.fixedFieldˣ) :
    (((uModelSU h hC₀ (tauSp (rootTorusHom h.fixedField 2 0 κ)) :
        gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) : GL (Fin (2 * 2)) K') :
          Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
      diagonal ![((κ : h.fixedField) : K'), ((κ : h.fixedField) : K'),
        (((κ⁻¹ : h.fixedFieldˣ) : h.fixedField) : K'),
        (((κ⁻¹ : h.fixedFieldˣ) : h.fixedField) : K')] := by
  rw [coe_uModelSU, coe_spModelSL_tauSp_rootTorusHom, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [twBlockSL]

end Tori

section Std

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

theorem natCard_fixedField_le (h : UnitaryFieldData 2 f K') :
    Nat.card h.fixedField ≤ Nat.card K' := by
  rw [h.card, h.card_fixedField]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem map_perfectCore_centralizer_uStdTorus_le (hk : 4 ≤ Nat.card h.fixedField) :
    (perfectCore (centralizer (uStdTorus h hC₀ :
        Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'))))).map
        (gramSUToSL h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) ≤
      blockSpecialLinear (K := K') (offPlaneSL 0) := by
  have : Finite K' := h.finite
  have : Finite h.fixedField := fixedField_finite h
  have hK' : 4 ≤ Nat.card K' := hk.trans (natCard_fixedField_le h)
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one_of_four_le hk
  have hne := coe_units_ne_inv_of_ne_one hκ₀
  have e1 : ((κ₀ : h.fixedField) : K') ≠ 1 := fun e => hκ₀ (Units.ext (Subtype.ext e))
  have e2 : (((κ₀⁻¹ : h.fixedFieldˣ) : h.fixedField) : K') ≠ 1 := fun e =>
    hκ₀ (inv_eq_one.1 (Units.ext (Subtype.ext e)))
  have e3 : ((κ₀ : h.fixedField) : K') ≠ (((κ₀⁻¹ : h.fixedFieldˣ) : h.fixedField) : K') :=
    fun e => hne (Subtype.ext e)
  have e4 : ((κ₀ : h.fixedField) : K') ≠ ((κ₀ : h.fixedField) : K')⁻¹ := by simpa using e3
  set ρ := gramSUToSL h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')
  refine (map_perfectCore_centralizer_le ρ _).trans ?_
  have hLevi := LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear (F := K')
    (N := Finset.univ) (I := offPlaneSL 0) (Finset.subset_univ _)
    (((uStdTorus h hC₀).map ρ : Subgroup (SpecialLinearGroup (Fin (2 * 2)) K')) :
      Set (SpecialLinearGroup (Fin (2 * 2)) K')) ?_ ?_ ?_
    (LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (card_offPlaneSL 0).ge hK')
  · rw [LinearPilot.blockSpecialLinear_univ, top_inf_eq] at hLevi
    exact hLevi.le
  · rintro d ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, rfl⟩ i j hij
    rw [coe_gramSUToSL, coe_uModelSU_rootTorusHom_zero, diagonal_apply_ne _ hij]
  · rintro d ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, rfl⟩ i hi j hj
    rw [coe_gramSUToSL, coe_uModelSU_rootTorusHom_zero, diagonal_apply_eq, diagonal_apply_eq]
    simp only [offPlaneSL, ite_true, Finset.mem_insert, Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rfl
  · intro i _ j _ hij hIJ
    refine ⟨_, ⟨_, ⟨_, ⟨κ₀, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    rw [coe_gramSUToSL, coe_uModelSU_rootTorusHom_zero, diagonal_apply_eq, diagonal_apply_eq]
    fin_cases i <;> fin_cases j <;> simp [offPlaneSL] at hij hIJ ⊢ <;>
      first | exact hκ₀ | exact e1 | exact e1.symm | exact e2 | exact e2.symm | exact e3 |
        exact e3.symm | exact e4 | exact e4.symm

omit [CharP h.fixedField 2] in
theorem specialLinearGroup_map_subtype_injective {n : ℕ} :
    Function.Injective (SpecialLinearGroup.map (n := Fin n) h.fixedField.subtype) := by
  intro x y hxy
  apply Subtype.ext
  exact Matrix.map_injective Subtype.val_injective
    (congrArg (fun z : SpecialLinearGroup (Fin n) K' => (z : Matrix (Fin n) (Fin n) K')) hxy)

theorem natCard_perfectCore_centralizer_uStdTorus_dvd (hk : 4 ≤ Nat.card h.fixedField) :
    Nat.card (perfectCore (centralizer (uStdTorus h hC₀ :
        Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'))))) ∣
      Nat.card (SpecialLinearGroup (Fin 2) h.fixedField) := by
  have : Finite K' := h.finite
  set C := perfectCore (centralizer (uStdTorus h hC₀ :
    Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'))))
  set ρ := gramSUToSL h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')
  set H : Subgroup (SpecialLinearGroup (Fin (2 * 2)) K') :=
    (blockSpecialLinear (K := h.fixedField) (offPlaneSL 0)).map
      (SpecialLinearGroup.map h.fixedField.subtype)
  have hle : C.map ρ ≤ H := by
    rintro _ ⟨g, hg, rfl⟩
    have hblk := map_perfectCore_centralizer_uStdTorus_le h hC₀ hk ⟨g, hg, rfl⟩
    obtain ⟨hu, hdet⟩ := mem_gramSU.1 g.2
    have hu' : (((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K').map h.bar)ᵀ *
        blockSwapJ (2 * 2) 2 * ((g : GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
          blockSwapJ (2 * 2) 2 := by
      rw [← hC₀]
      exact hu
    have hfix := map_bar_eq_of_mem_offPlane h hu' hdet
      (fun i j hij => mem_blockSpecialLinear.1 hblk i j hij)
    obtain ⟨y, hy, hyd⟩ := exists_map_subtype_eq_of_map_bar_eq h (ρ g) hfix
    refine ⟨y, ?_, hy⟩
    rw [SetLike.mem_coe, mem_blockSpecialLinear]
    intro i j hij
    apply Subtype.ext
    rw [hyd]
    have := mem_blockSpecialLinear.1 hblk i j hij
    simp only [descendMatrix, Matrix.of_apply]
    rw [this]
    by_cases hij' : i = j
    · subst hij'
      simp
    · simp [Matrix.one_apply_ne hij']
  have h1 : Nat.card C = Nat.card (C.map ρ) :=
    (Subgroup.card_map_of_injective (gramSUToSL_injective h _)).symm
  have h2 : Nat.card H = Nat.card (blockSpecialLinear (K := h.fixedField) (offPlaneSL 0)) :=
    Subgroup.card_map_of_injective (specialLinearGroup_map_subtype_injective h)
  rw [h1, ← natCard_blockSpecialLinear_of_card_two (card_offPlaneSL 0), ← h2]
  exact Subgroup.card_dvd_of_le hle

end Std

section Tw

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

omit [CharP h.fixedField 2] in
theorem blockSwapJ_eq_reindex_hypGram2 :
    (blockSwapJ (2 * 2) 2 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') =
      (CFSG.RankThree.Classical.hypGram2 2 K').reindex (spModelIdx 2) (spModelIdx 2) := by
  ext i j
  obtain ⟨u, rfl⟩ := (spModelIdx 2).surjective i
  obtain ⟨v, rfl⟩ := (spModelIdx 2).surjective j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases u with a | a <;> rcases v with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [blockSwapJ, CFSG.RankThree.Classical.hypGram2] <;> decide

@[expose] noncomputable def lambdaUMat :
    SpecialLinearGroup (Fin 2) K' →* Matrix (Fin (2 * 2)) (Fin (2 * 2)) K' :=
  (Matrix.reindexAlgEquiv K' K' (spModelIdx 2)).toRingEquiv.toMonoidHom.comp
    (CFSG.RankThree.CentralLift.leviUMat h 2)

omit [CharP h.fixedField 2] in
theorem lambdaUMat_apply (A : SpecialLinearGroup (Fin 2) K') :
    lambdaUMat h A =
      (CFSG.RankThree.CentralLift.leviUMat h 2 A).reindex (spModelIdx 2) (spModelIdx 2) :=
  rfl

omit [CharP h.fixedField 2] in
include hC₀ in
theorem lambdaUMat_mem (A : SpecialLinearGroup (Fin 2) K') :
    ((lambdaUMat h A).map h.bar)ᵀ * (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') *
        lambdaUMat h A = (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') ∧
      (lambdaUMat h A).det = 1 := by
  obtain ⟨h1, h2⟩ := CFSG.RankThree.CentralLift.leviUMat_mem h A
  rw [hC₀, blockSwapJ_eq_reindex_hypGram2, lambdaUMat_apply]
  refine ⟨?_, ?_⟩
  · rw [Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map,
      Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h1]
  · rw [Matrix.det_reindex_self, h2]

@[expose] noncomputable def lambdaU :
    SpecialLinearGroup (Fin 2) K' →* gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') :=
  (lambdaUMat h).toHomUnits.codRestrict _ fun A => mem_gramSU.2 (lambdaUMat_mem h hC₀ A)

omit [CharP h.fixedField 2] in
theorem coe_lambdaU (A : SpecialLinearGroup (Fin 2) K') :
    (((lambdaU h hC₀ A : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) :
      GL (Fin (2 * 2)) K') : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = lambdaUMat h A :=
  rfl

omit [CharP h.fixedField 2] in
theorem lambdaU_injective : Function.Injective (lambdaU h hC₀) := by
  intro A B hAB
  have h1 : lambdaUMat h A = lambdaUMat h B := by
    rw [← coe_lambdaU h hC₀, ← coe_lambdaU h hC₀, hAB]
  rw [lambdaUMat_apply, lambdaUMat_apply] at h1
  have h2 := congrArg Matrix.toBlocks₁₁
    ((Matrix.reindex (spModelIdx 2) (spModelIdx 2)).injective h1)
  rw [CFSG.RankThree.CentralLift.leviUMat_apply, CFSG.RankThree.CentralLift.leviUMat_apply,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₁] at h2
  exact Subtype.ext h2

theorem lambdaU_mem_centralizer_uTwTorus (A : SpecialLinearGroup (Fin 2) K') :
    lambdaU h hC₀ A ∈ centralizer (uTwTorus h hC₀ :
      Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'))) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨_, ⟨_, ⟨κ, rfl⟩, rfl⟩, rfl⟩
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lambdaU,
    coe_uModelSU_tauSp_rootTorusHom_zero]
  set μ : K' := ((κ : h.fixedField) : K')
  set ν : K' := (((κ⁻¹ : h.fixedFieldˣ) : h.fixedField) : K')
  have hv : ∀ a : Fin 2, (![μ, μ, ν, ν] : Fin (2 * 2) → K') (spModelIdx 2 (Sum.inl a)) = μ := by
    intro a
    fin_cases a <;> rfl
  have hv' : ∀ a : Fin 2, (![μ, μ, ν, ν] : Fin (2 * 2) → K') (spModelIdx 2 (Sum.inr a)) = ν := by
    intro a
    fin_cases a <;> rfl
  ext i j
  rw [mul_diagonal, diagonal_mul]
  obtain ⟨u, rfl⟩ := (spModelIdx 2).surjective i
  obtain ⟨w, rfl⟩ := (spModelIdx 2).surjective j
  rw [lambdaUMat_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, CFSG.RankThree.CentralLift.leviUMat_apply]
  rcases u with a | a <;> rcases w with b | b
  · rw [fromBlocks_apply₁₁, hv, hv, mul_comm]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, mul_zero]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, zero_mul, mul_zero]
  · rw [fromBlocks_apply₂₂, hv', hv', mul_comm]

omit [CharP h.fixedField 2] in
theorem commutator_range_lambdaU (hK' : 4 ≤ Nat.card K') :
    ⁅(lambdaU h hC₀).range, (lambdaU h hC₀).range⁆ = (lambdaU h hC₀).range := by
  have : Finite K' := h.finite
  have htop : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 2) K')),
      (⊤ : Subgroup (SpecialLinearGroup (Fin 2) K'))⁆ = ⊤ := by
    have h1 := LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (F := K') (n := 2)
      (I := Finset.univ) (by simp) hK'
    rwa [LinearPilot.blockSpecialLinear_univ] at h1
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, htop]

theorem range_lambdaU_le_perfectCore_centralizer_uTwTorus (hK' : 4 ≤ Nat.card K') :
    (lambdaU h hC₀).range ≤ perfectCore (centralizer (uTwTorus h hC₀ :
      Set (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')))) := by
  refine le_perfectCore_of_perfect ?_ (commutator_range_lambdaU h hC₀ hK')
  rintro _ ⟨A, rfl⟩
  exact lambdaU_mem_centralizer_uTwTorus h hC₀ A

end Tw

section Centre

variable {F : Type} [Field F] [CharP F 2]

theorem center_SL_two_eq_bot_of_charTwo :
    center (SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have h0 : (r - 1) ^ 2 = 0 := by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination hr2 + (1 - r) * h2
  have hr1 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h0)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1, map_one]
  rfl

end Centre

section Card

variable {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') [CharP h.fixedField 2]
  {C₀ : GL (Fin (2 * 2)) K'}
  (hC₀ : (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') = blockSwapJ (2 * 2) 2)

omit [CharP h.fixedField 2] in
theorem natCard_map_range_lambdaU {E : Type*} [Group E]
    (Φ : gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K') →* E)
    (hker : Φ.ker ≤ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K'))) :
    Nat.card ((lambdaU h hC₀).range.map Φ) = Nat.card (SpecialLinearGroup (Fin 2) K') := by
  have := h.charP
  have hinj : Function.Injective (Φ.comp (lambdaU h hC₀)) := by
    rw [injective_iff_map_eq_one]
    intro A hA
    have hc : lambdaU h hC₀ A ∈ center (gramSU h (C₀ : Matrix (Fin (2 * 2)) (Fin (2 * 2)) K')) :=
      hker hA
    have hAc : A ∈ center (SpecialLinearGroup (Fin 2) K') := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply lambdaU_injective h hC₀
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 hc (lambdaU h hC₀ B)
    rw [center_SL_two_eq_bot_of_charTwo] at hAc
    exact hAc
  rw [MonoidHom.range_eq_map, Subgroup.map_map, ← MonoidHom.range_eq_map]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Card

end CFSG.SeitzReduction.SymplecticPilot
