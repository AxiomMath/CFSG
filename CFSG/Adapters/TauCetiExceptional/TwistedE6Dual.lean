module

public import CFSG.Adapters.TauCetiExceptional.TwistedE6Upper
public import CFSG.Adapters.TauCetiExceptional.MinusculeCore
public import CFSG.LieType.Chevalley.IntrinsicDiagramPermutation

public noncomputable section

namespace CFSG.TauCetiBridge.Twisted

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
  TauCeti.DynkinType TauCeti.E6DoubledMinuscule
open CFSG.TauCetiBridge.Minuscule
open scoped Matrix

theorem e6Data_wt_ne_single_five :
    ∀ b : Fin 27, (fun i : Fin 6 => e6Data.wt (b : ℕ) i) ≠ Pi.single 5 1 := by
  decide +kernel

theorem e6Match_node
    (i : Fin 6) : e6Match.node i = i := by
  have hc : ∀ i j, Tag.cartanE 6 (e6Match.node i) (e6Match.node j) = Tag.cartanE 6 i j := by
    intro i j
    have h1 := e6Match.cartan i j
    have h2 := e6_cartan i j
    exact h1.symm.trans h2
  rcases perm_cases_of_cartanE6 e6Match.node hc with h | h
  · rw [h]
    rfl
  · exfalso
    apply e6Data_wt_ne_single_five (e6Match.lab 0)
    funext j
    obtain ⟨j, rfl⟩ := e6Match.node.surjective j
    have hw := e6Match.wt_lab 0 j
    rw [E6Minuscule.weightTable_weight, e6MinusculeWeight_zero] at hw
    rw [hw, h]
    clear hw
    revert j
    decide

section Field

variable (L : Type) [Field L]

theorem points_isBlockDiag (z : ↥(points L)) :
    IsBlockDiag e6Blk L ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) :=
  e6d_points_isBlockDiag L _ z.2

@[expose] def ulHom : ↥(points L) →* Matrix.GeneralLinearGroup (Fin 27) L where
  toFun z :=
    { val := ulBlock ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)
      inv := ulBlock (((z⁻¹ : ↥(points L)) : Matrix.GeneralLinearGroup (Fin 54) L) :
        Matrix (Fin 54) (Fin 54) L)
      val_inv := by
        rw [← ulBlock_mul (points_isBlockDiag L z), ← Units.val_mul, ← Subgroup.coe_mul,
          mul_inv_cancel, Subgroup.coe_one, Units.val_one, ulBlock_one]
      inv_val := by
        rw [← ulBlock_mul (points_isBlockDiag L z⁻¹), ← Units.val_mul, ← Subgroup.coe_mul,
          inv_mul_cancel, Subgroup.coe_one, Units.val_one, ulBlock_one] }
  map_one' := Units.ext ulBlock_one
  map_mul' x y := Units.ext (ulBlock_mul (points_isBlockDiag L x))

theorem coe_ulHom (z : ↥(points L)) :
    ((ulHom L z : Matrix.GeneralLinearGroup (Fin 27) L) : Matrix (Fin 27) (Fin 27) L) =
      ulBlock ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) :=
  rfl

theorem raisingMatrix_eq_weightTable (i : Fin 6) :
    E6Minuscule.raisingMatrix i = E6Minuscule.weightTable.raisingMatrix i := by
  ext a b
  rw [E6Minuscule.raisingMatrix_apply, MinusculeWeightTable.raisingMatrix_apply,
    E6Minuscule.weightTable_weight, E6Minuscule.weightTable_reflection]

theorem loweringMatrix_eq_weightTable (i : Fin 6) :
    E6Minuscule.loweringMatrix i = E6Minuscule.weightTable.loweringMatrix i := by
  ext a b
  rw [E6Minuscule.loweringMatrix_apply, MinusculeWeightTable.loweringMatrix_apply,
    E6Minuscule.weightTable_weight, E6Minuscule.weightTable_reflection]

theorem ulHom_rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (u : Multiplicative L) :
    (ulHom L (rootSubgroupPoints k L u) : Matrix.GeneralLinearGroup (Fin 27) L) =
      (E6Minuscule.rootSubgroupPoints k L u : Matrix.GeneralLinearGroup (Fin 27) L) := by
  refine Units.ext ?_
  rw [coe_ulHom, coe_rootSubgroupPoints_eq_one_add_smul, ulBlock_add, ulBlock_one,
    ulBlock_smul, ulBlock_map]
  rcases k with i | i
  · rw [ulBlock_rootIntMatrix_inl, E6Minuscule.coe_rootSubgroupPoints_inl,
      raisingMatrix_eq_weightTable]
  · rw [ulBlock_rootIntMatrix_inr, E6Minuscule.coe_rootSubgroupPoints_inr,
      loweringMatrix_eq_weightTable]

abbrev ulRange : Subgroup (Matrix.GeneralLinearGroup (Fin 27) L) := (ulHom L).range

theorem elementarySubgroup_le_ulRange :
    E6Minuscule.elementarySubgroup L ≤ (ulRange L).comap (E6Minuscule.points L).subtype := by
  rw [E6Minuscule.elementarySubgroup_le_iff]
  intro k u
  exact ⟨rootSubgroupPoints k L u, ulHom_rootSubgroupPoints L k u⟩

theorem toMat_mem_ulRange
    (g : e6Data_valid.minGroup L) :
    toMat e6Match.lab L g ∈ ulRange L := by
  have h : toMat e6Match.lab L g ∈
      (E6Minuscule.elementarySubgroup L).map (E6Minuscule.points L).subtype := by
    rw [← map_toMat_e6_minGroup]
    exact ⟨g, g.2, rfl⟩
  obtain ⟨x, hx, hxg⟩ := h
  rw [← hxg]
  exact elementarySubgroup_le_ulRange L hx

end Field

theorem elementarySubgroup_le_comap_ulHom :
    elementarySubgroup ℚ ≤ ((E6Minuscule.elementarySubgroup ℚ).map
      (E6Minuscule.points ℚ).subtype).comap (ulHom ℚ) := by
  rw [elementarySubgroup_le_iff]
  intro k u
  refine ⟨E6Minuscule.rootSubgroupPoints k ℚ u,
    E6Minuscule.rootSubgroupPoints_mem_elementarySubgroup ℚ k u, ?_⟩
  exact (ulHom_rootSubgroupPoints ℚ k u).symm

theorem ulRange_isZero
    (L : Type) [Field L] {z : Matrix.GeneralLinearGroup (Fin 27) L}
    (hz : z ∈ ulRange L) (P : MvPolynomial (Fin 27 × Fin 27) ℤ)
    (hP : ∀ g : e6Data_valid.minGroup ℚ,
      BigCell.evalMat ((toMat e6Match.lab ℚ g : Matrix.GeneralLinearGroup (Fin 27) ℚ) :
        Matrix (Fin 27) (Fin 27) ℚ) P = 0) :
    BigCell.evalMat (z : Matrix (Fin 27) (Fin 27) L) P = 0 := by
  obtain ⟨w, rfl⟩ := hz
  set f : Fin 27 × Fin 27 → Fin 54 × Fin 54 :=
    fun ab => (matrixIndexEquiv (.inl ab.1), matrixIndexEquiv (.inl ab.2))
  have key : ∀ (A : Type) [CommRing A] (M : Matrix (Fin 54) (Fin 54) A),
      BigCell.evalMat M (MvPolynomial.rename f P) = BigCell.evalMat (ulBlock M) P := by
    intro A _ M
    rw [evalMat_rename]
    rfl
  rw [coe_ulHom, ← key]
  refine e6d_evalMat_eq_zero _ (fun g' hg' => ?_) L _ w.2
  rw [key]
  obtain ⟨x, hx, hxg⟩ := elementarySubgroup_le_comap_ulHom hg'
  have h1 : ulBlock (((g' : ↥(points ℚ)) : Matrix.GeneralLinearGroup (Fin 54) ℚ) :
      Matrix (Fin 54) (Fin 54) ℚ) =
      (((E6Minuscule.points ℚ).subtype x : Matrix.GeneralLinearGroup (Fin 27) ℚ) :
        Matrix (Fin 27) (Fin 27) ℚ) := by
    rw [← coe_ulHom, ← hxg]
  rw [h1]
  have h2 : (E6Minuscule.points ℚ).subtype x ∈
      (e6Data_valid.minGroup ℚ).map (toMat e6Match.lab ℚ).toMonoidHom := by
    rw [map_toMat_e6_minGroup]
    exact ⟨x, hx, rfl⟩
  obtain ⟨g0, hg0, hg0x⟩ := h2
  rw [← hg0x]
  exact hP ⟨g0, hg0⟩

theorem isBlockDiag_e6E (L : Type) [Field L] (i : Fin 6) : IsBlockDiag e6Blk L (e6E L i) :=
  fun a b hab => by rw [e6E, Matrix.map_apply, rootIntMatrix_isBlockDiag _ a b hab, Int.cast_zero]

theorem isBlockDiag_e6F (L : Type) [Field L] (i : Fin 6) : IsBlockDiag e6Blk L (e6F L i) :=
  fun a b hab => by rw [e6F, Matrix.map_apply, rootIntMatrix_isBlockDiag _ a b hab, Int.cast_zero]

theorem eq_of_blocks {L : Type} [Field L] {M N : Matrix (Fin 54) (Fin 54) L}
    (hM : IsBlockDiag e6Blk L M) (hN : IsBlockDiag e6Blk L N) (hu : ulBlock M = ulBlock N)
    (hl : lrBlock M = lrBlock N) : M = N := by
  ext a b
  obtain ⟨x, rfl⟩ := matrixIndexEquiv.surjective a
  obtain ⟨y, rfl⟩ := matrixIndexEquiv.surjective b
  rcases x with x | x <;> rcases y with y | y
  · exact congrFun (congrFun hu x) y
  · rw [hM _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide),
      hN _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide)]
  · rw [hM _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide),
      hN _ _ (by rw [e6Blk_inl, e6Blk_inr]; decide)]
  · exact congrFun (congrFun hl x) y

theorem commute_inv_of_commute {n : ℕ} {L : Type} [Field L] {W W' X : Matrix (Fin n) (Fin n) L}
    (h1 : W * W' = 1) (h2 : W' * W = 1) (h : W * X = X * W) : W' * X = X * W' := by
  calc W' * X = W' * X * (W * W') := by rw [h1, Matrix.mul_one]
    _ = W' * (X * W) * W' := by simp only [Matrix.mul_assoc]
    _ = W' * (W * X) * W' := by rw [h]
    _ = X * W' := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem ulBlock_e6E (L : Type) [Field L] (i : Fin 6) :
    ulBlock (e6E L i) = (E6Minuscule.raisingMatrix i).map (Int.cast : ℤ → L) := by
  rw [e6E, ulBlock_map, ulBlock_rootIntMatrix_inl]

theorem ulBlock_e6F (L : Type) [Field L] (i : Fin 6) :
    ulBlock (e6F L i) = (E6Minuscule.loweringMatrix i).map (Int.cast : ℤ → L) := by
  rw [e6F, ulBlock_map, ulBlock_rootIntMatrix_inr]

theorem lrBlock_e6E (L : Type) [Field L] (i : Fin 6) :
    lrBlock (e6E L i) = -((E6Minuscule.raisingMatrix i).map (Int.cast : ℤ → L))ᵀ := by
  rw [e6E, lrBlock_map, lrBlock_rootIntMatrix_inl, loweringMatrix_eq_transpose,
    Matrix.map_neg _ (fun x => Int.cast_neg x), Matrix.transpose_map]

theorem lrBlock_e6F (L : Type) [Field L] (i : Fin 6) :
    lrBlock (e6F L i) = -((E6Minuscule.loweringMatrix i).map (Int.cast : ℤ → L))ᵀ := by
  rw [e6F, lrBlock_map, lrBlock_rootIntMatrix_inr, loweringMatrix_eq_transpose,
    Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_neg _ (fun x => Int.cast_neg x)]

theorem transpose_commute {n : ℕ} {L : Type} [Field L] {W' X : Matrix (Fin n) (Fin n) L}
    (h : W' * X = X * W') : W'ᵀ * -Xᵀ = -Xᵀ * W'ᵀ := by
  rw [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, h]

theorem commute_iff_ulBlock (L : Type) [Field L] (z : ↥(points L)) :
    (∀ i, ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6E L i =
        e6E L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) ∧
      ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) * e6F L i =
        e6F L i * ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L)) ↔
    ∀ i, ulBlock ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) *
          (E6Minuscule.raisingMatrix i).map (Int.cast : ℤ → L) =
        (E6Minuscule.raisingMatrix i).map (Int.cast : ℤ → L) *
          ulBlock ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) ∧
      ulBlock ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) *
          (E6Minuscule.loweringMatrix i).map (Int.cast : ℤ → L) =
        (E6Minuscule.loweringMatrix i).map (Int.cast : ℤ → L) *
          ulBlock ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) := by
  set Z := ((z : Matrix.GeneralLinearGroup (Fin 54) L) : Matrix (Fin 54) (Fin 54) L) with hZ
  have hZd : IsBlockDiag e6Blk L Z := points_isBlockDiag L z
  constructor
  · intro h i
    obtain ⟨hE, hF⟩ := h i
    have e1 := congrArg ulBlock hE
    have e2 := congrArg ulBlock hF
    rw [ulBlock_mul hZd, ulBlock_mul (isBlockDiag_e6E L i), ulBlock_e6E] at e1
    rw [ulBlock_mul hZd, ulBlock_mul (isBlockDiag_e6F L i), ulBlock_e6F] at e2
    exact ⟨e1, e2⟩
  · intro h i
    set W' := ulBlock (((z⁻¹ : ↥(points L)) : Matrix.GeneralLinearGroup (Fin 54) L) :
      Matrix (Fin 54) (Fin 54) L) with hW'
    have h1 : ulBlock Z * W' = 1 := (ulHom L z).val_inv
    have h2 : W' * ulBlock Z = 1 := (ulHom L z).inv_val
    have hlr : lrBlock Z = W'ᵀ := by
      have hid := lrBlock_transpose_mul_ulBlock (z : Matrix.GeneralLinearGroup (Fin 54) L) z.2
      rw [← hZ] at hid
      have : (lrBlock Z)ᵀ = W' := by
        calc (lrBlock Z)ᵀ = (lrBlock Z)ᵀ * (ulBlock Z * W') := by rw [h1, Matrix.mul_one]
          _ = W' := by rw [← Matrix.mul_assoc, hid, Matrix.one_mul]
      rw [← this, Matrix.transpose_transpose]
    have hE' := commute_inv_of_commute h1 h2 (h i).1
    have hF' := commute_inv_of_commute h1 h2 (h i).2
    refine ⟨eq_of_blocks (hZd.mul (isBlockDiag_e6E L i)) ((isBlockDiag_e6E L i).mul hZd) ?_ ?_,
      eq_of_blocks (hZd.mul (isBlockDiag_e6F L i)) ((isBlockDiag_e6F L i).mul hZd) ?_ ?_⟩
    · rw [ulBlock_mul hZd, ulBlock_mul (isBlockDiag_e6E L i), ulBlock_e6E]
      exact (h i).1
    · rw [lrBlock_mul hZd, lrBlock_mul (isBlockDiag_e6E L i), lrBlock_e6E, hlr]
      exact transpose_commute hE'
    · rw [ulBlock_mul hZd, ulBlock_mul (isBlockDiag_e6F L i), ulBlock_e6F]
      exact (h i).2
    · rw [lrBlock_mul hZd, lrBlock_mul (isBlockDiag_e6F L i), lrBlock_e6F, hlr]
      exact transpose_commute hF'

end CFSG.TauCetiBridge.Twisted
