module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4Red

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Blueprint
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Fix

variable {G : Type*} [Group G]

@[expose] def fixSub (α : MulAut G) : Subgroup G where
  carrier := {g | α g = g}
  one_mem' := map_one α
  mul_mem' := fun {a b} (ha : α a = a) (hb : α b = b) => by
    show α (a * b) = a * b
    rw [map_mul, ha, hb]
  inv_mem' := fun {a} (ha : α a = a) => by
    show α a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixSub {α : MulAut G} {g : G} : g ∈ fixSub α ↔ α g = g := Iff.rfl

theorem fixSub_conj (β α : MulAut G) : fixSub (β * α * β⁻¹) = (fixSub α).map β.toMonoidHom := by
  ext g
  rw [mem_fixSub, Subgroup.mem_map_equiv, mem_fixSub, MulAut.mul_apply, MulAut.mul_apply]
  constructor
  · intro h
    have h1 := congrArg β.symm h
    rwa [MulEquiv.symm_apply_apply] at h1
  · intro h
    rw [MulAut.inv_apply]
    show β (α (β.symm g)) = g
    rw [h, MulEquiv.apply_symm_apply]

noncomputable def fixSubEquiv {H : Type*} [Group H] (e : G ≃* H) (α : MulAut G) :
    ↥(fixSub α) ≃* ↥(fixSub ((e.symm.trans α).trans e)) :=
  (Subgroup.equivMapOfInjective (fixSub α) e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      ext h
      rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub]
      simp only [MulEquiv.trans_apply]
      constructor
      · intro hh
        rw [hh, MulEquiv.apply_symm_apply]
      · intro hh
        have h1 := congrArg e.symm hh
        rwa [MulEquiv.symm_apply_apply] at h1))

end Fix

section Blocks

variable {F : Type} [Field F]

abbrev blk31 (Y : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 4) (Fin 4) F :=
  !![Y 0 0, Y 0 1, Y 0 2, 0; Y 1 0, Y 1 1, Y 1 2, 0; Y 2 0, Y 2 1, Y 2 2, 0; 0, 0, 0, 1]

theorem blk31_one : blk31 (1 : Matrix (Fin 3) (Fin 3) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem blk31_mul (Y Z : Matrix (Fin 3) (Fin 3) F) : blk31 (Y * Z) = blk31 Y * blk31 Z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

theorem det_blk31 (Y : Matrix (Fin 3) (Fin 3) F) : (blk31 Y).det = Y.det := by
  rw [Matrix.det_succ_row_zero, Matrix.det_fin_three]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem det_zero_of_blocks {M : Matrix (Fin 4) (Fin 4) F}
    (h : ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → M i j = 0) (h33 : M 3 3 = 0) : M.det = 0 := by
  have h00 := h 0 0 (by decide) (by decide)
  have h01 := h 0 1 (by decide) (by decide)
  have h02 := h 0 2 (by decide) (by decide)
  have h10 := h 1 0 (by decide) (by decide)
  have h11 := h 1 1 (by decide) (by decide)
  have h12 := h 1 2 (by decide) (by decide)
  have h20 := h 2 0 (by decide) (by decide)
  have h21 := h 2 1 (by decide) (by decide)
  have h22 := h 2 2 (by decide) (by decide)
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, h00, h01,
    h02, h10, h11, h12, h20, h21, h22, h33]

@[expose] noncomputable def iota31 : SL(3, F) →* SL(4, F) where
  toFun Y := ⟨blk31 (Y : Matrix (Fin 3) (Fin 3) F), by rw [det_blk31]; exact Y.2⟩
  map_one' := Subtype.ext (by
    show blk31 (1 : Matrix (Fin 3) (Fin 3) F) = 1
    exact blk31_one)
  map_mul' Y Z := Subtype.ext (by
    show blk31 ((Y : Matrix (Fin 3) (Fin 3) F) * (Z : Matrix (Fin 3) (Fin 3) F)) =
      blk31 (Y : Matrix (Fin 3) (Fin 3) F) * blk31 (Z : Matrix (Fin 3) (Fin 3) F)
    exact blk31_mul _ _)

theorem coe_iota31 (Y : SL(3, F)) :
    ((iota31 Y : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = blk31 (Y : Matrix (Fin 3) (Fin 3) F) :=
  rfl

@[expose] noncomputable def phi31 : SL(3, F) →* projectiveSL 4 F := (proj 4 F).comp iota31

theorem zero_of_eq_neg (h2 : (2 : F) ≠ 0) {a : F} (h : a = -a) : a = 0 :=
  (mul_eq_zero.mp (show (2 : F) * a = 0 by linear_combination h)).resolve_left h2

theorem dMd_apply (M : Matrix (Fin 4) (Fin 4) F) (i j : Fin 4) :
    (E1521.blk (1 : F) 1 0 0 (-1) * M * E1521.blk (1 : F) 1 0 0 (-1)) i j =
      (if i = 3 then -1 else 1) * (if j = 3 then -1 else 1) * M i j := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.vecMul, dotProduct]

theorem exists_iota31_of_fix [Finite F] (hF : Nat.card F = 3) (g : SL(4, F))
    (hg : conjAut 4 F (E1521.dGL F) (proj 4 F g) = proj 4 F g) :
    ∃ Y : SL(3, F), proj 4 F (iota31 Y) = proj 4 F g := by
  have h2 := E1521.card3_two_ne_zero hF
  rw [conjAut_proj] at hg
  obtain ⟨c, -, hcm⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.proj_eq_exists hg
  rw [coe_slConjugation] at hcm
  have hD : (((E1521.dGL F)⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      E1521.blk 1 1 0 0 (-1) := rfl
  rw [E1521.coe_dGL, hD] at hcm
  set M := (g : Matrix (Fin 4) (Fin 4) F) with hM
  have e : ∀ i j, M i j = (c : F) * ((if i = 3 then -1 else 1) * (if j = 3 then -1 else 1) *
      M i j) := fun i j => by
    have := congrFun (congrFun hcm i) j
    rw [Matrix.smul_apply, dMd_apply, smul_eq_mul] at this
    exact this
  have hc2 : (c : F) * c = 1 := E1521.card3_mul_self hF c.ne_zero
  have hc : (c : F) = 1 ∨ (c : F) = -1 := by
    have h : ((c : F) - 1) * ((c : F) + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hdet : M.det = 1 := g.2
  rcases hc with hc | hc
  · have z : ∀ i j : Fin 4, (i = 3 ∧ j ≠ 3) ∨ (i ≠ 3 ∧ j = 3) → M i j = 0 := by
      intro i j hij
      have h1 := e i j
      rw [hc, one_mul] at h1
      rcases hij with ⟨hi, hj⟩ | ⟨hi, hj⟩
      · rw [if_pos hi, if_neg hj] at h1
        exact zero_of_eq_neg h2 (by linear_combination h1)
      · rw [if_neg hi, if_pos hj] at h1
        exact zero_of_eq_neg h2 (by linear_combination h1)
    have z03 := z 0 3 (Or.inr ⟨by decide, rfl⟩)
    have z13 := z 1 3 (Or.inr ⟨by decide, rfl⟩)
    have z23 := z 2 3 (Or.inr ⟨by decide, rfl⟩)
    have z30 := z 3 0 (Or.inl ⟨rfl, by decide⟩)
    have z31 := z 3 1 (Or.inl ⟨rfl, by decide⟩)
    have z32 := z 3 2 (Or.inl ⟨rfl, by decide⟩)
    set Y' : Matrix (Fin 3) (Fin 3) F :=
      !![M 0 0, M 0 1, M 0 2; M 1 0, M 1 1, M 1 2; M 2 0, M 2 1, M 2 2] with hY'
    have hdM : M.det = Y'.det * M 3 3 := by
      rw [Matrix.det_succ_row_zero, hY', Matrix.det_fin_three]
      simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove, z03,
        z13, z23, z30, z31, z32]
      ring
    have hm0 : M 3 3 ≠ 0 := fun h0 => by
      rw [hdet, h0, mul_zero] at hdM
      exact one_ne_zero hdM
    have hm2 := E1521.card3_mul_self hF hm0
    have hm : M 3 3 = 1 ∨ M 3 3 = -1 := by
      have h : (M 3 3 - 1) * (M 3 3 + 1) = 0 := by linear_combination hm2
      rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hm with hm | hm
    · have hY1 : Y'.det = 1 := by
        have h1 := hdM
        rw [hdet, hm, mul_one] at h1
        exact h1.symm
      refine ⟨⟨Y', hY1⟩, congrArg (proj 4 F) (Subtype.ext ?_)⟩
      show blk31 Y' = M
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hY', z03, z13, z23, z30, z31, z32, hm]
    · have hY1 : (-Y').det = 1 := by
        rw [Matrix.det_neg, Fintype.card_fin]
        have : Y'.det = -1 := by
          have h1 : Y'.det * (-1) = 1 := by rw [← hm, ← hdM, hdet]
          linear_combination -h1
        rw [this]
        norm_num
      have hs : ((-1 : Fˣ)) ^ 4 = 1 := by norm_num
      have hmem := scalarElement_mem_scalars (n := 4) (-1 : Fˣ) hs
      refine ⟨⟨-Y', hY1⟩, ?_⟩
      have hprod : iota31 ⟨-Y', hY1⟩ = scalarElement (-1 : Fˣ) hs * g := by
        apply Subtype.ext
        show blk31 (-Y') = Matrix.scalar (Fin 4) (((-1 : Fˣ)) : F) * M
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hY', z03, z13, z23, z30, z31, z32, hm,
          Matrix.mul_apply, Fin.sum_univ_four]
      rw [hprod, map_mul, (proj_eq_one_iff).mpr hmem, one_mul]
  · exfalso
    have z : ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → M i j = 0 := by
      intro i j hi hj
      have h1 := e i j
      rw [hc, if_neg hi, if_neg hj] at h1
      exact zero_of_eq_neg h2 (by linear_combination h1)
    have z33 : M 3 3 = 0 := by
      have h1 := e 3 3
      rw [hc, if_pos rfl] at h1
      exact zero_of_eq_neg h2 (by linear_combination h1)
    have := det_zero_of_blocks z z33
    rw [hdet] at this
    exact one_ne_zero this

theorem blk31_comm_d (Y : Matrix (Fin 3) (Fin 3) F) :
    ((E1521.dGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * blk31 Y =
      blk31 Y * ((E1521.dGL F : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
  rw [E1521.coe_dGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem range_phi31 [Finite F] (hF : Nat.card F = 3) :
    (phi31 : SL(3, F) →* projectiveSL 4 F).range = fixSub (conjAut 4 F (E1521.dGL F)) := by
  ext y
  rw [mem_fixSub]
  constructor
  · rintro ⟨Y, rfl⟩
    exact E1521.conjAut_proj_eq_of_comm _ _ (by rw [coe_iota31]; exact blk31_comm_d _)
  · intro hy
    obtain ⟨g, rfl⟩ := proj_surjective 4 F y
    obtain ⟨Y, hY⟩ := exists_iota31_of_fix hF g hy
    exact ⟨Y, hY⟩

theorem phi31_injective : Function.Injective (phi31 : SL(3, F) →* projectiveSL 4 F) := by
  rw [injective_iff_map_eq_one]
  intro Y hY
  have h1 : iota31 Y ∈ scalars 4 F := proj_eq_one_iff.mp hY
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h1
  rw [coe_iota31] at hc
  have h33 := congrFun (congrFun hc 3) 3
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h33
  have h33' : (c : F) = 1 := by simpa using h33.symm
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  have hij := congrFun (congrFun hc i.castSucc) j.castSucc
  rw [h33'] at hij
  fin_cases i <;> fin_cases j <;> simpa [Matrix.one_apply] using hij

noncomputable def fixSubDEquiv [Finite F] (hF : Nat.card F = 3) :
    ↥(fixSub (conjAut 4 F (E1521.dGL F))) ≃* SL(3, F) :=
  ((MulEquiv.subgroupCongr (range_phi31 hF)).symm.trans
    (MonoidHom.ofInjective (phi31_injective (F := F))).symm)

end Blocks

theorem exists_fixSub_equiv_sl3 {S : Type} [Group S] (hS : LieModel S .PSL 4 3 1)
    {A B : Subgroup S} {r : S} {x : MulAut S} (h : SPHyp A B r x) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧
      Nonempty (↥(fixSub x) ≃* SL(3, F)) := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hS
  rw [pow_one] at hF
  obtain ⟨e, he⟩ := E1521.exists_mulEquiv_blockQ0 hF e₀ h.quat.q8
  have hB8 : Nonempty (↥(B.map e.toMonoidHom) ≃* QuaternionGroup 2) := by
    obtain ⟨eB⟩ := h.q8B
    exact ⟨(B.equivMapOfInjective _ e.injective).symm.trans eB⟩
  have hB2 : B.map e.toMonoidHom = E1521.blockQ2 F := E1521.eq_blockQ2_of_comm hF hB8 (by
    rw [← he]
    rintro _ ⟨b, hb, rfl⟩ _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h.comm a ha b hb])
  set α : MulAut (projectiveSL 4 F) := (e.symm.trans x).trans e with hαdef
  have hα : ∀ y, α (e y) = e (x y) := fun y => by
    simp only [hαdef, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hα2 : α * α = 1 := by
    ext y
    obtain ⟨s, rfl⟩ := e.surjective y
    rw [MulAut.mul_apply, hα, hα, h.apply_apply, MulAut.one_apply]
  have hfix : ∀ y ∈ E1521.blockQ0 F, α y = y := by
    rw [← he]
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [hα, h.fixA a ha]
  have hmov : ∃ y : projectiveSL 4 F, (∀ z ∈ E1521.blockQ0 F, y * z = z * y) ∧ α y ≠ y := by
    obtain ⟨b, hb, -, hxb⟩ := h.exists_moved
    have hb' : e b ∈ E1521.blockQ2 F := hB2 ▸ ⟨b, hb, rfl⟩
    refine ⟨e b, fun z hz => (E1521.blockQ0_comm_blockQ2 hz hb').symm, fun h1 => ?_⟩
    exact hxb (e.injective (by rw [← hα, h1]))
  obtain ⟨Bm, -, hαeq⟩ := E1521.sig_psl4 hF α hα2 hfix hmov
  have hfixα : fixSub α = (fixSub (conjAut 4 F (E1521.dGL F))).map (conjAut 4 F Bm).toMonoidHom :=
    by rw [hαeq, fixSub_conj]
  refine ⟨F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  exact (fixSubEquiv e x).trans ((MulEquiv.subgroupCongr hfixα).trans
    (((fixSub (conjAut 4 F (E1521.dGL F))).equivMapOfInjective _
      (conjAut 4 F Bm).injective).symm.trans (fixSubDEquiv hF)))

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
