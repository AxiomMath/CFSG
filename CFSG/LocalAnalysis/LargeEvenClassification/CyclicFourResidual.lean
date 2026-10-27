module

public import CFSG.LocalAnalysis.LargeEvenClassification.ResidualRing

public section

namespace CFSG.LargeEvenClassification.Helpers

@[expose] def residualZeroLongDiagonal : ResidualRing 0 →+* ZMod 4 where
  toFun r := r.1.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' r s := by
    change r.1.1 * s.1.1 + 0 * r.1.2 * s.2.1 = _
    simp only [zero_mul, add_zero]

@[expose] def residualZeroShortDiagonal : ResidualRing 0 →+* ZMod 4 where
  toFun r := r.2.2
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' r s := by
    change 0 * r.2.1 * s.1.2 + r.2.2 * s.2.2 = _
    simp only [zero_mul, zero_add]

@[expose] def residualZeroDiagonal : (ResidualRing 0)ˣ →* (ZMod 4)ˣ × (ZMod 4)ˣ :=
  (Units.map residualZeroLongDiagonal.toMonoidHom).prod
    (Units.map residualZeroShortDiagonal.toMonoidHom)

@[expose] def residualZeroShear : Multiplicative (ZMod 4 × ZMod 4) →* (ResidualRing 0)ˣ where
  toFun x := {
    val := ((1, x.toAdd.1), (x.toAdd.2, 1))
    inv := ((1, -x.toAdd.1), (-x.toAdd.2, 1))
    val_inv := by
      change residualMultiply 0 _ _ = ((1, 0), (0, 1))
      simp only [residualMultiply, zero_mul, one_mul, mul_one, add_zero,
        zero_add, add_neg_cancel, neg_add_cancel]
      rfl
    inv_val := by
      change residualMultiply 0 _ _ = ((1, 0), (0, 1))
      simp only [residualMultiply, zero_mul, one_mul, mul_one, add_zero,
        zero_add, neg_add_cancel, add_neg_cancel]
      rfl }
  map_one' := rfl
  map_mul' x y := by
    apply Units.ext
    change ((1, x.toAdd.1 + y.toAdd.1), (x.toAdd.2 + y.toAdd.2, 1)) =
      residualMultiply 0 _ _
    simp only [residualMultiply, zero_mul, one_mul, mul_one, add_zero, zero_add]
    rw [add_comm x.toAdd.1 y.toAdd.1]

theorem residualZeroShear_injective : Function.Injective residualZeroShear := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply Prod.ext
  · exact congrArg (fun u : (ResidualRing 0)ˣ => u.val.1.2) h
  · exact congrArg (fun u : (ResidualRing 0)ˣ => u.val.2.1) h

@[expose] def residualZeroDiagonalSection : (ZMod 4)ˣ × (ZMod 4)ˣ →* (ResidualRing 0)ˣ where
  toFun x := {
    val := ((x.1.val, 0), (0, x.2.val))
    inv := ((x.1.inv, 0), (0, x.2.inv))
    val_inv := by
      change residualMultiply 0 _ _ = ((1, 0), (0, 1))
      simp only [residualMultiply, zero_mul, mul_zero, add_zero, zero_add,
        x.1.val_inv, x.2.val_inv]
      rfl
    inv_val := by
      change residualMultiply 0 _ _ = ((1, 0), (0, 1))
      simp only [residualMultiply, zero_mul, mul_zero, add_zero, zero_add,
        x.1.inv_val, x.2.inv_val]
      rfl }
  map_one' := rfl
  map_mul' x y := by
    apply Units.ext
    change ((x.1.val * y.1.val, 0), (0, x.2.val * y.2.val)) = residualMultiply 0 _ _
    simp only [residualMultiply, zero_mul, mul_zero, add_zero, zero_add]

theorem residualZeroDiagonal_section (x : (ZMod 4)ˣ × (ZMod 4)ˣ) :
    residualZeroDiagonal (residualZeroDiagonalSection x) = x := by
  apply Prod.ext <;> apply Units.ext <;> rfl

theorem residualZeroDiagonal_surjective : Function.Surjective residualZeroDiagonal :=
  Function.RightInverse.surjective residualZeroDiagonal_section

theorem residualZeroDiagonal_kernel : residualZeroDiagonal.ker = residualZeroShear.range := by
  apply le_antisymm
  · intro r hr
    have hdiagonal : r.val.1.1 = 1 ∧ r.val.2.2 = 1 := by
      exact ⟨congrArg (fun x : (ZMod 4)ˣ × (ZMod 4)ˣ => x.1.val) hr,
        congrArg (fun x : (ZMod 4)ˣ × (ZMod 4)ˣ => x.2.val) hr⟩
    refine ⟨Multiplicative.ofAdd (r.val.1.2, r.val.2.1), ?_⟩
    apply Units.ext
    change ((1, r.val.1.2), (r.val.2.1, 1)) = r.val
    exact Prod.ext (Prod.ext hdiagonal.1.symm rfl) (Prod.ext rfl hdiagonal.2.symm)
  · rintro r ⟨x, rfl⟩
    apply Prod.ext <;> apply Units.ext <;> rfl

theorem residualZero_normal_form (r : (ResidualRing 0)ˣ) :
    ∃ x : Multiplicative (ZMod 4 × ZMod 4),
      r = residualZeroShear x * residualZeroDiagonalSection (residualZeroDiagonal r) := by
  let d := residualZeroDiagonalSection (residualZeroDiagonal r)
  have hkernel : r * d⁻¹ ∈ residualZeroDiagonal.ker := by
    change residualZeroDiagonal (r * d⁻¹) = 1
    rw [map_mul, map_inv, residualZeroDiagonal_section, mul_inv_cancel]
  rw [residualZeroDiagonal_kernel] at hkernel
  obtain ⟨x, hx⟩ := hkernel
  exact ⟨x, by rw [hx, mul_assoc, inv_mul_cancel, mul_one]⟩

@[expose] def fourUnitSign : Multiplicative (ZMod 2) →* (ZMod 4)ˣ where
  toFun e := (-1) ^ e.toAdd.val
  map_one' := rfl
  map_mul' e f := by
    have h : ∀ e f : ZMod 2,
        (-1 : (ZMod 4)ˣ) ^ (e + f).val = (-1) ^ e.val * (-1) ^ f.val := by
      decide +kernel
    exact h e.toAdd f.toAdd

theorem fourUnitSign_bijective : Function.Bijective fourUnitSign := by
  constructor
  · intro e f h
    have hi : ∀ e f : ZMod 2,
        (-1 : (ZMod 4)ˣ) ^ e.val = (-1) ^ f.val → e = f := by decide +kernel
    exact Multiplicative.toAdd.injective (hi e.toAdd f.toAdd h)
  · intro u
    have hs : ∀ u : (ZMod 4)ˣ, ∃ e : ZMod 2, (-1 : (ZMod 4)ˣ) ^ e.val = u := by
      decide +kernel
    obtain ⟨e, he⟩ := hs u
    exact ⟨Multiplicative.ofAdd e, he⟩

@[expose] noncomputable def fourUnitSignEquiv : Multiplicative (ZMod 2) ≃* (ZMod 4)ˣ :=
  MulEquiv.ofBijective fourUnitSign fourUnitSign_bijective

@[expose] def residualZeroU : (ResidualRing 0)ˣ := residualZeroShear (Multiplicative.ofAdd (1, 0))
@[expose] def residualZeroV : (ResidualRing 0)ˣ := residualZeroShear (Multiplicative.ofAdd (0, 1))
@[expose] def residualZeroZ : (ResidualRing 0)ˣ := residualZeroDiagonalSection (-1, 1)
@[expose] def residualZeroW : (ResidualRing 0)ˣ := residualZeroDiagonalSection (1, -1)

theorem residualZeroShear_powers (i j : ZMod 4) :
    residualZeroShear (Multiplicative.ofAdd (i, j)) = residualZeroU ^ i.val * residualZeroV ^ j.val := by
  rw [residualZeroU, residualZeroV, ← map_pow residualZeroShear, ← map_pow residualZeroShear, ← map_mul residualZeroShear]
  congr 1
  apply Multiplicative.toAdd.injective
  change (i, j) = i.val • (1, 0) + j.val • (0, 1)
  apply Prod.ext
  · change i = i.val • (1 : ZMod 4) + j.val • 0
    simp only [smul_zero, add_zero, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  · change j = i.val • (0 : ZMod 4) + j.val • 1
    simp only [smul_zero, zero_add, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]

theorem residualZero_generators_normal_form (r : (ResidualRing 0)ˣ) :
    ∃ (i j : ZMod 4) (e f : ZMod 2),
      r = residualZeroU ^ i.val * residualZeroV ^ j.val * residualZeroZ ^ e.val * residualZeroW ^ f.val := by
  obtain ⟨x, hx⟩ := residualZero_normal_form r
  obtain ⟨e, he⟩ := fourUnitSign_bijective.2 (residualZeroDiagonal r).1
  obtain ⟨f, hf⟩ := fourUnitSign_bijective.2 (residualZeroDiagonal r).2
  refine ⟨x.toAdd.1, x.toAdd.2, e.toAdd, f.toAdd, ?_⟩
  rw [hx]
  change residualZeroShear (Multiplicative.ofAdd (x.toAdd.1, x.toAdd.2)) * _ = _
  rw [residualZeroShear_powers]
  have hd : residualZeroDiagonal r = ((-1) ^ e.toAdd.val, (-1) ^ f.toAdd.val) :=
    Prod.ext he.symm hf.symm
  rw [hd]
  have hs : residualZeroDiagonalSection ((-1) ^ e.toAdd.val, (-1) ^ f.toAdd.val) =
      residualZeroZ ^ e.toAdd.val * residualZeroW ^ f.toAdd.val := by
    rw [residualZeroZ, residualZeroW, ← map_pow residualZeroDiagonalSection,
      ← map_pow residualZeroDiagonalSection, ← map_mul residualZeroDiagonalSection]
    apply congrArg residualZeroDiagonalSection
    apply Prod.ext <;> simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_mul, Prod.snd_mul,
      one_pow, mul_one, one_mul]
  rw [hs]
  simp only [mul_assoc]

theorem residualZero_generators :
    Subgroup.closure ({residualZeroU, residualZeroV, residualZeroZ, residualZeroW} : Set (ResidualRing 0)ˣ) = ⊤ := by
  apply top_unique
  intro r _
  obtain ⟨i, j, e, f, rfl⟩ := residualZero_generators_normal_form r
  apply Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_) ?_ <;>
    apply Subgroup.pow_mem _ (Subgroup.subset_closure (by simp))

theorem residualZeroShear_range_generators :
    residualZeroShear.range = Subgroup.closure ({residualZeroU, residualZeroV} : Set (ResidualRing 0)ˣ) := by
  apply le_antisymm
  · rintro r ⟨x, rfl⟩
    change residualZeroShear (Multiplicative.ofAdd (x.toAdd.1, x.toAdd.2)) ∈ _
    rw [residualZeroShear_powers]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · apply (Subgroup.closure_le _).mpr
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact ⟨Multiplicative.ofAdd (1, 0), rfl⟩
    · exact ⟨Multiplicative.ofAdd (0, 1), rfl⟩

@[expose] noncomputable def residualZeroShearEquiv :
    Multiplicative (ZMod 4 × ZMod 4) ≃* residualZeroDiagonal.ker :=
  (MonoidHom.ofInjective residualZeroShear_injective).trans
    (MulEquiv.subgroupCongr residualZeroDiagonal_kernel.symm)

@[expose] noncomputable def residualZeroOuterEquiv :
    ((ResidualRing 0)ˣ ⧸ residualZeroDiagonal.ker) ≃*
      Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (QuotientGroup.quotientKerEquivOfSurjective residualZeroDiagonal
    residualZeroDiagonal_surjective).trans
      (MulEquiv.prodCongr fourUnitSignEquiv.symm fourUnitSignEquiv.symm)

theorem residualZeroShear_fourth_power (x : Multiplicative (ZMod 4 × ZMod 4)) :
    residualZeroShear x ^ 4 = 1 := by
  rw [← map_pow]
  have h : x ^ 4 = 1 := by
    apply Multiplicative.toAdd.injective
    change 4 • x.toAdd = 0
    apply Prod.ext
    · change 4 • x.toAdd.1 = (0 : ZMod 4)
      rw [nsmul_eq_mul]
      decide +revert +kernel
    · change 4 • x.toAdd.2 = (0 : ZMod 4)
      rw [nsmul_eq_mul]
      decide +revert +kernel
  rw [h, map_one]

theorem residualZeroShear_square (x : Multiplicative (ZMod 4 × ZMod 4)) :
    residualZeroShear x ^ 2 = 1 ↔
      (∃ i : ZMod 2, x.toAdd.1 = 2 * (i.val : ZMod 4)) ∧
      (∃ j : ZMod 2, x.toAdd.2 = 2 * (j.val : ZMod 4)) := by
  have h : residualZeroShear x ^ 2 = 1 ↔ x ^ 2 = 1 := by
    rw [← map_pow, ← residualZeroShear.map_one]
    exact residualZeroShear_injective.eq_iff
  rw [h]
  have hcoordinates : x ^ 2 = 1 ↔ 2 • x.toAdd = 0 := Iff.rfl
  rw [hcoordinates]
  have hcertificate : ∀ x : ZMod 4 × ZMod 4, 2 • x = 0 ↔
      (∃ i : ZMod 2, x.1 = 2 * (i.val : ZMod 4)) ∧
      (∃ j : ZMod 2, x.2 = 2 * (j.val : ZMod 4)) := by decide +kernel
  exact hcertificate x.toAdd

end CFSG.LargeEvenClassification.Helpers
