module

public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryOvergroup.NormSimilarity

public section

namespace CFSG.RankTwoShapes

open scoped commutatorElement

noncomputable section

namespace UnitaryFourW

variable {K : Type} [Field K] {hK : Nat.card K = 16}

theorem map_mem_center (α : unitaryFourW K hK ≃* unitaryFourW K hK) {z : unitaryFourW K hK}
    (hz : z ∈ Subgroup.center (unitaryFourW K hK)) : α z ∈ Subgroup.center (unitaryFourW K hK) := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro u
  have h := congrArg α (hz (α.symm u))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h

theorem fst_apply_eq_zero (α : unitaryFourW K hK ≃* unitaryFourW K hK) {w : unitaryFourW K hK}
    (hw : fst w = 0) : fst (α w) = 0 := by
  have h := map_mem_center α (mem_center_of_fst_eq_zero hw)
  rw [center_eq_ker_firstCoord, mem_ker_firstCoord] at h
  exact h

theorem fst_apply_eq_of_fst_eq (α : unitaryFourW K hK ≃* unitaryFourW K hK)
    {v w : unitaryFourW K hK} (h : fst v = fst w) : fst (α v) = fst (α w) := by
  have := charP_two_of_natCard_eq_sixteen hK
  have h0 : fst (v⁻¹ * w) = 0 := by
    rw [fst_mul, fst_inv, h]
    exact CharTwo.add_self_eq_zero _
  have h1 := fst_apply_eq_zero α h0
  rw [map_mul, map_inv, fst_mul, fst_inv] at h1
  exact (CharTwo.add_eq_zero.mp h1)

theorem exists_commutatorElement_eq {w : unitaryFourW K hK} (hw : fst w = 0) :
    ∃ v₁ v₂ : unitaryFourW K hK, ⁅v₁, v₂⁆ = w := by
  obtain ⟨r, hr⟩ := exists_add_pow_four_eq hK (snd_pow_four_of_fst_eq_zero hw)
  obtain ⟨v₁, hv₁⟩ := exists_fst_eq (hK := hK) 1
  obtain ⟨v₂, hv₂⟩ := exists_fst_eq (hK := hK) r
  refine ⟨v₁, v₂, ?_⟩
  ext
  · rw [fst_commutatorElement, hw]
  · rw [snd_commutatorElement, hv₁, hv₂, ← hr]
    ring

theorem add_pow_four_eq_zero_pow_five_of_pow_four_eq (hK : Nat.card K = 16) {t : K}
    (ht : t ^ 4 = t) :
    t + t ^ 4 = (0 : K) ^ 5 := by
  have := charP_two_of_natCard_eq_sixteen hK
  rw [ht, CharTwo.add_self_eq_zero, zero_pow (by norm_num)]

@[expose] def inducedFst (α : unitaryFourW K hK ≃* unitaryFourW K hK) : K →+ K where
  toFun a := fst (α (exists_fst_eq (hK := hK) a).choose)
  map_zero' := fst_apply_eq_zero α (exists_fst_eq (hK := hK) 0).choose_spec
  map_add' a b := by
    rw [fst_apply_eq_of_fst_eq α ((exists_fst_eq (hK := hK) (a + b)).choose_spec.trans
      (by rw [fst_mul, (exists_fst_eq (hK := hK) a).choose_spec,
        (exists_fst_eq (hK := hK) b).choose_spec]) :
      fst (exists_fst_eq (hK := hK) (a + b)).choose =
        fst ((exists_fst_eq (hK := hK) a).choose * (exists_fst_eq (hK := hK) b).choose)),
      map_mul, fst_mul]

theorem inducedFst_fst (α : unitaryFourW K hK ≃* unitaryFourW K hK) (w : unitaryFourW K hK) :
    inducedFst α (fst w) = fst (α w) :=
  fst_apply_eq_of_fst_eq α (exists_fst_eq (hK := hK) (fst w)).choose_spec

@[expose] def centralMk (hK : Nat.card K = 16) (t : fieldSixteenSubfield hK) : unitaryFourW K hK :=
  mk hK 0 t (add_pow_four_eq_zero_pow_five_of_pow_four_eq hK t.2)

@[simp] theorem fst_centralMk (t : fieldSixteenSubfield hK) : fst (centralMk hK t) = 0 :=
  fst_mk _ _ _

@[simp] theorem snd_centralMk (t : fieldSixteenSubfield hK) : snd (centralMk hK t) = t :=
  snd_mk _ _ _

theorem centralMk_snd {w : unitaryFourW K hK} (hw : fst w = 0) :
    centralMk hK ⟨snd w, snd_pow_four_of_fst_eq_zero hw⟩ = w := by
  ext
  · rw [fst_centralMk, hw]
  · rw [snd_centralMk]

@[expose] def inducedSnd (α : unitaryFourW K hK ≃* unitaryFourW K hK) :
    fieldSixteenSubfield hK →+ fieldSixteenSubfield hK where
  toFun t := ⟨snd (α (centralMk hK t)),
    snd_pow_four_of_fst_eq_zero (fst_apply_eq_zero α (fst_centralMk t))⟩
  map_zero' := by
    apply Subtype.ext
    have : centralMk hK (0 : fieldSixteenSubfield hK) = 1 := by
      ext
      · rw [fst_centralMk, fst_one]
      · rw [snd_centralMk, snd_one]
        rfl
    change snd (α (centralMk hK 0)) = 0
    rw [this, map_one, snd_one]
  map_add' s t := by
    apply Subtype.ext
    have : centralMk hK (s + t) = centralMk hK s * centralMk hK t := by
      ext
      · rw [fst_centralMk, fst_mul, fst_centralMk, fst_centralMk, add_zero]
      · rw [snd_centralMk, snd_mul, snd_centralMk, snd_centralMk, fst_centralMk]
        simp
    change snd (α (centralMk hK (s + t))) = snd (α (centralMk hK s)) + snd (α (centralMk hK t))
    rw [this, map_mul, snd_mul, fst_apply_eq_zero α (fst_centralMk s)]
    simp

theorem inducedSnd_apply (α : unitaryFourW K hK ≃* unitaryFourW K hK)
    (t : fieldSixteenSubfield hK) :
    (inducedSnd α t : K) = snd (α (centralMk hK t)) :=
  rfl

theorem inducedSnd_eq_inducedFst_mul (α : unitaryFourW K hK ≃* unitaryFourW K hK) (z : K)
    (w : fieldSixteenSubfield hK) (hw : (w : K) = z * z ^ 4) :
    (inducedSnd α w : K) = inducedFst α z * inducedFst α z ^ 4 := by
  obtain ⟨v, hv⟩ := exists_fst_eq (hK := hK) z
  have hsq : centralMk hK w = v ^ 2 := by
    ext
    · rw [fst_centralMk, fst_sq]
    · rw [snd_centralMk, snd_sq, hv, hw]
      ring
  rw [inducedSnd_apply, hsq, map_pow, snd_sq, ← hv, inducedFst_fst]
  ring

theorem inducedFst_ne_zero (α : unitaryFourW K hK ≃* unitaryFourW K hK) : inducedFst α ≠ 0 := by
  intro h
  obtain ⟨v, hv⟩ := exists_fst_eq (hK := hK) 1
  have h1 := inducedFst_fst α (α.symm v)
  rw [MulEquiv.apply_symm_apply, hv, h, AddMonoidHom.zero_apply] at h1
  exact zero_ne_one h1

theorem exists_units_fin_four_of_mulEquiv (α : unitaryFourW K hK ≃* unitaryFourW K hK) :
    ∃ (c : Kˣ) (j : Fin 4), (∀ w, fst (α w) = c * fst w ^ 2 ^ (j : ℕ)) ∧
      ∀ w, fst w = 0 → snd (α w) = c ^ 5 * snd w ^ 2 ^ (j : ℕ) := by
  have hF4 : Nat.card (fieldSixteenSubfield hK) = 4 :=
    natCard_pow_four_eq_self hK
  obtain ⟨⟨c, j⟩, ⟨hA, hB⟩, -⟩ :=
    (binaryQuadraticNorm_similarity_rigidity hK (fieldSixteenSubfield hK) hF4).1
      (inducedFst α) (inducedSnd α) (inducedFst_ne_zero α) (inducedSnd_eq_inducedFst_mul α)
  refine ⟨c, j, fun w => ?_, fun w hw => ?_⟩
  · rw [← inducedFst_fst, hA]
  · have h := hB ⟨snd w, snd_pow_four_of_fst_eq_zero hw⟩
    rw [inducedSnd_apply, centralMk_snd hw] at h
    rw [h]
    ring

@[expose] def firstCoordFixing (hK : Nat.card K = 16) : Subgroup (MulAut (unitaryFourW K hK)) where
  carrier := {α | ∀ w, fst (α w) = fst w}
  mul_mem' {α β} hα hβ w := by
    change fst (α (β w)) = fst w
    rw [hα, hβ]
  one_mem' w := rfl
  inv_mem' {α} hα w := by
    have h := hα (α⁻¹ w)
    change fst (α (α.symm w)) = fst (α.symm w) at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm

theorem mem_firstCoordFixing {α : MulAut (unitaryFourW K hK)} :
    α ∈ firstCoordFixing hK ↔ ∀ w, fst (α w) = fst w :=
  Iff.rfl

instance firstCoordFixing_normal : (firstCoordFixing hK).Normal where
  conj_mem α hα β w := by
    change fst (β (α (β.symm w))) = fst w
    rw [fst_apply_eq_of_fst_eq β (hα (β.symm w)), MulEquiv.apply_symm_apply]

theorem apply_eq_self_of_mem_firstCoordFixing {α : MulAut (unitaryFourW K hK)}
    (hα : α ∈ firstCoordFixing hK) {z : unitaryFourW K hK} (hz : fst z = 0) : α z = z := by
  obtain ⟨v₁, v₂, rfl⟩ := exists_commutatorElement_eq hz
  rw [map_commutatorElement]
  ext
  · rw [fst_commutatorElement, fst_commutatorElement]
  · rw [snd_commutatorElement, snd_commutatorElement, hα, hα]

theorem mul_self_eq_one_of_mem_firstCoordFixing {α : MulAut (unitaryFourW K hK)}
    (hα : α ∈ firstCoordFixing hK) : α * α = 1 := by
  have := charP_two_of_natCard_eq_sixteen hK
  ext1 w
  change α (α w) = w
  have hd : fst (w⁻¹ * α w) = 0 := by
    rw [fst_mul, fst_inv, hα]
    exact CharTwo.add_self_eq_zero _
  have hαw : α w = w * (w⁻¹ * α w) := by group
  have hsq := sq_eq_one_of_mem_center (mem_center_of_fst_eq_zero hd)
  calc α (α w) = α (w * (w⁻¹ * α w)) := by rw [← hαw]
    _ = α w * α (w⁻¹ * α w) := map_mul α _ _
    _ = w * (w⁻¹ * α w) ^ 2 := by
      rw [apply_eq_self_of_mem_firstCoordFixing hα hd]
      simp only [pow_two, mul_assoc, mul_inv_cancel_left]
    _ = w := by rw [hsq, mul_one]

end UnitaryFourW

end

end CFSG.RankTwoShapes
