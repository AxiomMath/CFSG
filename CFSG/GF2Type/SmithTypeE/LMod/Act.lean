module

public import CFSG.GF2Type.SmithTypeE.LMod.Tv
public import CFSG.GF2Type.SmithTypeE.LMod.Points

public section

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6 Matrix
open scoped MatrixGroups
open CFSG.LargeExtraspecial.SMod20 (bit)

attribute [local irreducible] tvIdxTab tvTab tvImg tvList

theorem coe_inv_mul (A : SL(6, ZMod 2)) :
    ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * (A : Matrix (Fin 6) (Fin 6) (ZMod 2))
      = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv (A : SL(6, ZMod 2)) :
    (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *
      ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem actSet_aux (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) (hBA : B * A = 1)
    {v φ : Fin 6 → ZMod 2} (hv : v ≠ 0) (hφ : φ ≠ 0) (hd : φ ⬝ᵥ v = 0) :
    A *ᵥ v ≠ 0 ∧ φ ᵥ* B ≠ 0 ∧ (φ ᵥ* B) ⬝ᵥ (A *ᵥ v) = 0 := by
  refine ⟨fun h => hv ?_, fun h => hφ ?_, ?_⟩
  · calc v = (B * A) *ᵥ v := by rw [hBA, one_mulVec]
      _ = B *ᵥ (A *ᵥ v) := by rw [← mulVec_mulVec]
      _ = 0 := by rw [h, mulVec_zero]
  · calc φ = φ ᵥ* (B * A) := by rw [hBA, vecMul_one]
      _ = (φ ᵥ* B) ᵥ* A := by rw [vecMul_vecMul]
      _ = 0 := by rw [h, zero_vecMul]
  · calc (φ ᵥ* B) ⬝ᵥ (A *ᵥ v) = φ ⬝ᵥ (B *ᵥ (A *ᵥ v)) :=
          (dotProduct_mulVec φ B (A *ᵥ v)).symm
      _ = φ ⬝ᵥ ((B * A) *ᵥ v) := by rw [mulVec_mulVec]
      _ = 0 := by rw [hBA, one_mulVec, hd]

@[expose] def actSet (A : SL(6, ZMod 2)) (p : TvSet) : TvSet :=
  ⟨((A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ p.1.1,
    p.1.2 ᵥ* ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))),
    actSet_aux _ _ (coe_inv_mul A) p.2.1 p.2.2.1 p.2.2.2⟩

theorem actSet_fst (A : SL(6, ZMod 2)) (p : TvSet) :
    (actSet A p).1.1 = (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ p.1.1 := rfl

theorem actSet_snd (A : SL(6, ZMod 2)) (p : TvSet) :
    (actSet A p).1.2 = p.1.2 ᵥ* ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) := rfl

theorem actSet_ext {p q : TvSet} (h1 : p.1.1 = q.1.1) (h2 : p.1.2 = q.1.2) : p = q :=
  Subtype.ext (Prod.ext h1 h2)

theorem actSet_one (p : TvSet) : actSet 1 p = p :=
  actSet_ext (by rw [actSet_fst, Matrix.SpecialLinearGroup.coe_one, one_mulVec])
    (by rw [actSet_snd, inv_one, Matrix.SpecialLinearGroup.coe_one, vecMul_one])

theorem actSet_mul (A B : SL(6, ZMod 2)) (p : TvSet) :
    actSet (A * B) p = actSet A (actSet B p) :=
  actSet_ext (by rw [actSet_fst, actSet_fst, actSet_fst, Matrix.SpecialLinearGroup.coe_mul,
      mulVec_mulVec])
    (by rw [actSet_snd, actSet_snd, actSet_snd, vecMul_vecMul, _root_.mul_inv_rev,
      Matrix.SpecialLinearGroup.coe_mul])

instance : MulAction SL(6, ZMod 2) TvSet where
  smul := actSet
  one_smul := actSet_one
  mul_smul := actSet_mul

theorem smul_def (A : SL(6, ZMod 2)) (p : TvSet) : A • p = actSet A p := rfl

section Certified

theorem tvVec_ne_zero {k : ℕ} (hk : k < 1953) : tvVec k ≠ 0 := by
  obtain ⟨h1, -, h3, -⟩ := tvListFacts.entry k hk
  intro h
  exact h3 (dec6_inj h1 (by norm_num) (h.trans dec6_zero.symm))

theorem tvForm_ne_zero {k : ℕ} (hk : k < 1953) : tvForm k ≠ 0 := by
  obtain ⟨-, h2, -, h4, -⟩ := tvListFacts.entry k hk
  intro h
  exact h4 (dec6_inj h2 (by norm_num) (h.trans dec6_zero.symm))

theorem tvForm_dot_tvVec {k : ℕ} (hk : k < 1953) : tvForm k ⬝ᵥ tvVec k = 0 := by
  obtain ⟨-, -, -, -, h5, -⟩ := tvListFacts.entry k hk
  have := bit_form (tvPair k).2 (tvPair k).1
  rw [h5] at this
  exact (by simpa [bit] using this.symm : dec6 (tvPair k).2 ⬝ᵥ dec6 (tvPair k).1 = 0)

@[expose] def tvToSet (k : Fin 1953) : TvSet :=
  ⟨(tvVec k, tvForm k), tvVec_ne_zero k.2, tvForm_ne_zero k.2, tvForm_dot_tvVec k.2⟩

theorem tvToSet_injective : Function.Injective tvToSet := by
  intro k l h
  have h1 : tvVec k = tvVec l := congrArg (fun p => p.1.1) h
  have h2 : tvForm k = tvForm l := congrArg (fun p => p.1.2) h
  obtain ⟨hk1, hk2, -, -, -, hk6⟩ := tvListFacts.entry k k.2
  obtain ⟨hl1, hl2, -, -, -, hl6⟩ := tvListFacts.entry l l.2
  have e1 : (tvPair k).1 = (tvPair l).1 := dec6_inj hk1 hl1 h1
  have e2 : (tvPair k).2 = (tvPair l).2 := dec6_inj hk2 hl2 h2
  apply Fin.ext
  rw [← hk6, ← hl6, e1, e2]

theorem tvToSet_surjective : Function.Surjective tvToSet := by
  intro p
  obtain ⟨⟨v, φ⟩, hv, hφ, hd⟩ := p
  obtain ⟨n₁, hn₁, e₁⟩ := dec6_surj v
  obtain ⟨n₂, hn₂, e₂⟩ := dec6_surj φ
  have h1 : n₁ ≠ 0 := by
    rintro rfl
    exact hv (e₁.symm.trans dec6_zero)
  have h2 : n₂ ≠ 0 := by
    rintro rfl
    exact hφ (e₂.symm.trans dec6_zero)
  have h3 : form n₂ n₁ = false := by
    have := bit_form n₂ n₁
    rw [e₁, e₂] at this
    simp only at hd
    rw [hd] at this
    cases h : form n₂ n₁
    · rfl
    · rw [h] at this
      simp [bit] at this
  have hn : 64 * n₁ + n₂ < 4096 := by omega
  have hd1 : (64 * n₁ + n₂) / 64 = n₁ := by omega
  have hd2 : (64 * n₁ + n₂) % 64 = n₂ := by omega
  have hs := tvListFacts.surj (64 * n₁ + n₂) hn (by rw [hd1]; exact h1) (by rw [hd2]; exact h2)
    (by rw [hd1, hd2]; exact h3)
  refine ⟨⟨tvIdxTab[64 * n₁ + n₂]!, hs⟩, ?_⟩
  rcases (tvListFacts.idxTab _ hn).2 with h | h
  · omega
  · rw [hd1, hd2] at h
    apply Subtype.ext
    apply Prod.ext
    · show dec6 (tvPair tvIdxTab[64 * n₁ + n₂]!).1 = v
      rw [h]
      exact e₁
    · show dec6 (tvPair tvIdxTab[64 * n₁ + n₂]!).2 = φ
      rw [h]
      exact e₂

@[expose] noncomputable def tvEquivTv : Fin 1953 ≃ TvSet :=
  Equiv.ofBijective tvToSet ⟨tvToSet_injective, tvToSet_surjective⟩

@[expose] noncomputable def actPerm : SL(6, ZMod 2) →* Equiv.Perm (Fin 1953) where
  toFun A := tvEquivTv.symm.permCongr (MulAction.toPerm A)
  map_one' := Equiv.ext fun k => by
    simp [Equiv.permCongr_apply]
  map_mul' A B := Equiv.ext fun k => by
    simp [Equiv.permCongr_apply, mul_smul]

theorem tvEquivTv_actPerm (A : SL(6, ZMod 2)) (k : Fin 1953) :
    tvEquivTv (actPerm A k) = A • tvEquivTv k := by
  simp [actPerm, Equiv.permCongr_apply]

theorem tvVec_actPerm (A : SL(6, ZMod 2)) (k : Fin 1953) :
    tvVec (actPerm A k) = (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ tvVec k :=
  congrArg (fun p => p.1.1) (tvEquivTv_actPerm A k)

theorem tvForm_actPerm (A : SL(6, ZMod 2)) (k : Fin 1953) :
    tvForm (actPerm A k) =
      tvForm k ᵥ* ((A⁻¹ : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
  congrArg (fun p => p.1.2) (tvEquivTv_actPerm A k)

@[expose] def tvMatrix (k : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  1 + vecMulVec (tvVec k) (tvForm k)

theorem tvMatrix_mul_self {k : ℕ} (hk : k < 1953) : tvMatrix k * tvMatrix k = 1 :=
  transvec_mul_self (tvForm_dot_tvVec hk)

theorem det_tvMatrix {k : ℕ} (hk : k < 1953) : (tvMatrix k).det = 1 :=
  det_transvec (tvForm_dot_tvVec hk)

@[expose] def tvSL (k : Fin 1953) : SL(6, ZMod 2) := ⟨tvMatrix k, det_tvMatrix k.2⟩

theorem coe_tvSL (k : Fin 1953) : (tvSL k : Matrix (Fin 6) (Fin 6) (ZMod 2)) = tvMatrix k := rfl

theorem tvSL_mul_self (k : Fin 1953) : tvSL k * tvSL k = 1 :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul, coe_tvSL, tvMatrix_mul_self k.2,
    Matrix.SpecialLinearGroup.coe_one])

theorem tvSL_inv (k : Fin 1953) : (tvSL k)⁻¹ = tvSL k :=
  inv_eq_of_mul_eq_one_right (tvSL_mul_self k)

theorem tvSL_actPerm (A : SL(6, ZMod 2)) (k : Fin 1953) :
    tvSL (actPerm A k) = A * tvSL k * A⁻¹ := by
  apply Subtype.ext
  rw [coe_tvSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_tvSL]
  unfold tvMatrix
  rw [conj_transvec _ _ (coe_mul_inv A), tvVec_actPerm, tvForm_actPerm]

theorem dec6_ite_xor (c : Bool) (x w : ℕ) :
    dec6 (if c then x ^^^ w else x) = dec6 x + bit c • dec6 w := by
  cases c <;> simp [dec6_xor, bit]

theorem tvVec_tvImg {j a : Fin 1953} :
    tvVec (tvImg j a) = tvVec a + (tvForm j ⬝ᵥ tvVec a) • tvVec j := by
  have h := tvPair_tvImg j.2 a.2
  unfold tvVec tvForm
  rw [h]
  show dec6 (if form (tvPair j).2 (tvPair a).1 then (tvPair a).1 ^^^ (tvPair j).1
    else (tvPair a).1) = _
  rw [dec6_ite_xor, bit_form]

theorem tvForm_tvImg {j a : Fin 1953} :
    tvForm (tvImg j a) = tvForm a + (tvForm a ⬝ᵥ tvVec j) • tvForm j := by
  have h := tvPair_tvImg j.2 a.2
  unfold tvVec tvForm
  rw [h]
  show dec6 (if form (tvPair a).2 (tvPair j).1 then (tvPair a).2 ^^^ (tvPair j).2
    else (tvPair a).2) = _
  rw [dec6_ite_xor, bit_form]

theorem actPerm_tvSL_apply (j a : Fin 1953) :
    ((actPerm (tvSL j) a : Fin 1953) : ℕ) = tvImg j a := by
  have hlt := tvImg_lt j.2 a.2
  suffices h : actPerm (tvSL j) a = ⟨tvImg j a, hlt⟩ from congrArg Fin.val h
  apply tvToSet_injective
  apply Subtype.ext
  apply Prod.ext
  · show tvVec (actPerm (tvSL j) a) = tvVec (tvImg j a)
    rw [tvVec_actPerm, coe_tvSL, tvVec_tvImg]
    unfold tvMatrix
    rw [transvec_mulVec]
  · show tvForm (actPerm (tvSL j) a) = tvForm (tvImg j a)
    rw [tvForm_actPerm, tvSL_inv, coe_tvSL, tvForm_tvImg]
    unfold tvMatrix
    rw [vecMul_transvec]

@[expose] noncomputable def tvP (k : Fin 1953) : Equiv.Perm (Fin 1953) := actPerm (tvSL k)

theorem tvP_apply (k a : Fin 1953) : ((tvP k a : Fin 1953) : ℕ) = tvImg k a :=
  actPerm_tvSL_apply k a

theorem tvP_mul_self (k : Fin 1953) : tvP k * tvP k = 1 := by
  rw [tvP, ← map_mul, tvSL_mul_self, map_one]

theorem tvP_inv (k : Fin 1953) : (tvP k)⁻¹ = tvP k :=
  inv_eq_of_mul_eq_one_right (tvP_mul_self k)

theorem tvSL_injective : Function.Injective tvSL := by
  intro k l h
  have h' : tvMatrix k = tvMatrix l := congrArg Subtype.val h
  obtain ⟨h1, h2⟩ := transvec_inj (tvVec_ne_zero k.2) (tvForm_ne_zero k.2)
    (by simpa [tvMatrix] using h')
  apply tvToSet_injective
  exact Subtype.ext (Prod.ext h1 h2)

end Certified

theorem exists_form_ne_zero (x : Fin 6 → ZMod 2) (hx : x ≠ 0) :
    ∃ φ : Fin 6 → ZMod 2, φ ≠ 0 ∧ φ ⬝ᵥ x = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have key3 : ∀ a : ZMod 2, a + a = 0 := by decide
  have hxi : x i = 1 := key _ hi
  obtain ⟨j, hj⟩ : ∃ j : Fin 6, j ≠ i := by
    by_cases h0 : i = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, fun h => h0 h.symm⟩
  refine ⟨Pi.single j 1 + x j • Pi.single i 1, fun h => ?_, ?_⟩
  · have := congrFun h j
    simp [Pi.single_apply, hj] at this
  · simp [add_dotProduct, smul_dotProduct, hxi, key3]

section Certified2

theorem actPerm_injective : Function.Injective actPerm := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have key : ∀ x : Fin 6 → ZMod 2, (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ x = x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨φ, hφ, hd⟩ := exists_form_ne_zero x hx
    obtain ⟨k, hk⟩ := tvToSet_surjective ⟨(x, φ), hx, hφ, hd⟩
    have h1 : actPerm A k = k := by rw [hA]; rfl
    have h2 := tvEquivTv_actPerm A k
    rw [h1] at h2
    have h3 := congrArg (fun p => p.1.1) h2
    have h4 : (tvEquivTv k).1.1 = x := congrArg (fun p => p.1.1) hk
    simp only [smul_def, actSet_fst, h4] at h3
    exact h3.symm
  apply Subtype.ext
  ext i j
  have := congrFun (key (Pi.single j 1)) i
  simp only [Matrix.mulVec_single, mul_one] at this
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
  by_cases hij : i = j <;> simp_all [Pi.single_apply]

theorem tv_elementary {i j : Fin 6} (hij : i ≠ j) :
    ∃ k : Fin 1953, tvSL k = Matrix.SpecialLinearGroup.transvection hij (1 : ZMod 2) := by
  have hne : ∀ a : Fin 6, (Pi.single a (1 : ZMod 2) : Fin 6 → ZMod 2) ≠ 0 := fun a h => by
    have := congrFun h a
    simp at this
  obtain ⟨k, hk⟩ := tvToSet_surjective
    (⟨(Pi.single i 1, Pi.single j 1), hne i, hne j, by
      rw [dotProduct_single, mul_one]; simp [Pi.single_apply, Ne.symm hij]⟩ : TvSet)
  refine ⟨k, Subtype.ext ?_⟩
  have hv : tvVec k = Pi.single i 1 := congrArg (fun q => q.1.1) hk
  have hφ : tvForm k = Pi.single j 1 := congrArg (fun q => q.1.2) hk
  rw [coe_tvSL, Matrix.SpecialLinearGroup.transvection_coe]
  unfold tvMatrix
  rw [hv, hφ]
  congr 1
  ext a b
  simp [vecMulVec_apply, Matrix.single_apply, Pi.single_apply]
  by_cases hb : b = j <;> by_cases ha : a = i
  · subst hb
    subst ha
    simp
  · subst hb
    simp [ha, Ne.symm ha]
  · subst ha
    simp [hb, Ne.symm hb]
  · simp [hb, ha, Ne.symm ha, Ne.symm hb]

theorem closure_range_tvSL : Subgroup.closure (Set.range tvSL) = ⊤ :=
  eq_top_of_elementary _ fun _ _ hij => Subgroup.subset_closure (tv_elementary hij)

theorem tvP_injective : Function.Injective tvP := fun k l h =>
  tvSL_injective (actPerm_injective h)

end Certified2

end CFSG.GF2Type.SmithTypeE.LMod
