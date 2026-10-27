module

public import CFSG.GroupTheory.SymmetricFiveTranspositions
public import CFSG.Timmesfeld.Transvection.QTwoThin

public section

namespace CFSG.Fischer.Classification

open CFSG.Open CFSG.GroupTheory Matrix QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def stdQ : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2) :=
  QuadraticMap.ofPolar (fun x => x 0 + x 0 * x 1 + x 1 + x 2 * x 3)
    (by
      intro a x
      rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one a with rfl | rfl <;> simp)
    (by
      intro x y z
      simp only [QuadraticMap.polar, Pi.add_apply]
      ring)
    (by
      intro a x y
      rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one a with rfl | rfl <;>
        simp [QuadraticMap.polar, Pi.add_apply])

@[simp]
theorem stdQ_apply (x : Fin 4 → ZMod 2) :
    stdQ x = x 0 + x 0 * x 1 + x 1 + x 2 * x 3 := rfl

theorem stdQ_nondegenerate :
    ∀ x : Fin 4 → ZMod 2, (∀ y, polar stdQ x y = 0) → x = 0 := by
  decide +kernel

@[expose] def isoVec : Fin 5 → (Fin 4 → ZMod 2)
  | 0 => ![0, 0, 0, 1]
  | 1 => ![0, 0, 1, 0]
  | 2 => ![0, 1, 1, 1]
  | 3 => ![1, 0, 1, 1]
  | 4 => ![1, 1, 1, 1]

theorem isoVec_injective : Function.Injective isoVec := by
  decide +kernel

theorem stdQ_isoVec (i : Fin 5) : stdQ (isoVec i) = 0 := by
  fin_cases i <;> decide +kernel

theorem mem_range_isoVec_of_isotropic {v : Fin 4 → ZMod 2}
    (hv : stdQ v = 0) (hv0 : v ≠ 0) : v ∈ Set.range isoVec := by
  revert v
  decide +kernel

theorem span_isoVec : Submodule.span (ZMod 2) (Set.range isoVec) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h0 : (![1, 0, 0, 0] : Fin 4 → ZMod 2) ∈
      Submodule.span (ZMod 2) (Set.range isoVec) := by
    have h : (![1, 0, 0, 0] : Fin 4 → ZMod 2) =
        isoVec 3 + isoVec 1 + isoVec 0 := by decide +kernel
    rw [h]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.subset_span ⟨3, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩))
      (Submodule.subset_span ⟨0, rfl⟩)
  have h1 : (![0, 1, 0, 0] : Fin 4 → ZMod 2) ∈
      Submodule.span (ZMod 2) (Set.range isoVec) := by
    have h : (![0, 1, 0, 0] : Fin 4 → ZMod 2) =
        isoVec 2 + isoVec 1 + isoVec 0 := by decide +kernel
    rw [h]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.subset_span ⟨2, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩))
      (Submodule.subset_span ⟨0, rfl⟩)
  have h2 : (![0, 0, 1, 0] : Fin 4 → ZMod 2) ∈
      Submodule.span (ZMod 2) (Set.range isoVec) :=
    Submodule.subset_span ⟨1, rfl⟩
  have h3 : (![0, 0, 0, 1] : Fin 4 → ZMod 2) ∈
      Submodule.span (ZMod 2) (Set.range isoVec) :=
    Submodule.subset_span ⟨0, rfl⟩
  have hx : x = x 0 • (![1, 0, 0, 0] : Fin 4 → ZMod 2) +
      x 1 • (![0, 1, 0, 0] : Fin 4 → ZMod 2) +
      x 2 • (![0, 0, 1, 0] : Fin 4 → ZMod 2) +
      x 3 • (![0, 0, 0, 1] : Fin 4 → ZMod 2) := by
    funext i
    fin_cases i <;> simp
  rw [hx]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ h0) (Submodule.smul_mem _ _ h1))
    (Submodule.smul_mem _ _ h2)) (Submodule.smul_mem _ _ h3)

abbrev isomGroup (Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)) :
    Subgroup (GL (Fin 4) (ZMod 2)) :=
  fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x)

abbrev transvectionSet (Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)) :
    Set (isomGroup Q) :=
  {g | (g : GL (Fin 4) (ZMod 2)) ∈
    fischerTransvections (polar Q) (fun v => Q v = 1)}

abbrev O4m : Subgroup (GL (Fin 4) (ZMod 2)) := isomGroup stdQ

abbrev transvectionsO4m : Set O4m := transvectionSet stdQ

theorem orthTransvectionGL_mem_isomGroup {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    {v : Fin 4 → ZMod 2} (hv : Q v = 1) :
    orthTransvectionGL Q v ∈ isomGroup Q :=
  fischerTransvections_polar_subset (orthTransvectionGL_mem_fischerTransvections hv)

theorem mem_transvectionSet_iff (Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2))
    (g : isomGroup Q) :
    g ∈ transvectionSet Q ↔ ∃ v, Q v = 1 ∧ (g : GL (Fin 4) (ZMod 2)) = orthTransvectionGL Q v := by
  constructor
  · intro hg
    exact eq_orthTransvectionGL_of_mem_fischerTransvections hg
  · rintro ⟨v, hv, hgv⟩
    change (g : GL (Fin 4) (ZMod 2)) ∈
      fischerTransvections (polar Q) (fun v => Q v = 1)
    rw [hgv]
    exact orthTransvectionGL_mem_fischerTransvections hv

theorem transvectionSet_stdQ : transvectionSet stdQ = transvectionsO4m := by
  unfold transvectionsO4m
  rfl

theorem GL_mulVec_mul (A B : GL (Fin 4) (ZMod 2)) (x : Fin 4 → ZMod 2) :
    (((A * B : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        ((B : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

theorem GL_mulVec_inv_mul (A : GL (Fin 4) (ZMod 2)) (x : Fin 4 → ZMod 2) :
    (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)) = x := by
  rw [Matrix.mulVec_mulVec]
  change (((A⁻¹ * A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = x
  have h : ((A⁻¹ * A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [show A⁻¹ * A = (1 : GL (Fin 4) (ZMod 2)) from inv_mul_cancel A, Units.val_one]
  rw [h, Matrix.one_mulVec]

theorem GL_mulVec_mul_inv (A : GL (Fin 4) (ZMod 2)) (x : Fin 4 → ZMod 2) :
    ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
      (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)) = x := by
  rw [Matrix.mulVec_mulVec]
  change (((A * A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = x
  have h : ((A * A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    rw [show A * A⁻¹ = (1 : GL (Fin 4) (ZMod 2)) from mul_inv_cancel A, Units.val_one]
  rw [h, Matrix.one_mulVec]

theorem O4m_isometry (A : O4m) :
    ∀ x, stdQ (((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) =
      stdQ x :=
  (mem_fischerMatrixGroup_isometry_iff stdQ (A : GL (Fin 4) (ZMod 2))).mp A.2

theorem isoVec_ne_zero (i : Fin 5) : isoVec i ≠ 0 := by
  fin_cases i <;> decide +kernel

noncomputable def actIndex (A : O4m) (i : Fin 5) : Fin 5 :=
  Classical.choose (mem_range_isoVec_of_isotropic
    (by simpa using (O4m_isometry A (isoVec i)).trans (stdQ_isoVec i))
    (by
      intro h
      have h0 : isoVec i = 0 := by
        have := congrArg (fun y =>
          (((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))⁻¹) *ᵥ y) h
        simpa [GL_mulVec_inv_mul] using this
      exact isoVec_ne_zero i h0))

theorem actIndex_spec (A : O4m) (i : Fin 5) :
    ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec i =
      isoVec (actIndex A i) :=
  (Classical.choose_spec (mem_range_isoVec_of_isotropic
    (by simpa using (O4m_isometry A (isoVec i)).trans (stdQ_isoVec i))
    (by
      intro h
      have h0 : isoVec i = 0 := by
        have := congrArg (fun y =>
          (((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))⁻¹) *ᵥ y) h
        simpa [GL_mulVec_inv_mul] using this
      exact isoVec_ne_zero i h0))).symm

theorem actIndex_injective (A : O4m) : Function.Injective (actIndex A) := by
  intro i j hij
  apply isoVec_injective
  have hi := actIndex_spec A i
  have hj := actIndex_spec A j
  have h : ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec i =
      ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec j := by
    rw [hi, hj, hij]
  have := congrArg (fun y =>
    (((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))⁻¹) *ᵥ y) h
  simpa [GL_mulVec_inv_mul] using this

noncomputable def actO4m : O4m →* Equiv.Perm (Fin 5) where
  toFun A := Equiv.ofBijective (actIndex A) (actIndex_injective A).bijective_of_finite
  map_one' := by
    apply Equiv.ext
    intro i
    simp only [Equiv.ofBijective_apply, Equiv.Perm.coe_one, id_eq]
    refine isoVec_injective ?_
    rw [← actIndex_spec]
    simp
  map_mul' A B := by
    apply Equiv.ext
    intro i
    simp only [Equiv.ofBijective_apply, Equiv.Perm.mul_apply]
    refine isoVec_injective ?_
    rw [← actIndex_spec (A * B) i, ← actIndex_spec A (actIndex B i), ← actIndex_spec B i]
    simp [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]

theorem actO4m_spec (A : O4m) (i : Fin 5) :
    ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec i =
      isoVec (actO4m A i) := by
  change ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec i =
    isoVec (actIndex A i)
  exact actIndex_spec A i

theorem actO4m_injective : Function.Injective actO4m := by
  intro A B h
  have hfix : ∀ i : Fin 5,
      ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec i =
        ((B : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ isoVec i := by
    intro i
    rw [actO4m_spec A i, actO4m_spec B i, h]
  have hlin : Matrix.mulVecLin ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      Matrix.mulVecLin ((B : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    apply LinearMap.ext_on (s := Set.range isoVec) span_isoVec
    rintro _ ⟨i, rfl⟩
    exact hfix i
  have hmat : ((A : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      ((B : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    ext i j
    have hsingle := congrFun (congrArg (fun f => f (Pi.single j 1)) hlin) i
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Matrix.col_apply] using hsingle
  exact Subtype.ext (Units.ext hmat)

theorem mem_fischerTransvections_stdQ_iff (g : GL (Fin 4) (ZMod 2)) :
    g ∈ fischerTransvections (polar stdQ) (fun v => stdQ v = 1) ↔
      ∃ v, stdQ v = 1 ∧ g = orthTransvectionGL stdQ v := by
  constructor
  · exact eq_orthTransvectionGL_of_mem_fischerTransvections
  · rintro ⟨v, hv, hgv⟩
    rw [show (g : GL (Fin 4) (ZMod 2)) = orthTransvectionGL stdQ v from hgv]
    exact orthTransvectionGL_mem_fischerTransvections hv

theorem orthTransvectionGL_mem_O4m {v : Fin 4 → ZMod 2} (hv : stdQ v = 1) :
    orthTransvectionGL stdQ v ∈ O4m :=
  fischerTransvections_polar_subset (orthTransvectionGL_mem_fischerTransvections hv)

theorem actO4m_transvection_apply_eq_iff {v : Fin 4 → ZMod 2} (hv : stdQ v = 1) (i : Fin 5) :
    actO4m ⟨orthTransvectionGL stdQ v, orthTransvectionGL_mem_O4m hv⟩ i = i ↔
      polar stdQ (isoVec i) v = 0 := by
  constructor
  · intro h
    have hspec := actO4m_spec ⟨orthTransvectionGL stdQ v, orthTransvectionGL_mem_O4m hv⟩ i
    rw [orthTransvectionGL_mulVec hv] at hspec
    rw [h] at hspec
    have hB : polar stdQ (isoVec i) v • v = 0 := by
      have h1 : isoVec i + polar stdQ (isoVec i) v • v = isoVec i + 0 := by
        rw [add_zero]
        exact hspec
      exact add_left_cancel h1
    rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one
      (polar stdQ (isoVec i) v) with h0 | h1
    · exact h0
    · rw [h1, one_smul] at hB
      have hv0 : v ≠ 0 := by
        rintro rfl
        rw [QuadraticMap.map_zero] at hv
        exact zero_ne_one hv
      exact absurd hB hv0
  · intro hB
    refine isoVec_injective ?_
    rw [← actO4m_spec, orthTransvectionGL_mulVec hv]
    have hzero : ∀ (c : ZMod 2), c = 0 → isoVec i + c • v = isoVec i := by
      intro c hc
      rw [hc, zero_smul, add_zero]
    exact hzero _ hB

theorem card_isoVec_orthogonal (v : Fin 4 → ZMod 2) (hv : stdQ v = 1) :
    (Finset.univ.filter (fun i : Fin 5 => polar stdQ (isoVec i) v = 0)).card = 3 := by
  revert v
  decide +kernel

theorem support_actO4m_transvection {v : Fin 4 → ZMod 2} (hv : stdQ v = 1) :
    (actO4m ⟨orthTransvectionGL stdQ v, orthTransvectionGL_mem_O4m hv⟩).support =
      Finset.univ \ Finset.univ.filter (fun i : Fin 5 => polar stdQ (isoVec i) v = 0) := by
  ext i
  rw [Equiv.Perm.mem_support]
  rw [ne_eq, actO4m_transvection_apply_eq_iff hv i]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]

theorem card_support_actO4m_transvection {v : Fin 4 → ZMod 2} (hv : stdQ v = 1) :
    (actO4m ⟨orthTransvectionGL stdQ v, orthTransvectionGL_mem_O4m hv⟩).support.card = 2 := by
  rw [support_actO4m_transvection hv,
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    card_isoVec_orthogonal v hv]
  decide

theorem isSwap_actO4m_transvection {v : Fin 4 → ZMod 2} (hv : stdQ v = 1) :
    (actO4m ⟨orthTransvectionGL stdQ v, orthTransvectionGL_mem_O4m hv⟩).IsSwap := by
  rw [← Equiv.Perm.card_support_eq_two]
  exact card_support_actO4m_transvection hv

theorem card_stdQ_one : Fintype.card {v : Fin 4 → ZMod 2 // stdQ v = 1} = 10 := by
  decide +kernel

noncomputable def tvPerm (v : {v : Fin 4 → ZMod 2 // stdQ v = 1}) : Equiv.Perm (Fin 5) :=
  actO4m ⟨orthTransvectionGL stdQ v.1, orthTransvectionGL_mem_O4m v.2⟩

theorem tvPerm_injective : Function.Injective tvPerm := by
  intro v w h
  have h' : (⟨orthTransvectionGL stdQ v.1, orthTransvectionGL_mem_O4m v.2⟩ : O4m) =
      ⟨orthTransvectionGL stdQ w.1, orthTransvectionGL_mem_O4m w.2⟩ :=
    actO4m_injective h
  have hv : orthTransvectionGL stdQ v.1 = orthTransvectionGL stdQ w.1 := by
    simpa using congrArg (fun x : O4m => (x : GL (Fin 4) (ZMod 2))) h'
  apply Subtype.ext
  exact CFSG.Timmesfeld.Transvection.QTwo.eq_of_tv_eq stdQ_nondegenerate v.2 w.2 hv

theorem tvPerm_isSwap (v : {v : Fin 4 → ZMod 2 // stdQ v = 1}) : (tvPerm v).IsSwap :=
  isSwap_actO4m_transvection v.2

theorem transvections_act_swaps :
    actO4m '' transvectionsO4m = transpositions := by
  have hrange : Set.range tvPerm = actO4m '' transvectionsO4m := by
    ext σ
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨orthTransvectionGL stdQ v.1, orthTransvectionGL_mem_O4m v.2⟩,
        orthTransvectionGL_mem_fischerTransvections v.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      change (g : GL (Fin 4) (ZMod 2)) ∈
        fischerTransvections (polar stdQ) (fun v => stdQ v = 1) at hg
      rw [mem_fischerTransvections_stdQ_iff] at hg
      obtain ⟨v, hv, hgv⟩ := hg
      refine ⟨⟨v, hv⟩, ?_⟩
      have hg' : g = ⟨orthTransvectionGL stdQ v, orthTransvectionGL_mem_O4m hv⟩ :=
        Subtype.ext hgv
      rw [hg']
      simp [tvPerm]
  have hcard_range : (Set.range tvPerm).ncard = 10 := by
    rw [Set.ncard_range_of_injective tvPerm_injective, Nat.card_eq_fintype_card, card_stdQ_one]
  have hcard_transpositions : transpositions.ncard = 10 := by
    rw [← Nat.card_coe_set_eq]
    exact card_transpositions
  have hsubset : Set.range tvPerm ⊆ transpositions := by
    rintro _ ⟨v, rfl⟩
    exact tvPerm_isSwap v
  rw [← hrange]
  exact Set.eq_of_subset_of_ncard_le hsubset (by rw [hcard_transpositions, hcard_range])

theorem actO4m_surjective : Function.Surjective actO4m := by
  have htop : Subgroup.closure (transpositions : Set (Equiv.Perm (Fin 5))) = ⊤ :=
    Equiv.Perm.closure_isSwap
  have hclosure : Subgroup.closure (transpositions : Set (Equiv.Perm (Fin 5))) ≤ actO4m.range := by
    rw [Subgroup.closure_le]
    intro σ hσ
    rw [← transvections_act_swaps] at hσ
    obtain ⟨g, -, rfl⟩ := hσ
    exact ⟨g, rfl⟩
  rw [htop] at hclosure
  intro σ
  simpa [MonoidHom.mem_range] using hclosure (Subgroup.mem_top σ)

theorem exists_equiv_s5_of_std :
    ∃ e : O4m ≃* Equiv.Perm (Fin 5), e '' transvectionsO4m = transpositions := by
  have hbij : Function.Bijective actO4m := ⟨actO4m_injective, actO4m_surjective⟩
  exact ⟨MulEquiv.ofBijective actO4m hbij, transvections_act_swaps⟩

theorem polar_of_isometry {A : GL (Fin 4) (ZMod 2)}
    {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hA : ∀ x, stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = Q x)
    (x y : Fin 4 → ZMod 2) :
    polar stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)
      ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) = polar Q x y := by
  rw [QuadraticMap.polar, QuadraticMap.polar, ← Matrix.mulVec_add, hA, hA, hA]

theorem conj_orthTransvectionGL {A : GL (Fin 4) (ZMod 2)}
    {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hA : ∀ x, stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = Q x)
    {v : Fin 4 → ZMod 2} (hv : Q v = 1) :
    A * orthTransvectionGL Q v * A⁻¹ =
      orthTransvectionGL stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) := by
  have hstd : stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) = 1 := by
    rw [hA v, hv]
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro j
  set x : Fin 4 → ZMod 2 := Pi.single j 1
  have hL : (((A * orthTransvectionGL Q v * A⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) =
      x + polar stdQ x ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) •
        ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) := by
    rw [GL_mulVec_mul, GL_mulVec_mul]
    rw [orthTransvectionGL_mulVec hv]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [GL_mulVec_mul_inv]
    have hpolar : polar Q (((A⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) v =
        polar stdQ x ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) := by
      rw [← polar_of_isometry hA (((A⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) v]
      rw [GL_mulVec_mul_inv]
    congr 2
  have hR : (((orthTransvectionGL stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) :
        GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) =
      x + polar stdQ x ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) •
        ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) := by
    rw [orthTransvectionGL_mulVec hstd]
    rfl
  exact hL.trans hR.symm

theorem linearIndependent_of_dual_pairing {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v w : ι → V} (h : ∀ i j, B (v i) (w j) = if i = j then (1 : K) else 0) :
    LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hsum : (∑ i, c i * B (v i) (w j)) = 0 := by
    have := congrArg (fun x => B x (w j)) hc
    simpa [map_sum, map_smul, smul_eq_mul, Finset.sum_apply] using this
  rw [Finset.sum_eq_single j] at hsum
  · rw [h j j, if_pos rfl, mul_one] at hsum
    exact hsum
  · intro i _ hij
    rw [h i j, if_neg hij, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem exists_isometry_stdQ {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hno : ¬ ∃ W : Submodule (ZMod 2) (Fin 4 → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ∃ A : GL (Fin 4) (ZMod 2), ∀ x, stdQ (A *ᵥ x) = Q x := by
  classical
  let B : LinearMap.BilinForm (ZMod 2) (Fin 4 → ZMod 2) := QuadraticMap.polarBilin Q
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
  have hself : ∀ x, B x x = 0 := fun x => by
    simp only [B, QuadraticMap.polarBilin_apply_apply]
    exact CFSG.Timmesfeld.Transvection.QTwo.polar_self_zmod_two (Q := Q) x
  have hBnd : B.Nondegenerate := by
    have hbalt : B.IsAlt := fun x => by
      simpa [B, QuadraticMap.polarBilin_apply_apply] using
        CFSG.Timmesfeld.Transvection.QTwo.polar_self_zmod_two (Q := Q) x
    have hsep : B.SeparatingLeft := by
      intro x hx
      exact hnd x fun y => by
        simpa [B, QuadraticMap.polarBilin_apply_apply] using hx y
    exact (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hbalt.isRefl).mpr hsep
  have hdimV : Module.finrank (ZMod 2) (Fin 4 → ZMod 2) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hex1 : ∃ e1 : Fin 4 → ZMod 2, Q e1 = 1 := by
    by_contra h
    push Not at h
    have hzero : ∀ x, Q x = 0 := fun x => by
      rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one (Q x) with h0 | h1
      · exact h0
      · exact absurd h1 (h x)
    have hBzero : ∀ x y, B x y = 0 := by
      intro x y
      simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
        hzero (x + y), hzero x, hzero y]
      decide
    have hne : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    exact hne (hnd _ (by
      intro y
      simpa [B, QuadraticMap.polarBilin_apply_apply] using hBzero (Pi.single 0 1) y))
  obtain ⟨e1, he1⟩ := hex1
  have he1_ne : e1 ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at he1
    exact zero_ne_one he1
  let W : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
    B.orthogonal (Submodule.span (ZMod 2) ({e1} : Set (Fin 4 → ZMod 2)))
  have hWdim : Module.finrank (ZMod 2) W = 3 := by
    simp only [W, LinearMap.BilinForm.finrank_orthogonal hBnd, hdimV,
      finrank_span_singleton he1_ne]
  obtain ⟨e2W, he2W_ne, he2W_Q⟩ :=
    CFSG.ClassicalGroups.Orthogonal.exists_ne_zero_map_eq_zero
      (Q := Q.restrict W) (by rw [hWdim])
  let e2 : Fin 4 → ZMod 2 := e2W
  have he2_W : e2 ∈ W := e2W.2
  have he2_ne : e2 ≠ 0 := by
    intro h
    exact he2W_ne (Subtype.ext h)
  have he2_Q : Q e2 = 0 := by
    simpa [e2] using he2W_Q
  have he1e2 : B e1 e2 = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp he2_W) e1 (Submodule.mem_span_singleton_self e1)
  have he2e1 : B e2 e1 = 0 := by rw [hsymm, he1e2]
  have he2_not_mem : e2 ∉ Submodule.span (ZMod 2) ({e1} : Set (Fin 4 → ZMod 2)) := by
    intro h
    rw [Submodule.mem_span_singleton] at h
    obtain ⟨a, ha⟩ := h
    rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact he2_ne ha.symm
    · rw [one_smul] at ha
      have : Q e2 = Q e1 := by rw [← ha]
      rw [he2_Q, he1] at this
      exact zero_ne_one this
  have hli12 : LinearIndependent (ZMod 2) ![e1, e2] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one b with hb | hb
    · subst hb
      have ha : a = 0 := by
        rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one a with ha | ha
        · exact ha
        · subst ha
          rw [one_smul, zero_smul, add_zero] at hab
          exact absurd hab he1_ne
      exact ⟨ha, rfl⟩
    · subst hb
      rw [one_smul] at hab
      have he2span : e2 ∈ Submodule.span (ZMod 2) ({e1} : Set (Fin 4 → ZMod 2)) := by
        rw [Submodule.mem_span_singleton]
        refine ⟨a, ?_⟩
        have h' : e2 + a • e1 = 0 := by
          have := congrArg (fun x => x + a • e1) hab
          simpa [add_assoc, CFSG.Timmesfeld.Transvection.QTwo.add_self_zmod_two] using this
        have h'' := congrArg (fun x => x + a • e1) h'
        simpa [add_assoc, CFSG.Timmesfeld.Transvection.QTwo.add_self_zmod_two] using h''.symm
      exact absurd he2span he2_not_mem
  obtain ⟨e3', he3'⟩ :=
    CFSG.Timmesfeld.Transvection.QTwo.exists_pairings_of_nondeg
      (B := B) hsymm (fun x hx => hnd x (by
        simpa [B, QuadraticMap.polarBilin_apply_apply] using hx))
      (w := ![e1, e2]) hli12 ![0, 1]
  have he3'_e1' : B e3' e1 = 0 := by simpa using he3' 0
  have he3'_e2' : B e3' e2 = 1 := by simpa using he3' 1
  have he3'_e2polar : polar Q e3' e2 = 1 := by
    simpa [B, QuadraticMap.polarBilin_apply_apply] using he3'_e2' 
  let e3 : Fin 4 → ZMod 2 := if Q e3' = 0 then e3' else e3' + e2
  have he3_Q : Q e3 = 0 := by
    by_cases h : Q e3' = 0
    · simp [e3, h]
    · have h1 : Q e3' = 1 := by
        rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one (Q e3') with h0 | h1
        · exact absurd h0 h
        · exact h1
      simp only [e3, if_neg h]
      rw [QuadraticMap.map_add Q, h1, he2_Q, he3'_e2polar]
      decide
  have he3_e1 : B e3 e1 = 0 := by
    by_cases h : Q e3' = 0
    · simp [e3, h, he3'_e1']
    · simp only [e3, if_neg h]
      rw [map_add, LinearMap.add_apply, he3'_e1', he2e1, add_zero]
  have he3_e2 : B e3 e2 = 1 := by
    by_cases h : Q e3' = 0
    · simp [e3, h, he3'_e2']
    · simp only [e3, if_neg h]
      rw [map_add, LinearMap.add_apply, he3'_e2', hself e2, add_zero]
  have he3_not_mem : e3 ∉ Submodule.span (ZMod 2) ({e1, e2} : Set (Fin 4 → ZMod 2)) := by
    intro h
    rw [Submodule.mem_span_pair] at h
    obtain ⟨a, b, hst⟩ := h
    have hB : B e3 e2 = 0 := by
      simp only [← hst, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, he1e2, hself e2, mul_zero, add_zero]
    rw [he3_e2] at hB
    exact one_ne_zero hB
  have hli123 : LinearIndependent (ZMod 2) ![e1, e2, e3] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc2 : c 2 = 0 := by
      have hsum : B (c 0 • e1 + c 1 • e2 + c 2 • e3) e2 =
          c 0 * B e1 e2 + c 1 * B e2 e2 + c 2 * B e3 e2 := by
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul]
      have h := congrArg (fun x => B x e2) hc
      rw [Fin.sum_univ_three] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h
      rw [hsum] at h
      simp only [he1e2, hself e2, he3_e2, mul_zero, mul_one, add_zero, zero_add] at h
      simpa using h
    have hc1 : c 1 = 0 := by
      have hsum : B (c 0 • e1 + c 1 • e2 + c 2 • e3) e3 =
          c 0 * B e1 e3 + c 1 * B e2 e3 + c 2 * B e3 e3 := by
        simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul]
      have h := congrArg (fun x => B x e3) hc
      rw [Fin.sum_univ_three] at h
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h
      rw [hsum] at h
      simp only [hsymm e1 e3, he3_e1, hsymm e2 e3, he3_e2, hself e3, mul_zero,
        mul_one, add_zero, zero_add] at h
      simpa using h
    have hc0 : c 0 = 0 := by
      have h : c 0 • e1 = 0 := by
        simpa [Fin.sum_univ_three, hc1, hc2] using hc
      rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one (c 0) with h0 | h0
      · exact h0
      · rw [h0, one_smul] at h
        exact absurd h he1_ne
    intro i
    fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  obtain ⟨e0, he0⟩ :=
    CFSG.Timmesfeld.Transvection.QTwo.exists_pairings_of_nondeg
      (B := B) hsymm (fun x hx => hnd x (by
        simpa [B, QuadraticMap.polarBilin_apply_apply] using hx))
      (w := ![e1, e2, e3]) hli123 ![1, 0, 0]
  have he0_e1' : B e0 e1 = 1 := by simpa using he0 0
  have he0_e2' : B e0 e2 = 0 := by simpa using he0 1
  have he0_e3' : B e0 e3 = 0 := by simpa using he0 2
  have he0_e2polar : polar Q e0 e2 = 0 := by
    simpa [B, QuadraticMap.polarBilin_apply_apply] using he0_e2' 
  have he0_Q : Q e0 = 1 := by
    rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one (Q e0) with h0 | h1
    · exfalso
      have he0e2_Q : Q (e0 + e2) = 0 := by
        rw [QuadraticMap.map_add Q, h0, he2_Q, he0_e2polar]
        decide
      have hB0 : B e0 (e0 + e2) = 0 := by
        rw [map_add, hself e0, he0_e2', add_zero]
      have hli : LinearIndependent (ZMod 2) ![e0, e0 + e2] := by
        rw [LinearIndependent.pair_iff]
        intro a b hab
        have hBsum : B (e0 + e2) e1 = 1 := by
          rw [map_add, LinearMap.add_apply, he0_e1', he2e1]
          decide
        have hpair := congrArg (fun x => B x e1) hab
        simp only [map_add, map_smul, map_zero] at hpair
        rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one a with ha | ha <;>
          rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one b with hb | hb
        · exact ⟨ha, hb⟩
        · exfalso
          have h : e0 + e2 = 0 := by simpa [ha, hb] using hab
          have : B (e0 + e2) e1 = 0 := by rw [h]; simp
          rw [hBsum] at this
          exact one_ne_zero this
        · exfalso
          have h : e0 = 0 := by simpa [ha, hb] using hab
          have : B e0 e1 = 0 := by rw [h]; simp
          rw [he0_e1'] at this
          exact one_ne_zero this
        · exfalso
          rw [ha, hb, one_smul, one_smul] at hab
          rw [← add_assoc, CFSG.Timmesfeld.Transvection.QTwo.add_self_zmod_two,
            zero_add] at hab
          exact he2_ne hab
      let W' : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
        Submodule.span (ZMod 2) ({e0, e0 + e2} : Set (Fin 4 → ZMod 2))
      have hW'dim : Module.finrank (ZMod 2) W' = 2 := by
        have hspan : Submodule.span (ZMod 2) (Set.range ![e0, e0 + e2]) = W' := by
          change Submodule.span (ZMod 2) (Set.range ![e0, e0 + e2]) =
            Submodule.span (ZMod 2) ({e0, e0 + e2} : Set (Fin 4 → ZMod 2))
          congr 1
          ext x
          simp [Set.range, eq_comm]
        rw [← hspan]
        exact finrank_span_eq_card hli
      have hW'Q : ∀ w ∈ W', Q w = 0 := by
        intro w hw
        change w ∈ Submodule.span (ZMod 2) ({e0, e0 + e2} : Set (Fin 4 → ZMod 2)) at hw
        rw [Submodule.mem_span_pair] at hw
        obtain ⟨a, b, hst⟩ := hw
        rw [← hst]
        rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one a with ha | ha <;>
          rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one b with hb | hb <;>
          subst ha <;> subst hb
        · simp
        · simpa using he0e2_Q
        · simpa using h0
        · simpa only [one_smul, ← add_assoc,
            CFSG.Timmesfeld.Transvection.QTwo.add_self_zmod_two, zero_add] using he2_Q
      exact hno ⟨W', hW'dim, hW'Q⟩
    · exact h1
  have he1e0 : B e1 e0 = 1 := by rw [hsymm, he0_e1']
  have he1e3 : B e1 e3 = 0 := by rw [hsymm, he3_e1]
  have he2e0 : B e2 e0 = 0 := by rw [hsymm, he0_e2']
  have he3e0 : B e3 e0 = 0 := by rw [hsymm, he0_e3']
  have he2e3 : B e2 e3 = 1 := by rw [hsymm, he3_e2]
  have hli0123 : LinearIndependent (ZMod 2) ![e0, e1, e2, e3] := by
    apply linearIndependent_of_dual_pairing (B := B) (w := ![e1, e0, e3, e2])
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [he0_e1', he0_e2', he0_e3', he1e0, he1e2, he1e3, he2e0, he2e1, he2e3,
        he3e0, he3_e1, he3_e2, hself, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  let v : Fin 4 → (Fin 4 → ZMod 2) := ![e0, e1, e2, e3]
  let f : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    Fintype.linearCombination (ZMod 2) v
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hzero : f (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hsum : (∑ i, (x - y) i • v i) = 0 := by
      simpa [f, Fintype.linearCombination_apply] using hzero
    have hc : (x - y) = 0 := by
      funext i
      exact (Fintype.linearIndependent_iff.mp hli0123) (x - y) (by simpa [v] using hsum) i
    exact sub_eq_zero.mp hc
  let e : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    LinearEquiv.ofInjectiveEndo f hf_inj
  let A : GL (Fin 4) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin).symm
      (LinearMap.GeneralLinearGroup.ofLinearEquiv e.symm)
  have hA_apply : ∀ x, (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x = e.symm x := by
    intro x
    change (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv x = e.symm x
    simp [A]
  refine ⟨A, ?_⟩
  intro x
  rw [hA_apply x]
  have hxe : e (e.symm x) = x := e.apply_symm_apply x
  have hQfour : ∀ a b c d : Fin 4 → ZMod 2,
      Q (a + b + c + d) = Q a + Q b + Q c + Q d +
        polar Q a b + polar Q a c + polar Q a d +
        polar Q b c + polar Q b d + polar Q c d := by
    intro a b c d
    rw [QuadraticMap.map_add Q (a + b + c) d,
      QuadraticMap.map_add Q (a + b) c,
      QuadraticMap.map_add Q a b]
    simp only [QuadraticMap.polar_add_left]
    abel
  have hQe : ∀ y : Fin 4 → ZMod 2, Q (e y) = stdQ y := by
    intro y
    have hy : e y = ∑ i, y i • v i := by
      change f y = ∑ i, y i • v i
      rw [Fintype.linearCombination_apply]
    rw [hy]
    have hsum : (∑ i, y i • v i) = y 0 • e0 + y 1 • e1 + y 2 • e2 + y 3 • e3 := by
      simp [Fin.sum_univ_four, v]
    rw [hsum, hQfour]
    have hy0 : y 0 * y 0 = y 0 := by
      rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one (y 0) with h | h <;>
        simp [h]
    have hy1 : y 1 * y 1 = y 1 := by
      rcases CFSG.Timmesfeld.Transvection.QTwo.zmod_two_eq_zero_or_one (y 1) with h | h <;>
        simp [h]
    have hBpolar : ∀ x y, polar Q x y = B x y := fun x y =>
      (QuadraticMap.polarBilin_apply_apply Q x y).symm
    simp only [QuadraticMap.map_smul, hBpolar, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, he0_Q, he1, he2_Q, he3_Q, he0_e1', he0_e2', he0_e3', he1e2,
      he1e3, he2e3, mul_one, mul_zero, add_zero, stdQ_apply]
    rw [hy0, hy1]
    ring
  rw [← hQe (e.symm x), hxe]

theorem conj_apply_mulVec (A g : GL (Fin 4) (ZMod 2)) (x : Fin 4 → ZMod 2) :
    (((MulAut.conj A g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) =
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x)) := by
  simp only [MulAut.conj_apply, Units.val_mul, Matrix.mulVec_mulVec, mul_assoc]

theorem map_conj_isomGroup {A : GL (Fin 4) (ZMod 2)}
    {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hA : ∀ x, stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = Q x) :
    (isomGroup Q).map (MulAut.conj A).toMonoidHom = O4m := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_fischerMatrixGroup_isometry_iff]
    intro x
    have hh' : ∀ y, Q ((h : GL (Fin 4) (ZMod 2)) *ᵥ y) = Q y :=
      (mem_fischerMatrixGroup_isometry_iff Q (h : GL (Fin 4) (ZMod 2))).mp hh
    change stdQ (((MulAut.conj A h : GL (Fin 4) (ZMod 2)) :
      Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = stdQ x
    rw [conj_apply_mulVec]
    rw [hA, hh', ← hA, GL_mulVec_mul_inv]
  · intro hg
    have hg' : ∀ y, stdQ ((g : GL (Fin 4) (ZMod 2)) *ᵥ y) = stdQ y :=
      (mem_fischerMatrixGroup_isometry_iff stdQ (g : GL (Fin 4) (ZMod 2))).mp hg
    refine ⟨(MulAut.conj A)⁻¹ g, ?_, ?_⟩
    · change (MulAut.conj A)⁻¹ g ∈
        fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x)
      rw [mem_fischerMatrixGroup_isometry_iff]
      intro y
      rw [MulAut.conj_inv_apply]
      rw [show ((((A⁻¹ * g * A : GL (Fin 4) (ZMod 2))) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) =
          (((MulAut.conj A⁻¹ g : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y) by
        rw [MulAut.conj_apply, inv_inv]]
      rw [conj_apply_mulVec, inv_inv]
      rw [← hA (((A⁻¹ : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
          ((g : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
            ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ y)))]
      rw [GL_mulVec_mul_inv, hg', hA]
    · exact MulEquiv.apply_symm_apply _ _

noncomputable def conjIsom {A : GL (Fin 4) (ZMod 2)}
    {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hA : ∀ x, stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = Q x) :
    isomGroup Q ≃* O4m :=
  ((MulAut.conj A).subgroupMap (isomGroup Q)).trans
    (MulEquiv.subgroupCongr (map_conj_isomGroup hA))

theorem conjIsom_apply_coe {A : GL (Fin 4) (ZMod 2)}
    {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hA : ∀ x, stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = Q x)
    (g : isomGroup Q) :
    ((conjIsom hA g : O4m) : GL (Fin 4) (ZMod 2)) =
      A * (g : GL (Fin 4) (ZMod 2)) * A⁻¹ := by
  change (MulAut.conj A (g : GL (Fin 4) (ZMod 2))) =
    A * (g : GL (Fin 4) (ZMod 2)) * A⁻¹
  rw [MulAut.conj_apply]

theorem image_conj_transvectionSet {A : GL (Fin 4) (ZMod 2)}
    {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hA : ∀ x, stdQ ((A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ x) = Q x) :
    (conjIsom hA) '' transvectionSet Q = transvectionsO4m := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [mem_transvectionSet_iff] at hh
    obtain ⟨v, hv, hgv⟩ := hh
    rw [← transvectionSet_stdQ]
    rw [mem_transvectionSet_iff]
    refine ⟨(A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v, ?_, ?_⟩
    · rw [hA v, hv]
    · rw [conjIsom_apply_coe, hgv]
      exact conj_orthTransvectionGL hA hv
  · intro hg
    rw [← transvectionSet_stdQ] at hg
    rw [mem_transvectionSet_iff] at hg
    obtain ⟨w, hw, hgw⟩ := hg
    let v : Fin 4 → ZMod 2 :=
      ((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w
    have hAv : (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v = w := by
      show (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ
        (((A⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ w) = w
      rw [GL_mulVec_mul_inv]
    have hv : Q v = 1 := by
      rw [← hA v, hAv, hw]
    refine ⟨⟨orthTransvectionGL Q v, orthTransvectionGL_mem_isomGroup hv⟩,
      ?_, ?_⟩
    · rw [mem_transvectionSet_iff]
      exact ⟨v, hv, rfl⟩
    · apply Subtype.ext
      rw [conjIsom_apply_coe, conj_orthTransvectionGL hA hv, hAv, hgw]

theorem o4minus2_equiv_s5 {Q : QuadraticForm (ZMod 2) (Fin 4 → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hno : ¬ ∃ W : Submodule (ZMod 2) (Fin 4 → ZMod 2),
      Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ∃ e : isomGroup Q ≃* Equiv.Perm (Fin 5),
      e '' transvectionSet Q = transpositions := by
  obtain ⟨A, hA⟩ := exists_isometry_stdQ hnd hno
  let eQ : isomGroup Q ≃* O4m := conjIsom hA
  obtain ⟨eStd, heStd⟩ := exists_equiv_s5_of_std
  refine ⟨eQ.trans eStd, ?_⟩
  have himage : (eQ.trans eStd) '' transvectionSet Q = transpositions := by
    rw [show (eQ.trans eStd) '' transvectionSet Q =
        eStd '' (eQ '' transvectionSet Q) by
      ext σ
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨eQ g, ⟨g, hg, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨g, hg, rfl⟩]
    rw [image_conj_transvectionSet (A := A) hA, heStd]
  exact himage

end CFSG.Fischer.Classification
