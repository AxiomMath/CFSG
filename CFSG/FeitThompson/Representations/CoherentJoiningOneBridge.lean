module

public import CFSG.FeitThompson.Representations.DisjointConjugateFamiliesOrthogonalImages
import CFSG.FeitThompson.Representations.ConstantValuePuncturedSubgroupInteger
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L G : Type*} [Group L] [Group G] {X Y : Set (L → ℂ)}

omit [Group L] in
theorem exists_add_eq_of_mem_span_union {f : L → ℂ} (hf : f ∈ Submodule.span ℤ (X ∪ Y)) :
    ∃ p ∈ Submodule.span ℤ X, ∃ q ∈ Submodule.span ℤ Y, p + q = f := by
  rw [Submodule.span_union] at hf
  exact Submodule.mem_sup.1 hf

def spanAdd (X Y : Set (L → ℂ)) :
    (Submodule.span ℤ X × Submodule.span ℤ Y) →ₗ[ℤ] Submodule.span ℤ (X ∪ Y) :=
  LinearMap.codRestrict _ ((Submodule.span ℤ X).subtype.coprod (Submodule.span ℤ Y).subtype)
    fun p => by
      rw [Submodule.span_union]
      exact Submodule.add_mem_sup p.1.2 p.2.2

omit [Group L] in
@[simp] theorem coe_spanAdd_apply (p : Submodule.span ℤ X × Submodule.span ℤ Y) :
    ((spanAdd X Y p : Submodule.span ℤ (X ∪ Y)) : L → ℂ) = (p.1 : L → ℂ) + (p.2 : L → ℂ) := (rfl)

omit [Group L] in
theorem spanAdd_bijective (hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)) :
    Function.Bijective (spanAdd X Y) := by
  constructor
  · intro p q hpq
    have h : (p.1 : L → ℂ) + p.2 = (q.1 : L → ℂ) + q.2 := by
      simpa using congrArg (fun z : Submodule.span ℤ (X ∪ Y) => (z : L → ℂ)) hpq
    have hmem : (p.1 : L → ℂ) - q.1 ∈ Submodule.span ℤ X ⊓ Submodule.span ℤ Y := by
      refine ⟨(Submodule.span ℤ X).sub_mem p.1.2 q.1.2, ?_⟩
      have he : (p.1 : L → ℂ) - q.1 = (q.2 : L → ℂ) - p.2 := by
        rw [sub_eq_sub_iff_add_eq_add]; linear_combination (norm := abel) h
      rw [he]
      exact (Submodule.span ℤ Y).sub_mem q.2.2 p.2.2
    rw [disjoint_iff.1 hdisj, Submodule.mem_bot] at hmem
    have h1 : p.1 = q.1 := Subtype.ext (sub_eq_zero.1 hmem)
    have h2 : p.2 = q.2 := by
      refine Subtype.ext ?_
      rw [h1] at h
      exact add_left_cancel h
    exact Prod.ext h1 h2
  · intro f
    obtain ⟨u, hu, v, hv, huv⟩ := exists_add_eq_of_mem_span_union f.2
    exact ⟨(⟨u, hu⟩, ⟨v, hv⟩), Subtype.ext (by simpa using huv)⟩

noncomputable def spanProdEquiv (hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)) :
    (Submodule.span ℤ X × Submodule.span ℤ Y) ≃ₗ[ℤ] Submodule.span ℤ (X ∪ Y) :=
  LinearEquiv.ofBijective (spanAdd X Y) (spanAdd_bijective hdisj)

omit [Group L] in
@[simp] theorem spanProdEquiv_apply (hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y))
    (p : Submodule.span ℤ X × Submodule.span ℤ Y) :
    spanProdEquiv hdisj p = spanAdd X Y p := (rfl)

noncomputable def joinHom (νX : Submodule.span ℤ X →+ virtualChars G)
    (νY : Submodule.span ℤ Y →+ virtualChars G)
    (hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)) :
    Submodule.span ℤ (X ∪ Y) →+ virtualChars G :=
  (νX.coprod νY).comp (spanProdEquiv hdisj).symm.toAddMonoidHom

section JoinApply

variable {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
  {hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)}

omit [Group L] in
theorem joinHom_apply_add {p q : L → ℂ} (hp : p ∈ Submodule.span ℤ X)
    (hq : q ∈ Submodule.span ℤ Y) (hpq : p + q ∈ Submodule.span ℤ (X ∪ Y)) :
    joinHom νX νY hdisj ⟨p + q, hpq⟩ = νX ⟨p, hp⟩ + νY ⟨q, hq⟩ := by
  have h1 : spanProdEquiv hdisj (⟨p, hp⟩, ⟨q, hq⟩) = ⟨p + q, hpq⟩ := Subtype.ext (by simp)
  have h2 : (spanProdEquiv hdisj).symm ⟨p + q, hpq⟩ = (⟨p, hp⟩, ⟨q, hq⟩) := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  simp [joinHom, h2]

omit [Group L] in
theorem joinHom_apply_left {p : L → ℂ} (hp : p ∈ Submodule.span ℤ X)
    (hp' : p ∈ Submodule.span ℤ (X ∪ Y)) :
    joinHom νX νY hdisj ⟨p, hp'⟩ = νX ⟨p, hp⟩ := by
  have h1 : spanProdEquiv hdisj (⟨p, hp⟩, 0) = ⟨p, hp'⟩ := Subtype.ext (by simp)
  have h2 : (spanProdEquiv hdisj).symm ⟨p, hp'⟩ = (⟨p, hp⟩, 0) := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  simp [joinHom, h2]

omit [Group L] in
theorem joinHom_apply_right {q : L → ℂ} (hq : q ∈ Submodule.span ℤ Y)
    (hq' : q ∈ Submodule.span ℤ (X ∪ Y)) :
    joinHom νX νY hdisj ⟨q, hq'⟩ = νY ⟨q, hq⟩ := by
  have h1 : spanProdEquiv hdisj (0, ⟨q, hq⟩) = ⟨q, hq'⟩ := Subtype.ext (by simp)
  have h2 : (spanProdEquiv hdisj).symm ⟨q, hq'⟩ = (0, ⟨q, hq⟩) := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  simp [joinHom, h2]

end JoinApply

theorem eq_zero_of_forall_mem_span {M A : Type*} [AddCommGroup M] [AddCommGroup A]
    {S : Set M} (φ : Submodule.span ℤ S →+ A)
    (h : ∀ s : S, φ ⟨(s : M), Submodule.subset_span s.2⟩ = 0) (a : Submodule.span ℤ S) :
    φ a = 0 := by
  obtain ⟨a, ha⟩ := a
  induction ha using Submodule.span_induction with
  | mem s hs => exact h ⟨s, hs⟩
  | zero =>
    have h0 : (⟨0, Submodule.zero_mem _⟩ : Submodule.span ℤ S) = 0 := rfl
    rw [h0, map_zero]
  | add x y hx hy ihx ihy =>
    have hadd : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Submodule.span ℤ S)
        = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [hadd, map_add, ihx, ihy, add_zero]
  | smul r x hx ihx =>
    have hsm : (⟨r • x, Submodule.smul_mem _ r hx⟩ : Submodule.span ℤ S) = r • ⟨x, hx⟩ := rfl
    rw [hsm, map_zsmul, ihx, smul_zero]

section CfInnerSpan

variable {α : Type*} [Fintype α]

private theorem cfInner_zsmul_right' (n : ℤ) (f h : α → ℂ) :
    cfInner f (n • h) = (n : ℂ) * cfInner f h := by
  rw [← Int.cast_smul_eq_zsmul ℂ n h, cfInner_smul_right]
  simp

theorem cfInner_eq_zero_of_mem_span_of_mem_span {A B : Set (α → ℂ)}
    (h : ∀ u ∈ A, ∀ v ∈ B, cfInner u v = 0) {a b : α → ℂ}
    (ha : a ∈ Submodule.span ℤ A) (hb : b ∈ Submodule.span ℤ B) :
    cfInner a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => exact cfInner_zero_right u
    | add x y _ _ hx hy => rw [cfInner_add_right, hx, hy, add_zero]
    | smul r x _ hx => rw [cfInner_zsmul_right', hx, mul_zero]
  | zero => exact cfInner_zero_left b
  | add x y _ _ hx hy => rw [cfInner_add_left, hx, hy, add_zero]
  | smul r x _ hx => rw [cfInner_zsmul_left, hx, mul_zero]

end CfInnerSpan

section Ortho

variable [Fintype L]

theorem cfInner_eq_zero_of_mem_span_of_disjoint (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L)
    (hXY : Disjoint X Y) {a b : L → ℂ}
    (ha : a ∈ Submodule.span ℤ X) (hb : b ∈ Submodule.span ℤ Y) : cfInner a b = 0 :=
  cfInner_eq_zero_of_mem_span_of_mem_span
    (fun _ hu _ hv => cfInner_eq_zero_of_mem_Irr (hX hu) (hY hv)
      (fun huv => Set.disjoint_left.1 hXY hu (huv ▸ hv))) ha hb

theorem disjoint_span_span_of_disjoint (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L)
    (hXY : Disjoint X Y) : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y) := by
  rw [Submodule.disjoint_def]
  intro u hu hu'
  exact cfInner_self_eq_zero.1 (cfInner_eq_zero_of_mem_span_of_disjoint hX hY hXY hu hu')

end Ortho

section CrossImage

variable [Fintype G]

private noncomputable def cfInnerRightHom (νY : Submodule.span ℤ Y →+ virtualChars G)
    (c : G → ℂ) : Submodule.span ℤ Y →+ ℂ where
  toFun b := cfInner c (νY b : G → ℂ)
  map_zero' := by simpa using cfInner_zero_right c
  map_add' x y := by
    rw [map_add]
    simpa using cfInner_add_right c (νY x : G → ℂ) (νY y : G → ℂ)

private noncomputable def cfInnerLeftHom (νX : Submodule.span ℤ X →+ virtualChars G)
    (c : G → ℂ) : Submodule.span ℤ X →+ ℂ where
  toFun a := cfInner (νX a : G → ℂ) c
  map_zero' := by simpa using cfInner_zero_left c
  map_add' x y := by
    rw [map_add]
    simpa using cfInner_add_left (νX x : G → ℂ) (νX y : G → ℂ) c

omit [Group L] in
theorem cfInner_map_map_eq_zero {νX : Submodule.span ℤ X →+ virtualChars G}
    {νY : Submodule.span ℤ Y →+ virtualChars G}
    (h : ∀ ξ : X, ∀ η : Y, cfInner (coherentVal νX ξ) (coherentVal νY η) = 0)
    (a : Submodule.span ℤ X) (b : Submodule.span ℤ Y) :
    cfInner (νX a : G → ℂ) (νY b : G → ℂ) = 0 := by
  refine eq_zero_of_forall_mem_span (cfInnerLeftHom νX (νY b : G → ℂ)) (fun ξ => ?_) a
  refine eq_zero_of_forall_mem_span
    (cfInnerRightHom νY (νX ⟨(ξ : L → ℂ), Submodule.subset_span ξ.2⟩ : G → ℂ))
    (fun η => ?_) b
  simpa [cfInnerRightHom, coherentVal_apply] using h ξ η

end CrossImage

theorem smul_sub_smul_mem_charSpanZero {S : Set (L → ℂ)} [Fintype L] (hS : S ⊆ Irr L)
    {p ξ : L → ℂ} (hp : p ∈ Submodule.span ℤ S) (hξ : ξ ∈ S) :
    ξ 1 • p - p 1 • ξ ∈ charSpanZero S := by
  obtain ⟨d, -, hd⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr (hS hξ)
  obtain ⟨a, ha⟩ := exists_int_apply_one_of_mem_span_Irr (Submodule.span_mono hS hp)
  refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ ?_ ?_, ?_⟩
  · rw [hd, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hp d
  · rw [ha, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (Submodule.subset_span hξ) a
  · simp [mul_comm]

section Isometry

variable [Fintype L] [Fintype G]

theorem cfInner_joinHom_joinHom (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L) (hXY : Disjoint X Y)
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    {hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)}
    (hisoX : ∀ f h : Submodule.span ℤ X,
      cfInner (νX f : G → ℂ) (νX h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ))
    (hisoY : ∀ f h : Submodule.span ℤ Y,
      cfInner (νY f : G → ℂ) (νY h : G → ℂ) = cfInner (f : L → ℂ) (h : L → ℂ))
    (hcross : ∀ ξ : X, ∀ η : Y, cfInner (coherentVal νX ξ) (coherentVal νY η) = 0)
    (f h : Submodule.span ℤ (X ∪ Y)) :
    cfInner (joinHom νX νY hdisj f : G → ℂ) (joinHom νX νY hdisj h : G → ℂ)
      = cfInner (f : L → ℂ) (h : L → ℂ) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_add_eq_of_mem_span_union f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := exists_add_eq_of_mem_span_union h.2
  have hf : f = ⟨p + q, hpq ▸ f.2⟩ := Subtype.ext hpq.symm
  have hh : h = ⟨r + s, hrs ▸ h.2⟩ := Subtype.ext hrs.symm
  rw [hf, hh, joinHom_apply_add hp hq, joinHom_apply_add hr hs]
  have e1 : ((νX ⟨p, hp⟩ + νY ⟨q, hq⟩ : virtualChars G) : G → ℂ)
      = (νX ⟨p, hp⟩ : G → ℂ) + (νY ⟨q, hq⟩ : G → ℂ) := rfl
  have e2 : ((νX ⟨r, hr⟩ + νY ⟨s, hs⟩ : virtualChars G) : G → ℂ)
      = (νX ⟨r, hr⟩ : G → ℂ) + (νY ⟨s, hs⟩ : G → ℂ) := rfl
  have hqr : cfInner (νY ⟨q, hq⟩ : G → ℂ) (νX ⟨r, hr⟩ : G → ℂ) = 0 := by
    rw [← conj_cfInner, cfInner_map_map_eq_zero hcross ⟨r, hr⟩ ⟨q, hq⟩, map_zero]
  rw [e1, e2, cfInner_add_left, cfInner_add_right, cfInner_add_right,
    hisoX ⟨p, hp⟩ ⟨r, hr⟩, hisoY ⟨q, hq⟩ ⟨s, hs⟩,
    cfInner_map_map_eq_zero hcross ⟨p, hp⟩ ⟨s, hs⟩, hqr]
  have hqr' : cfInner q r = 0 := by
    rw [← conj_cfInner, cfInner_eq_zero_of_mem_span_of_disjoint hX hY hXY hr hq, map_zero]
  change _ = cfInner (p + q) (r + s)
  rw [cfInner_add_left, cfInner_add_right, cfInner_add_right,
    cfInner_eq_zero_of_mem_span_of_disjoint hX hY hXY hp hs, hqr']

end Isometry

section Zero

variable [Fintype L] [Fintype G]
variable {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
  {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
  {hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)}

theorem joinHom_eq_tau_left (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    {v : L → ℂ} (hv : v ∈ charSpanZero X) (hv' : v ∈ charSpanZero (X ∪ Y))
    (hv'' : v ∈ Submodule.span ℤ (X ∪ Y)) :
    joinHom νX νY hdisj ⟨v, hv''⟩ = τ ⟨v, hv'⟩ := by
  rw [joinHom_apply_left (charSpanZero_le X hv)]
  have h := hνX.eq_on_zero ⟨v, hv⟩
  rw [restrictBaseline_apply] at h
  exact h

theorem joinHom_eq_tau_right (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    {v : L → ℂ} (hv : v ∈ charSpanZero Y) (hv' : v ∈ charSpanZero (X ∪ Y))
    (hv'' : v ∈ Submodule.span ℤ (X ∪ Y)) :
    joinHom νX νY hdisj ⟨v, hv''⟩ = τ ⟨v, hv'⟩ := by
  rw [joinHom_apply_right (charSpanZero_le Y hv)]
  have h := hνY.eq_on_zero ⟨v, hv⟩
  rw [restrictBaseline_apply] at h
  exact h

private noncomputable def joinHomZero (νX : Submodule.span ℤ X →+ virtualChars G)
    (νY : Submodule.span ℤ Y →+ virtualChars G)
    (hdisj : Disjoint (Submodule.span ℤ X) (Submodule.span ℤ Y)) :
    charSpanZero (X ∪ Y) →+ virtualChars G :=
  (joinHom νX νY hdisj).comp
    (Submodule.inclusion (charSpanZero_le (X ∪ Y))).toAddMonoidHom

private theorem joinHomZero_apply_mk {v : L → ℂ} (hv : v ∈ charSpanZero (X ∪ Y))
    (hv' : v ∈ Submodule.span ℤ (X ∪ Y)) :
    joinHomZero νX νY hdisj ⟨v, hv⟩ = joinHom νX νY hdisj ⟨v, hv'⟩ := rfl

theorem joinHom_eq_on_charSpanZero (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L)
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    {ξ₀ η₀ : L → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y)
    {hw3 : η₀ 1 • ξ₀ - ξ₀ 1 • η₀ ∈ charSpanZero (X ∪ Y)}
    (hbridge : (τ ⟨η₀ 1 • ξ₀ - ξ₀ 1 • η₀, hw3⟩ : G → ℂ)
      = η₀ 1 • coherentVal νX ⟨ξ₀, hξ₀⟩ - ξ₀ 1 • coherentVal νY ⟨η₀, hη₀⟩)
    (f : charSpanZero (X ∪ Y)) :
    joinHom νX νY hdisj (Submodule.inclusion (charSpanZero_le (X ∪ Y)) f) = τ f := by
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_add_eq_of_mem_span_union (charSpanZero_le _ f.2)
  obtain ⟨dn, hdnpos, hdn⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr (hX hξ₀)
  obtain ⟨en, henpos, hen⟩ := NormalInducedFamily.exists_apply_one_eq_of_mem_Irr (hY hη₀)
  obtain ⟨a, hpa⟩ := exists_int_apply_one_of_mem_span_Irr (Submodule.span_mono hX hp)
  set d : ℤ := (dn : ℤ) with hddef
  set e : ℤ := (en : ℤ) with hedef
  have hd : ξ₀ 1 = (d : ℂ) := by rw [hdn, hddef]; push_cast; ring
  have he : η₀ 1 = (e : ℂ) := by rw [hen, hedef]; push_cast; ring
  have hde : (d * e) ≠ 0 := by simp only [hddef, hedef]; positivity
  have hqa : q 1 = -(a : ℂ) := by
    have h := congrArg (fun g : L → ℂ => g 1) hpq
    simp only [Pi.add_apply] at h
    rw [hpa, charSpanZero_apply_one f] at h
    linear_combination h
  have hz1 : ξ₀ 1 • p - p 1 • ξ₀ ∈ charSpanZero X := smul_sub_smul_mem_charSpanZero hX hp hξ₀
  have hz2 : η₀ 1 • q - q 1 • η₀ ∈ charSpanZero Y := smul_sub_smul_mem_charSpanZero hY hq hη₀
  have hw1 : ξ₀ 1 • p - p 1 • ξ₀ ∈ charSpanZero (X ∪ Y) :=
    FeitExtension.charSpanZero_mono Set.subset_union_left hz1
  have hw2 : η₀ 1 • q - q 1 • η₀ ∈ charSpanZero (X ∪ Y) :=
    FeitExtension.charSpanZero_mono Set.subset_union_right hz2
  set w1 : charSpanZero (X ∪ Y) := ⟨_, hw1⟩ with hw1def
  set w2 : charSpanZero (X ∪ Y) := ⟨_, hw2⟩ with hw2def
  set w3 : charSpanZero (X ∪ Y) := ⟨_, hw3⟩ with hw3def
  have hkey : (d * e) • f = e • w1 + d • w2 + a • w3 := by
    apply Subtype.ext
    push_cast [hw1def, hw2def, hw3def]
    rw [← hpq, hd, he, hpa, hqa]
    simp only [Int.cast_smul_eq_zsmul]
    module
  set φ := joinHomZero νX νY hdisj with hφdef
  have h1 : φ w1 = τ w1 := by
    rw [hφdef, hw1def, joinHomZero_apply_mk hw1 (charSpanZero_le _ hw1)]
    exact joinHom_eq_tau_left hνX hz1 hw1 _
  have h2 : φ w2 = τ w2 := by
    rw [hφdef, hw2def, joinHomZero_apply_mk hw2 (charSpanZero_le _ hw2)]
    exact joinHom_eq_tau_right hνY hz2 hw2 _
  have h3 : (φ w3 : G → ℂ) = (τ w3 : G → ℂ) := by
    rw [hw3def, hbridge, hφdef, joinHomZero_apply_mk hw3 (charSpanZero_le _ hw3)]
    have hmem1 : η₀ 1 • ξ₀ ∈ Submodule.span ℤ X := by
      rw [he, Int.cast_smul_eq_zsmul]
      exact zsmul_mem (Submodule.subset_span hξ₀) e
    have hmem2 : -(ξ₀ 1 • η₀) ∈ Submodule.span ℤ Y := by
      rw [hd, Int.cast_smul_eq_zsmul]
      exact Submodule.neg_mem _ (zsmul_mem (Submodule.subset_span hη₀) d)
    have heq : (⟨η₀ 1 • ξ₀ - ξ₀ 1 • η₀, charSpanZero_le _ hw3⟩ : Submodule.span ℤ (X ∪ Y))
        = ⟨η₀ 1 • ξ₀ + -(ξ₀ 1 • η₀), by
            rw [Submodule.span_union]; exact Submodule.add_mem_sup hmem1 hmem2⟩ :=
      Subtype.ext (by simp [sub_eq_add_neg])
    have e1 : (⟨η₀ 1 • ξ₀, hmem1⟩ : Submodule.span ℤ X)
        = e • ⟨ξ₀, Submodule.subset_span hξ₀⟩ := Subtype.ext (by simp [he, Int.cast_smul_eq_zsmul])
    have e2 : (⟨-(ξ₀ 1 • η₀), hmem2⟩ : Submodule.span ℤ Y)
        = (-d) • ⟨η₀, Submodule.subset_span hη₀⟩ :=
      Subtype.ext (by simp [hd, Int.cast_smul_eq_zsmul])
    rw [heq, joinHom_apply_add hmem1 hmem2, e1, e2, map_zsmul, map_zsmul,
      coherentVal_apply, coherentVal_apply, hd, he]
    change e • (νX ⟨ξ₀, _⟩ : G → ℂ) + (-d) • (νY ⟨η₀, _⟩ : G → ℂ) = _
    simp only [Int.cast_smul_eq_zsmul]
    module
  have hmid : (φ ((d * e) • f) : G → ℂ) = (τ ((d * e) • f) : G → ℂ) := by
    rw [hkey, map_add, map_add, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      map_zsmul, map_zsmul, map_zsmul, h1, h2]
    change ((e • τ w1 + d • τ w2 : virtualChars G) : G → ℂ) + a • (φ w3 : G → ℂ)
      = ((e • τ w1 + d • τ w2 : virtualChars G) : G → ℂ) + a • (τ w3 : G → ℂ)
    rw [h3]
  rw [map_zsmul, map_zsmul] at hmid
  have hsub : ((d * e) : ℤ) • ((φ f : G → ℂ) - (τ f : G → ℂ)) = 0 := by
    rw [smul_sub]
    change (d * e) • (φ f : G → ℂ) - (d * e) • (τ f : G → ℂ) = 0
    rw [show ((d * e) • (φ f : G → ℂ)) = (((d * e) • φ f : virtualChars G) : G → ℂ) from rfl,
      show ((d * e) • (τ f : G → ℂ)) = (((d * e) • τ f : virtualChars G) : G → ℂ) from rfl,
      hmid, sub_self]
  have hzero : (φ f : G → ℂ) - (τ f : G → ℂ) = 0 := by
    rcases smul_eq_zero.1 hsub with h | h
    · exact absurd h hde
    · exact h
  exact Subtype.ext (sub_eq_zero.1 hzero)

end Zero

section Main

variable [Fintype L] [Fintype G]

theorem isCoherentWith_joinHom
    (hX : X ⊆ Irr L) (hY : Y ⊆ Irr L) (hXY : Disjoint X Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXstar : ∀ χ ∈ X, star χ ∈ X) (hYstar : ∀ χ ∈ Y, star χ ∈ Y)
    (hXnr : ∀ χ ∈ X, star χ ≠ χ) (hYnr : ∀ χ ∈ Y, star χ ≠ χ)
    {τ : charSpanZero (X ∪ Y) →+ virtualChars G}
    (hτ1 : ∀ f : charSpanZero (X ∪ Y), (τ f : G → ℂ) 1 = 0)
    (hτiso : ∀ f g : charSpanZero (X ∪ Y),
      cfInner (τ f : G → ℂ) (τ g : G → ℂ) = cfInner (f : L → ℂ) (g : L → ℂ))
    (hτstar : ∀ f : charSpanZero (X ∪ Y),
      (τ (starCharSpanZero (star_mem_union hXstar hYstar) f) : G → ℂ) = star ((τ f : G → ℂ)))
    {νX : Submodule.span ℤ X →+ virtualChars G} {νY : Submodule.span ℤ Y →+ virtualChars G}
    (hνX : IsCoherentWith X (restrictBaseline Set.subset_union_left τ) νX)
    (hνY : IsCoherentWith Y (restrictBaseline Set.subset_union_right τ) νY)
    {ξ₀ η₀ : L → ℂ} (hξ₀ : ξ₀ ∈ X) (hη₀ : η₀ ∈ Y)
    {hw3 : η₀ 1 • ξ₀ - ξ₀ 1 • η₀ ∈ charSpanZero (X ∪ Y)}
    (hbridge : (τ ⟨η₀ 1 • ξ₀ - ξ₀ 1 • η₀, hw3⟩ : G → ℂ)
      = η₀ 1 • coherentVal νX ⟨ξ₀, hξ₀⟩ - ξ₀ 1 • coherentVal νY ⟨η₀, hη₀⟩) :
    IsCoherentWith (X ∪ Y) τ (joinHom νX νY (disjoint_span_span_of_disjoint hX hY hXY)) where
  inner_eq := cfInner_joinHom_joinHom hX hY hXY hνX.inner_eq hνY.inner_eq
    (cfInner_coherentVal_coherentVal_eq_zero_of_disjoint hX hY hXY hXne hYne hXstar hYstar
      hXnr hYnr hτ1 hτiso hτstar hνX hνY)
  eq_on_zero := joinHom_eq_on_charSpanZero hX hY hνX hνY hξ₀ hη₀ hbridge

end Main

end CFSG.FeitThompson
