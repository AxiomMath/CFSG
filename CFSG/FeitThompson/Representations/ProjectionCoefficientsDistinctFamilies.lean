module

public import CFSG.FeitThompson.Definitions.CoherentExtensionOfACharacterFamilyMap
public import CFSG.FeitThompson.Definitions.NormalInducedCharacterFamily
import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis
import CFSG.FeitThompson.Representations.NormalInducedCharactersOrthogonal

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CrossFamilyProjection

open ComplexConjugate

section InnerLemmas

variable {α : Type*} [Fintype α]

theorem cfInner_eq_zero_of_mem_span {f : α → ℂ} {E : Set (α → ℂ)}
    (hE : ∀ h ∈ E, cfInner f h = 0) {h : α → ℂ} (hh : h ∈ Submodule.span ℂ E) :
    cfInner f h = 0 := by
  induction hh using Submodule.span_induction with
  | mem x hx => exact hE x hx
  | zero => exact cfInner_zero_right f
  | add x y _ _ hx hy => rw [cfInner_add_right, hx, hy, add_zero]
  | smul c x _ hx => rw [cfInner_smul_right, hx, mul_zero]

private theorem cfInner_zsmul_right (d : ℤ) (f h : α → ℂ) :
    cfInner f (d • h) = (d : ℂ) * cfInner f h := by
  rw [← Int.cast_smul_eq_zsmul ℂ d h, cfInner_smul_right]
  simp

theorem eq_of_forall_cfInner_sub_eq_zero [Nonempty α] {M : Submodule ℂ (α → ℂ)} {f p q : α → ℂ}
    (hp : p ∈ M) (hq : q ∈ M) (hp' : ∀ h ∈ M, cfInner (f - p) h = 0)
    (hq' : ∀ h ∈ M, cfInner (f - q) h = 0) : p = q := by
  have hd : p - q ∈ M := M.sub_mem hp hq
  have key : cfInner ((f - q) - (f - p)) (p - q) = 0 := by
    rw [cfInner_sub_left, hq' _ hd, hp' _ hd, sub_self]
  have h1 : (f - q) - (f - p) = (p - q : α → ℂ) := by ring
  rw [h1] at key
  exact sub_eq_zero.1 (cfInner_self_eq_zero.1 key)

end InnerLemmas

section Family

variable {L G : Type*} [Group G] {ι : Type*} (ξ : ι → (L → ℂ))
  (ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G)

noncomputable def coherentImage (k : ι) : G → ℂ :=
  (ν ⟨ξ k, Submodule.subset_span ⟨k, rfl⟩⟩ : G → ℂ)

theorem coherentImage_apply (k : ι) :
    coherentImage ξ ν k = (ν ⟨ξ k, Submodule.subset_span ⟨k, rfl⟩⟩ : G → ℂ) := (rfl)

theorem coherentImage_mem_span (k : ι) :
    coherentImage ξ ν k ∈ Submodule.span ℂ (Set.range (coherentImage ξ ν)) :=
  Submodule.subset_span ⟨k, rfl⟩

variable [One L] [Fintype ι]

noncomputable def coherentSum (e : ℂ) : G → ℂ :=
  ∑ k, (ξ k 1 / e) • coherentImage ξ ν k

theorem coherentSum_apply (e : ℂ) :
    coherentSum ξ ν e = ∑ k, (ξ k 1 / e) • coherentImage ξ ν k := (rfl)

theorem coherentSum_mem_span (e : ℂ) :
    coherentSum ξ ν e ∈ Submodule.span ℂ (Set.range (coherentImage ξ ν)) :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (coherentImage_mem_span ξ ν k)

end Family

section Coherence

variable {L G : Type*} [Group L] [Group G] {S : Set (L → ℂ)}
  {τ : charSpanZero S →+ virtualChars G} {β : G → ℂ}

theorem forall_cfInner_eq_zero_of_disjoint_support [Fintype G] {Di Dj : Set G}
    (hβ : Function.support β ⊆ Di)
    (hτ : ∀ f : charSpanZero S, Function.support (τ f : G → ℂ) ⊆ Dj)
    (hd : Disjoint Di Dj) (f : charSpanZero S) : cfInner β (τ f : G → ℂ) = 0 :=
  cfInner_eq_zero_of_disjoint_support (hd.mono hβ (hτ f))

theorem cfInner_coherent_eq_mul [Fintype L] [Fintype G]
    {ν : Submodule.span ℤ S →+ virtualChars G} (hν : IsCoherentWith S τ ν)
    (hβ : ∀ f : charSpanZero S, cfInner β (τ f : G → ℂ) = 0)
    (u v : Submodule.span ℤ S) {e : ℂ} {d : ℤ}
    (hu : (u : L → ℂ) 1 = e) (hv : (v : L → ℂ) 1 = (d : ℂ) * e) :
    cfInner β (ν v : G → ℂ) = (d : ℂ) * cfInner β (ν u : G → ℂ) := by
  have hmem : (v : L → ℂ) - d • (u : L → ℂ) ∈ charSpanZero S := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ v.2 (Submodule.smul_mem _ _ u.2), ?_⟩
    have hsm : (d • (u : L → ℂ)) 1 = (d : ℂ) * (u : L → ℂ) 1 := by simp
    rw [Pi.sub_apply, hsm, hu, hv, sub_self]
  set f : charSpanZero S := ⟨(v : L → ℂ) - d • (u : L → ℂ), hmem⟩ with hf
  have hincl : Submodule.inclusion (charSpanZero_le S) f = v - d • u := Subtype.ext (by simp [hf])
  have key : cfInner β ((ν (v - d • u) : G → ℂ)) = 0 := by
    rw [← hincl, hν.eq_on_zero f]; exact hβ f
  rw [map_sub, map_zsmul] at key
  have hcoe : ((ν v - d • ν u : virtualChars G) : G → ℂ)
      = (ν v : G → ℂ) - d • (ν u : G → ℂ) := by simp
  rw [hcoe, cfInner_sub_right, cfInner_zsmul_right, sub_eq_zero] at key
  exact key

end Coherence

section Main

variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {ι : Type*} [Fintype ι] {ξ : ι → (L → ℂ)}
  {τ : charSpanZero (Set.range ξ) →+ virtualChars G}
  {ν : Submodule.span ℤ (Set.range ξ) →+ virtualChars G} {β : G → ℂ} (H : Subgroup L)

open scoped Classical in
theorem cfInner_coherentImage_coherentImage (hinj : Function.Injective ξ)
    (hIrr : ∀ k, ξ k ∈ Irr L) (hν : IsCoherentWith (Set.range ξ) τ ν) (k l : ι) :
    cfInner (coherentImage ξ ν k) (coherentImage ξ ν l) = if k = l then 1 else 0 := by
  rw [coherentImage_apply, coherentImage_apply, hν.inner_eq]
  simpa [hinj.eq_iff] using cfInner_eq_ite_of_mem_Irr (hIrr k) (hIrr l)

theorem cfInner_coherentImage_eq
    (hξS : Set.range ξ ⊆ indFam H (Irr H))
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hβ : ∀ f : charSpanZero (Set.range ξ), cfInner β (τ f : G → ℂ) = 0)
    {k₀ : ι} (hζ : ξ k₀ 1 = (H.index : ℂ)) (k : ι) :
    cfInner β (coherentImage ξ ν k)
      = (ξ k 1 / (H.index : ℂ)) * cfInner β (coherentImage ξ ν k₀) := by
  obtain ⟨d, -, hdvd, hd⟩ :=
    NormalInducedFamily.exists_apply_one_eq_of_mem_indFam H (hξS ⟨k, rfl⟩)
  obtain ⟨m, hm⟩ := hdvd
  have hidx : (H.index : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
  have hv : ξ k 1 = ((m : ℤ) : ℂ) * (H.index : ℂ) := by
    rw [hd, hm]; push_cast; ring
  have key := cfInner_coherent_eq_mul (β := β) hν hβ
    ⟨ξ k₀, Submodule.subset_span ⟨k₀, rfl⟩⟩ ⟨ξ k, Submodule.subset_span ⟨k, rfl⟩⟩ hζ hv
  rw [← coherentImage_apply, ← coherentImage_apply] at key
  rw [key, hv]
  field_simp

theorem cfInner_sub_smul_coherentSum_eq_zero (hinj : Function.Injective ξ)
    (hIrr : ∀ k, ξ k ∈ Irr L) (hξS : Set.range ξ ⊆ indFam H (Irr H))
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hβ : ∀ f : charSpanZero (Set.range ξ), cfInner β (τ f : G → ℂ) = 0)
    {k₀ : ι} (hζ : ξ k₀ 1 = (H.index : ℂ))
    {h : G → ℂ} (hh : h ∈ Submodule.span ℂ (Set.range (coherentImage ξ ν))) :
    cfInner (β - cfInner β (coherentImage ξ ν k₀) • coherentSum ξ ν (H.index : ℂ)) h = 0 := by
  classical
  refine cfInner_eq_zero_of_mem_span ?_ hh
  rintro - ⟨l, rfl⟩
  rw [cfInner_sub_left, cfInner_coherentImage_eq H hξS hν hβ hζ l, cfInner_smul_left,
    coherentSum_apply, cfInner_sum_left]
  have hsum : ∑ k, cfInner ((ξ k 1 / (H.index : ℂ)) • coherentImage ξ ν k)
      (coherentImage ξ ν l) = ξ l 1 / (H.index : ℂ) := by
    rw [Finset.sum_eq_single_of_mem l (Finset.mem_univ l)]
    · rw [cfInner_smul_left, cfInner_coherentImage_coherentImage hinj hIrr hν, if_pos rfl, mul_one]
    · intro k _ hkl
      rw [cfInner_smul_left, cfInner_coherentImage_coherentImage hinj hIrr hν, if_neg hkl,
        mul_zero]
  rw [hsum]
  ring

theorem eq_smul_coherentSum_of_isProj (hinj : Function.Injective ξ)
    (hIrr : ∀ k, ξ k ∈ Irr L) (hξS : Set.range ξ ⊆ indFam H (Irr H))
    (hν : IsCoherentWith (Set.range ξ) τ ν)
    (hβ : ∀ f : charSpanZero (Set.range ξ), cfInner β (τ f : G → ℂ) = 0)
    {k₀ : ι} (hζ : ξ k₀ 1 = (H.index : ℂ))
    {p : G → ℂ} (hp : p ∈ Submodule.span ℂ (Set.range (coherentImage ξ ν)))
    (hp' : ∀ h ∈ Submodule.span ℂ (Set.range (coherentImage ξ ν)), cfInner (β - p) h = 0) :
    p = cfInner β (coherentImage ξ ν k₀) • coherentSum ξ ν (H.index : ℂ) :=
  eq_of_forall_cfInner_sub_eq_zero hp
    (Submodule.smul_mem _ _ (coherentSum_mem_span ξ ν _)) hp'
    fun _ hh => cfInner_sub_smul_coherentSum_eq_zero H hinj hIrr hξS hν hβ hζ hh

end Main

end CrossFamilyProjection

end CFSG.FeitThompson
