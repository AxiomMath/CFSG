module

public import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import CFSG.FeitThompson.Representations.DisjointAntirealBlocksOrthogonal
public import CFSG.FeitThompson.Representations.EqualDegreeZeroLatticeBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate
open Module

variable {G : Type*} [Group G]

section Dual

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]

def dualSubrepresentationOrderIso (ρ : Representation k G V) :
    Subrepresentation ρ.dual ≃o (Subrepresentation ρ)ᵒᵈ where
  toFun U := OrderDual.toDual
    ⟨U.toSubmodule.dualCoannihilator, fun g v hv => by
      rw [Submodule.mem_dualCoannihilator]
      intro f hf
      have hf' : ρ.dual g⁻¹ f ∈ U.toSubmodule := U.apply_mem_toSubmodule g⁻¹ hf
      have h := (Submodule.mem_dualCoannihilator v).1 hv _ hf'
      rw [Representation.dual_apply, Dual.transpose_apply] at h
      simpa using h⟩
  invFun U := ⟨(OrderDual.ofDual U).toSubmodule.dualAnnihilator, fun g f hf => by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    rw [Representation.dual_apply, Dual.transpose_apply]
    exact (Submodule.mem_dualAnnihilator f).1 hf _
      ((OrderDual.ofDual U).apply_mem_toSubmodule g⁻¹ hw)⟩
  left_inv U := Subrepresentation.ext
    (Subspace.dualCoannihilator_dualAnnihilator_eq (W := U.toSubmodule))
  right_inv U := OrderDual.toDual.injective (Subrepresentation.ext
    (Subspace.dualAnnihilator_dualCoannihilator_eq (W := (OrderDual.ofDual U).toSubmodule)))
  map_rel_iff' {U W} := by
    change W.toSubmodule.dualCoannihilator ≤ U.toSubmodule.dualCoannihilator ↔
      U.toSubmodule ≤ W.toSubmodule
    refine ⟨fun h => ?_, fun h => Submodule.dualCoannihilator_anti h⟩
    have h' := Submodule.dualAnnihilator_anti h
    rwa [Subspace.dualCoannihilator_dualAnnihilator_eq,
      Subspace.dualCoannihilator_dualAnnihilator_eq] at h'

theorem isIrreducible_dual (ρ : Representation k G V) [ρ.IsIrreducible] :
    ρ.dual.IsIrreducible :=
  (dualSubrepresentationOrderIso ρ).isSimpleOrder

end Dual

theorem conj_mem_Irr [Finite G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    (fun x => conj (χ x)) ∈ Irr G := by
  obtain ⟨V, hV, rfl⟩ := mem_Irr.1 hχ
  refine mem_Irr.2 ⟨FDRep.of (Representation.dual (V.ρ : Representation ℂ G V.V)), ?_, ?_⟩
  · rw [FDRep.of_ρ']
    have := hV
    exact isIrreducible_dual _
  · funext g
    simp only [FDRep.character, FDRep.of_ρ']
    exact Representation.character_dual_eq_conj _ (isOfFinOrder_of_finite g)

theorem conj_mem_signedIrr [Finite G] {f : G → ℂ} (hf : f ∈ signedIrr G) :
    (fun x => conj (f x)) ∈ signedIrr G := by
  rcases mem_signedIrr.1 hf with h | h
  · exact mem_signedIrr.2 (Or.inl (conj_mem_Irr h))
  · refine mem_signedIrr.2 (Or.inr ?_)
    have h' := conj_mem_Irr h
    have he : (fun x => conj ((-f) x)) = -fun x => conj (f x) := by funext x; simp
    rwa [he] at h'

theorem conj_apply_one_of_mem_Irr {χ : G → ℂ} (hχ : χ ∈ Irr G) : conj (χ 1) = χ 1 := by
  obtain ⟨V, -, rfl⟩ := mem_Irr.1 hχ
  rw [FDRep.char_one]
  simp

theorem apply_one_ne_zero_of_mem_signedIrr {f : G → ℂ} (hf : f ∈ signedIrr G) : f 1 ≠ 0 := by
  rcases mem_signedIrr.1 hf with h | h
  · exact apply_one_ne_zero_of_mem_Irr h
  · have := apply_one_ne_zero_of_mem_Irr h
    simpa using this

theorem conj_apply_one_of_mem_signedIrr {f : G → ℂ} (hf : f ∈ signedIrr G) :
    conj (f 1) = f 1 := by
  rcases mem_signedIrr.1 hf with h | h
  · exact conj_apply_one_of_mem_Irr h
  · have h' := conj_apply_one_of_mem_Irr h
    simp only [Pi.neg_apply, map_neg, neg_inj] at h'
    exact h'

theorem ne_neg_conj_of_mem_signedIrr {f : G → ℂ} (hf : f ∈ signedIrr G) :
    f ≠ -fun x => conj (f x) := by
  intro h
  have h1 : f 1 = -conj (f 1) := congrFun h 1
  rw [conj_apply_one_of_mem_signedIrr hf] at h1
  exact apply_one_ne_zero_of_mem_signedIrr hf (by linear_combination h1 / 2)

theorem cfInner_conj_eq_zero_of_ne [Fintype G] {s : G → ℂ} (hs : s ∈ signedIrr G)
    (hsr : s ≠ fun x => conj (s x)) : cfInner s (fun x => conj (s x)) = 0 := by
  have hcs : (fun x => conj (s x)) ∈ signedIrr G := conj_mem_signedIrr hs
  rcases cfInner_eq_zero_or_one_or_neg_one_of_mem_signedIrr hs hcs with h | h | h
  · exact h
  · exact absurd (eq_of_cfInner_eq_one hs hcs h) hsr
  · have h1 : cfInner (-s) (fun x => conj (s x)) = 1 := by rw [cfInner_neg_left, h, neg_neg]
    have h2 := eq_of_cfInner_eq_one (neg_mem_signedIrr_iff.2 hs) hcs h1
    exact absurd (neg_eq_iff_eq_neg.1 h2) (ne_neg_conj_of_mem_signedIrr hs)

theorem cfInner_eq_zero_of_disjoint_support_of_ne_conj [Fintype G] {ρ s : G → ℂ}
    (hρ : ρ ∈ signedIrr G) (hs : s ∈ signedIrr G) (hsr : s ≠ fun x => conj (s x))
    {D E : Set G} (hDE : Disjoint D E)
    (hρD : ∀ x ∉ D, ρ x - conj (ρ x) = 0) (hsE : ∀ x ∉ E, s x - conj (s x) = 0) :
    cfInner ρ s = 0 := by
  classical
  set cs : G → ℂ := fun x => conj (s x) with hcs
  have hcsmem : cs ∈ signedIrr G := conj_mem_signedIrr hs
  have hne : s ≠ -cs := ne_neg_conj_of_mem_signedIrr hs
  have hsum : ∑ b ∈ ({s, -cs} : Finset (G → ℂ)), b = s + -cs := Finset.sum_pair hne
  refine cfInner_eq_zero_of_conj_eq_neg_of_disjoint_support (R := {ρ}) (T := {s, -cs})
    (fun a ha => by rwa [Finset.mem_singleton.1 ha]) ?_ ?_ hDE ?_ ?_ ?_
    (Finset.mem_singleton_self ρ) (Finset.mem_insert_self _ _)
  · intro b hb
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hs
    · rw [Finset.mem_singleton.1 hb]
      exact neg_mem_signedIrr_iff.2 hcsmem
  ·
    have h0 : cfInner s cs = 0 := cfInner_conj_eq_zero_of_ne hs hsr
    have h0' : cfInner cs s = 0 := by rw [← conj_cfInner, h0, map_zero]
    intro b hb b' hb'
    rcases Finset.mem_insert.1 hb with rfl | hb <;> rcases Finset.mem_insert.1 hb' with rfl | hb'
    · rw [if_pos rfl]; exact cfInner_self_of_mem_signedIrr hs
    · rw [Finset.mem_singleton.1 hb', if_neg hne, cfInner_neg_right, h0, neg_zero]
    · rw [Finset.mem_singleton.1 hb, if_neg (Ne.symm hne), cfInner_neg_left, h0', neg_zero]
    · rw [Finset.mem_singleton.1 hb, Finset.mem_singleton.1 hb', if_pos rfl,
        cfInner_neg_left, cfInner_neg_right, neg_neg]
      exact cfInner_self_of_mem_signedIrr hcsmem
  ·
    intro x
    rw [hsum]
    simp only [Pi.add_apply, Pi.neg_apply, hcs, map_add, map_neg, Complex.conj_conj]
    ring
  ·
    intro x hx
    have h := hsE x hx
    rw [hsum]
    simp only [Pi.add_apply, Pi.neg_apply, hcs]
    linear_combination h
  · intro a ha x hx
    rw [Finset.mem_singleton.1 ha]
    exact hρD x hx

open scoped Classical in
theorem not_of_disjoint_support_of_row_column [Fintype G]
    {I J : Type*} [Fintype I] [Fintype J] {η : I → J → G → ℂ}
    (_hηmem : ∀ i j, η i j ∈ virtualChars G)
    (hηortho : ∀ i j i' j', cfInner (η i j) (η i' j') = if i = i' ∧ j = j' then 1 else 0)
    {ρ s : G → ℂ} (hρ : ρ ∈ signedIrr G) (hs : s ∈ signedIrr G)
    (hsr : s ≠ fun x => conj (s x))
    (hρη : ∀ i j, cfInner ρ (η i j) = 0) (hsη : ∀ i j, cfInner s (η i j) = 0)
    {D E : Set G} (hDE : Disjoint D E) (i₀ : I) (j₀ : J) {ε δ : ℂ}
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    (hρD : ∀ x ∉ D, ρ x - conj (ρ x) = 0)
    (hρD' : ∀ x ∉ D, (ρ - ε • ∑ i : I, η i j₀) x = 0)
    (hsE : ∀ x ∉ E, s x - conj (s x) = 0)
    (hsE' : ∀ x ∉ E, (s - δ • ∑ j : J, η i₀ j) x = 0) : False := by
  have hρs : cfInner ρ s = 0 :=
    cfInner_eq_zero_of_disjoint_support_of_ne_conj hρ hs hsr hDE hρD hsE
  set col : G → ℂ := ∑ i : I, η i j₀ with hcol
  set row : G → ℂ := ∑ j : J, η i₀ j with hrow
  have hρrow : cfInner ρ row = 0 := by
    rw [hrow, cfInner_sum_right]
    exact Finset.sum_eq_zero fun j _ => hρη i₀ j
  have hcols : cfInner col s = 0 := by
    rw [hcol, cfInner_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← conj_cfInner, hsη i j₀, map_zero]
  have hcolrow : cfInner col row = 1 := by
    have hin : ∀ i : I, cfInner (η i j₀) row = if i = i₀ then 1 else 0 := fun i => by
      rw [hrow, cfInner_sum_right, Finset.sum_congr rfl fun j _ => hηortho i j₀ i₀ j]
      by_cases h : i = i₀ <;> simp [h]
    rw [hcol, cfInner_sum_left, Finset.sum_congr rfl fun i _ => hin i]
    simp
  have key : cfInner (ρ - ε • col) (s - δ • row) = 0 := by
    refine cfInner_eq_zero_of_disjoint_support (Set.disjoint_left.2 fun x hx hy => ?_)
    have hxD : x ∈ D := by by_contra h; exact hx (hρD' x h)
    have hxE : x ∈ E := by by_contra h; exact hy (hsE' x h)
    exact Set.disjoint_left.1 hDE hxD hxE
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
    cfInner_smul_right, cfInner_smul_right, cfInner_smul_left, hρs, hρrow, hcols,
    hcolrow] at key
  have hne : ε * conj δ ≠ 0 := by
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> norm_num
  exact hne (by linear_combination key)

end CFSG.FeitThompson
