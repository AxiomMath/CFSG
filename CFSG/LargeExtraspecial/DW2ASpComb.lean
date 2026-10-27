module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.DW2ModBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] (β : LinearMap.BilinForm (ZMod 2) E)

@[expose] def IsIsoPair (c c' : E) : Prop := c ≠ 0 ∧ c' ≠ 0 ∧ c ≠ c' ∧ β c c' = 0

@[expose] def defect (ε : E → ZMod 2) (c c' : E) : ZMod 2 := ε (c + c') + ε c + ε c'

variable {β} (hβ : β.IsAlt) {ε : E → ZMod 2}
  (hR : ∀ c c' : E, β c c' = 1 → ε (c + c') = ε c + ε c')
include hβ

theorem isAlt_apply_comm (u v : E) : β u v = β v u := by
  rw [← LinearMap.BilinForm.IsAlt.neg_eq hβ u v, ZMod.neg_eq_self_mod_two]

omit [Module (ZMod 2) E] hβ in
theorem defect_comm (c c' : E) : defect ε c c' = defect ε c' c := by
  simp only [defect, add_comm c c']
  ring

omit hβ in
theorem defect_add (c c' : E) : defect ε c (c + c') = defect ε c c' := by
  simp only [defect]
  rw [← add_assoc, add_self_zmod2, zero_add]
  ring

omit hβ in
include hR in
theorem defect_eq_of_move {c c' d : E} (h1 : β c c' = 0) (h2 : β c' d = 0) (h3 : β c d = 1) :
    defect ε c c' = defect ε c' d := by
  have e1 : ε (c + c' + d) = ε (c + c') + ε d := hR _ _ (by
    rw [map_add, LinearMap.add_apply, h3, h2]; rfl)
  have e2 : ε (c + (c' + d)) = ε c + ε (c' + d) := hR _ _ (by
    rw [map_add, h1, h3]; rfl)
  rw [← add_assoc] at e2
  simp only [defect]
  have : ε (c + c') = ε c + ε (c' + d) + ε d := by
    rw [← e2, e1, add_assoc, add_self_zmod2, add_zero]
  rw [this]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from rfl]
  ring

omit hβ in
theorem exists_apply_eq_apply_eq (hnd : ∀ a : E, a ≠ 0 → ∃ b, β a b = 1) {c c' : E} (hc : c ≠ 0)
    (hc' : c' ≠ 0) (hcc' : c ≠ c') (α α' : ZMod 2) : ∃ e, β c e = α ∧ β c' e = α' := by
  obtain ⟨e₁, he₁⟩ := hnd c hc
  obtain ⟨e₂, he₂⟩ := hnd c' hc'
  have hsum : c + c' ≠ 0 := fun h => hcc' (by
    have := congrArg (· + c') h
    simpa [add_assoc, add_self_zmod2] using this)
  obtain ⟨e₃, he₃⟩ := hnd (c + c') hsum
  rw [map_add, LinearMap.add_apply] at he₃
  have hall : ∀ a b : ZMod 2, ∃ e, β c e = a ∧ β c' e = b := by
    have key : (∃ e, β c e = 1 ∧ β c' e = 0) ∧ (∃ e, β c e = 0 ∧ β c' e = 1) := by
      rcases zmod2_cases (β c' e₁) with h1 | h1 <;> rcases zmod2_cases (β c e₂) with h2 | h2
      · exact ⟨⟨e₁, he₁, h1⟩, ⟨e₂, h2, he₂⟩⟩
      · refine ⟨⟨e₁, he₁, h1⟩, ⟨e₁ + e₂, ?_, ?_⟩⟩
        · rw [map_add, he₁, h2]; rfl
        · rw [map_add, h1, he₂]; rfl
      · refine ⟨⟨e₁ + e₂, ?_, ?_⟩, ⟨e₂, h2, he₂⟩⟩
        · rw [map_add, he₁, h2]; rfl
        · rw [map_add, h1, he₂]; rfl
      ·
        rcases zmod2_cases (β c e₃) with h3 | h3
        · have h3' : β c' e₃ = 1 := by rw [h3, zero_add] at he₃; exact he₃
          refine ⟨⟨e₁ + e₃, ?_, ?_⟩, ⟨e₃, h3, h3'⟩⟩
          · rw [map_add, he₁, h3]; rfl
          · rw [map_add, h1, h3']; rfl
        · have h3' : β c' e₃ = 0 := by
            rw [h3] at he₃
            have := congrArg (· + 1) he₃
            simpa [add_assoc, add_comm] using this
          refine ⟨⟨e₃, h3, h3'⟩, ⟨e₁ + e₃, ?_, ?_⟩⟩
          · rw [map_add, he₁, h3]; rfl
          · rw [map_add, h1, h3']; rfl
    intro a b
    obtain ⟨⟨u, hu1, hu2⟩, ⟨w, hw1, hw2⟩⟩ := key
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
    · exact ⟨0, by simp, by simp⟩
    · exact ⟨w, hw1, hw2⟩
    · exact ⟨u, hu1, hu2⟩
    · refine ⟨u + w, ?_, ?_⟩
      · rw [map_add, hu1, hw1]; rfl
      · rw [map_add, hu2, hw2]; rfl
  exact hall α α'

include hR in
theorem defect_eq_of_share (hnd : ∀ a : E, a ≠ 0 → ∃ b, β a b = 1) {c c' d : E}
    (h1 : IsIsoPair β c c') (h2 : IsIsoPair β c' d) : defect ε c c' = defect ε c' d := by
  obtain ⟨hc, hc', hcc', hβcc'⟩ := h1
  obtain ⟨-, hd, hc'd, hβc'd⟩ := h2
  by_cases h3 : β c d = 1
  · exact defect_eq_of_move hR hβcc' hβc'd h3
  have h3' : β c d = 0 := (zmod2_cases _).resolve_right h3
  obtain ⟨e, he1, he2⟩ := exists_apply_eq_apply_eq hnd hc' hc (Ne.symm hcc') 0 1
  obtain ⟨f, hf1, hf2⟩ := exists_apply_eq_apply_eq hnd hc' hd hc'd 0 1
  obtain ⟨f', hf'1, hf'2, hf'3⟩ : ∃ f', β c' f' = 0 ∧ β d f' = 1 ∧ β e f' = 1 := by
    rcases zmod2_cases (β e f) with h | h
    · refine ⟨f + c, ?_, ?_, ?_⟩
      · rw [map_add, hf1, isAlt_apply_comm hβ c' c, hβcc', add_zero]
      · rw [map_add, hf2, isAlt_apply_comm hβ d c, h3', add_zero]
      · rw [map_add, h, isAlt_apply_comm hβ e c, he2, zero_add]
    · exact ⟨f, hf1, hf2, h⟩
  have m1 := defect_eq_of_move hR hβcc' he1 he2
  have m2 := defect_eq_of_move (ε := ε) hR (c := e) (c' := c') (d := f')
    (by rw [isAlt_apply_comm hβ e c', he1]) hf'1 hf'3
  have m3 := defect_eq_of_move (ε := ε) hR (c := d) (c' := c') (d := f')
    (by rw [isAlt_apply_comm hβ d c', hβc'd]) hf'1 hf'2
  rw [m1, defect_comm c' e, m2, ← m3, defect_comm]

include hR in
theorem defect_eq_of_isIsoPair (hnd : ∀ a : E, a ≠ 0 → ∃ b, β a b = 1) {c c' e e' : E}
    (h1 : IsIsoPair β c c') (h2 : IsIsoPair β e e') : defect ε c c' = defect ε e e' := by
  obtain ⟨hc, hc', hcc', hβcc'⟩ := h1
  obtain ⟨he, he', hee', hβee'⟩ := h2
  have hsum : e + e' ≠ 0 := fun h => hee' (by
    have := congrArg (· + e') h
    simpa [add_assoc, add_self_zmod2] using this)
  obtain ⟨f, f', hpair, hβcf, hdef⟩ : ∃ f f', IsIsoPair β f f' ∧ β c f = 0 ∧
      defect ε e e' = defect ε f f' := by
    rcases zmod2_cases (β c e) with h | h
    · exact ⟨e, e', ⟨he, he', hee', hβee'⟩, h, rfl⟩
    rcases zmod2_cases (β c e') with h' | h'
    · exact ⟨e', e, ⟨he', he, Ne.symm hee', by rw [isAlt_apply_comm hβ, hβee']⟩, h',
        defect_comm e e'⟩
    · refine ⟨e + e', e, ⟨hsum, he, fun h0 => he' ?_, ?_⟩, ?_, ?_⟩
      · have := congrArg (e + ·) h0.symm
        simpa [← add_assoc, add_self_zmod2] using this.symm
      · rw [map_add, LinearMap.add_apply, hβ e, isAlt_apply_comm hβ e' e, hβee', add_zero]
      · rw [map_add, h, h']
        rfl
      · rw [defect_comm (e + e') e, defect_add]
  have hc'c : IsIsoPair β c' c := ⟨hc', hc, Ne.symm hcc', by rw [isAlt_apply_comm hβ, hβcc']⟩
  rw [hdef, defect_comm c c']
  by_cases hfc : f = c
  · rw [hfc] at hpair ⊢
    exact defect_eq_of_share hβ hR hnd hc'c hpair
  · have hcf : IsIsoPair β c f := ⟨hc, hpair.1, Ne.symm hfc, hβcf⟩
    rw [defect_eq_of_share hβ hR hnd hc'c hcf, defect_eq_of_share hβ hR hnd hcf hpair]

omit hβ in
theorem exists_eq_of_defect_eq_zero [FiniteDimensional (ZMod 2) E] (hnd : β.Nondegenerate)
    (hR : ∀ c c' : E, β c c' = 1 → ε (c + c') = ε c + ε c') (hε0 : ε 0 = 0)
    (hD : ∀ c c' : E, IsIsoPair β c c' → defect ε c c' = 0) : ∃ w : E, ∀ c, ε c = β w c := by
  have hadd : ∀ c c' : E, ε (c + c') = ε c + ε c' := by
    intro c c'
    by_cases hc : c = 0
    · rw [hc, zero_add, hε0, zero_add]
    by_cases hc' : c' = 0
    · rw [hc', add_zero, hε0, add_zero]
    by_cases hcc' : c = c'
    · rw [hcc', add_self_zmod2, hε0, add_self_zmod2]
    rcases zmod2_cases (β c c') with h | h
    · have := hD c c' ⟨hc, hc', hcc', h⟩
      simp only [defect] at this
      have := congrArg (· + (ε c + ε c')) this
      simp only [zero_add] at this
      rw [← this]
      ring_nf
      rw [show (2 : ZMod 2) = 0 from rfl]
      ring
    · exact hR c c' h
  let φ : Module.Dual (ZMod 2) E :=
    { toFun := ε
      map_add' := hadd
      map_smul' := fun a x => by
        rcases zmod2_cases a with rfl | rfl
        · rw [zero_smul, hε0, RingHom.id_apply, zero_smul]
        · rw [one_smul, RingHom.id_apply, one_smul] }
  refine ⟨(β.toDual hnd).symm φ, fun c => ?_⟩
  rw [← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  rfl

end CFSG.LargeExtraspecial.DW
