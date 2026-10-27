module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IndexTwoBlockUniqueness

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace Classif

variable {Ω : Type*} [DecidableEq Ω] {W : Subgroup (Perm Ω)} {x : Ω}

theorem eq_of_swap_mem (hW : IsPGroup 2 W) {a b c : Ω} (hab : a ≠ b) (hac : a ≠ c)
    (hb : swap a b ∈ W) (hc : swap a c ∈ W) : b = c := by
  by_contra hbc
  have hca : c ≠ a := Ne.symm hac
  have hcb : c ≠ b := Ne.symm hbc
  have hba : b ≠ a := Ne.symm hab
  refine not_isPGroup_of_threeCycle hW (g := swap a b * swap a c) (W.mul_mem hb hc)
    (a := a) (b := c) (c := b) hac hcb hba ?_ ?_ ?_
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hca hcb]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hba hbc, swap_apply_right]

open scoped Classical in
@[expose] noncomputable def partnerFn (W : Subgroup (Perm Ω)) (x : Ω) : Ω :=
  if h : ∃ y, x ≠ y ∧ swap x y ∈ W then h.choose else x

theorem partnerFn_eq (hW : IsPGroup 2 W) {x y : Ω} (hxy : x ≠ y) (h : swap x y ∈ W) :
    partnerFn W x = y := by
  classical
  have hex : ∃ y, x ≠ y ∧ swap x y ∈ W := ⟨y, hxy, h⟩
  unfold partnerFn
  simp only [hex, ↓reduceDIte]
  exact eq_of_swap_mem hW hex.choose_spec.1 hxy hex.choose_spec.2 h

theorem partnerFn_eq_self (h : ∀ y, x ≠ y → swap x y ∉ W) : partnerFn W x = x := by
  classical
  unfold partnerFn
  have hn : ¬ ∃ y, x ≠ y ∧ swap x y ∈ W := by rintro ⟨y, hy, hm⟩; exact h y hy hm
  simp only [hn, ↓reduceDIte]

theorem partnerFn_ne_iff {x : Ω} : partnerFn W x ≠ x ↔ ∃ y, x ≠ y ∧ swap x y ∈ W := by
  classical
  constructor
  · intro h
    by_contra hn
    exact h (partnerFn_eq_self fun y hy hm => hn ⟨y, hy, hm⟩)
  · intro hex
    unfold partnerFn
    simp only [hex, ↓reduceDIte]
    exact Ne.symm hex.choose_spec.1

theorem swap_partnerFn_mem {x : Ω} (h : partnerFn W x ≠ x) : swap x (partnerFn W x) ∈ W := by
  classical
  have hex := partnerFn_ne_iff.1 h
  unfold partnerFn
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec.2

theorem partnerFn_partnerFn (hW : IsPGroup 2 W) (x : Ω) : partnerFn W (partnerFn W x) = x := by
  by_cases h : partnerFn W x = x
  · rw [h, h]
  · have hm := swap_partnerFn_mem h
    refine partnerFn_eq hW h ?_
    rw [swap_comm]; exact hm

theorem swap_conj_mem {w : Perm Ω} (hw : w ∈ W) {x y : Ω} (h : swap x y ∈ W) :
    swap (w x) (w y) ∈ W := by
  rw [swap_apply_apply]
  exact W.mul_mem (W.mul_mem hw h) (W.inv_mem hw)

theorem partnerFn_apply_of_mem (hW : IsPGroup 2 W) {w : Perm Ω} (hw : w ∈ W) (x : Ω) :
    partnerFn W (w x) = w (partnerFn W x) := by
  by_cases h : partnerFn W x = x
  · rw [h]
    by_contra hne
    have hm := swap_partnerFn_mem hne
    have := swap_conj_mem (W.inv_mem hw) hm
    have e : w⁻¹ (w x) = x := by simp
    rw [e] at this
    have hne' : x ≠ w⁻¹ (partnerFn W (w x)) := by
      intro hx
      apply hne
      have := congrArg w hx
      simpa using this.symm
    have h2 : partnerFn W x = w⁻¹ (partnerFn W (w x)) := partnerFn_eq hW hne' this
    have h3 : w⁻¹ (partnerFn W (w x)) = x := h2.symm.trans h
    apply hne
    have := congrArg w h3
    simpa using this
  · have hm := swap_conj_mem hw (swap_partnerFn_mem h)
    refine partnerFn_eq hW ?_ hm
    intro hx
    exact h (w.injective hx).symm

@[expose] noncomputable def partner (hW : IsPGroup 2 W) : Perm Ω :=
  Function.Involutive.toPerm (partnerFn W) (partnerFn_partnerFn hW)

theorem partner_partner (hW : IsPGroup 2 W) (x : Ω) : partner hW (partner hW x) = x :=
  partnerFn_partnerFn hW x

theorem partner_comm (hW : IsPGroup 2 W) {w : Perm Ω} (hw : w ∈ W) (x : Ω) :
    partner hW (w x) = w (partner hW x) := partnerFn_apply_of_mem hW hw x

theorem partner_eq_of_swap_mem (hW : IsPGroup 2 W) {x y : Ω} (hxy : x ≠ y) (h : swap x y ∈ W) :
    partner hW x = y := partnerFn_eq hW hxy h

theorem swap_partner_mem (hW : IsPGroup 2 W) {x : Ω} (h : partner hW x ≠ x) :
    swap x (partner hW x) ∈ W := swap_partnerFn_mem h

theorem partner_ne_iff (hW : IsPGroup 2 W) {x : Ω} :
    partner hW x ≠ x ↔ ∃ y, x ≠ y ∧ swap x y ∈ W := partnerFn_ne_iff

end Classif

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
