module

public import CFSG.GF2Type.SmithTypeE.E8.ModD6
public import CFSG.GF2Type.SmithTypeE.E8.SfFix
public import CFSG.GF2Type.SmithTypeE.E8.ModDefs

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.SmithE8M
open CFSG.SeitzReduction.EPilot (pinnedElt)

@[expose] def wgrade (b : Fin e7Data.d) : ℤ := ![2, 3, 4, 6, 5, 4, 3] ⬝ᵥ e7Data.wt b

theorem w0_wgrade_cases :
    ∀ b : Fin e7Data.d, wgrade b = 3 ∨ wgrade b = 1 ∨ wgrade b = -1 ∨ wgrade b = -3 := by
  decide +kernel

theorem w0_card_pos : (Finset.univ.filter fun b : Fin e7Data.d => 0 < wgrade b).card = 28 := by
  decide +kernel

theorem w0_exists_RA : ∀ b : Fin e7Data.d, wgrade b ≤ 0 →
    ∃ k : Fin 126, e7Data.wt 0 ⬝ᵥ e8mRoot k = 1 ∧ e7Data.wt b ⬝ᵥ e8mRoot k = -1 ∧
      e7Data.wt b + MinData.toWeight (e8mRoot k) ≠ e7Data.wt 0 := by
  decide +kernel

theorem w0_shift_zero : ∀ b : Fin e7Data.d, 0 < wgrade b → ∀ k : Fin 126,
    e7Data.wt 0 ⬝ᵥ e8mRoot k = 1 → e7Data.wt b ⬝ᵥ e8mRoot k = -1 →
      e7Data.wt b + MinData.toWeight (e8mRoot k) = e7Data.wt 0 := by
  decide +kernel

theorem w0_RA_pos : ∀ k : Fin 126, e8mRoot k ⟨6, by decide⟩ = 1 → 0 < height (e8mRoot k) := by
  decide +kernel

theorem w0_c7_le_one : ∀ k : Fin 126, 0 < height (e8mRoot k) → e8mRoot k ⟨6, by decide⟩ ≠ 0 →
    e8mRoot k ⟨6, by decide⟩ = 1 := by
  decide +kernel

section Group


theorem sum_single_one (w : Fin e7Data.d →₀ ZMod 2) :
    w = ∑ a, w a • Finsupp.single a (1 : ZMod 2) := by
  ext c
  simp [Finsupp.finset_sum_apply, Finsupp.single_apply]

set_option maxRecDepth 20000 in
theorem rootOp_apply_eq_sum (β : Fin (Tag.rank .E7) → ℤ) (w : Fin e7Data.d →₀ ZMod 2) :
    e7Data.rootOp (ZMod 2) β w =
      ∑ a, w a • e7Data.rootOp (ZMod 2) β (Finsupp.single a 1) := by
  conv_lhs => rw [sum_single_one w]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ =>
    (e7Data.rootOp (ZMod 2) β).map_smul (w a) (Finsupp.single a 1)

set_option maxRecDepth 20000 in
theorem rootOp_single_coord {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (a c : Fin e7Data.d) :
    (e7Data.rootOp (ZMod 2) β (Finsupp.single a 1)) c =
      if e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt c = e7Data.wt a + MinData.toWeight β then 1 else 0 := by
  rcases rootOp_single_cases (K := ZMod 2) hβ a with ⟨h1, h2⟩ | ⟨h1, b, hb, h2⟩
  · rw [h2]
    simp [h1]
  · rw [h2, Finsupp.single_apply]
    by_cases hcb : b = c
    · subst hcb
      simp [h1, hb]
    · have : ¬ (e7Data.wt c = e7Data.wt a + MinData.toWeight β) := fun h =>
        hcb (e7Data_valid.wt_injective (hb.trans h.symm))
      simp [hcb, this]

set_option maxRecDepth 20000 in
theorem coord_pinned_sub {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (w : Fin e7Data.d →₀ ZMod 2) {b c : Fin e7Data.d} (hb : e7Data.wt b ⬝ᵥ β = -1)
    (hc : e7Data.wt c = e7Data.wt b + MinData.toWeight β) :
    (e7Rep56 (ZMod 2) (pinnedElt .E7 β 1) w - w) c = w b := by
  rw [e7Rep56_pinnedElt_apply hβ, one_smul, add_sub_cancel_left, rootOp_apply_eq_sum,
    Finsupp.finset_sum_apply]
  rw [Finset.sum_eq_single b]
  · rw [Finsupp.smul_apply, rootOp_single_coord hβ, if_pos ⟨hb, hc⟩]
    simp
  · intro a _ hab
    rw [Finsupp.smul_apply, rootOp_single_coord hβ, if_neg]
    · simp
    · rintro ⟨_, h⟩
      exact hab (e7Data_valid.wt_injective (add_right_cancel (h.symm.trans hc)))
  · simp

@[expose] def W0stab : Subgroup ↥(adjointGroup .E7 (ZMod 2)) where
  carrier := {g | e7Rep56 (ZMod 2) g e7Y56 = e7Y56 ∧ ∀ w : Fin e7Data.d →₀ ZMod 2,
    (∀ b, wgrade b ≤ 0 → w b = 0) →
      e7Rep56 (ZMod 2) g w - w ∈ Submodule.span (ZMod 2) {(e7Y56 : Fin e7Data.d →₀ ZMod 2)}}
  one_mem' := ⟨by rw [map_one]; rfl, fun w _ => by
    rw [map_one]
    simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨by rw [map_mul, Module.End.mul_apply, hh1, hg1], fun w hw => ?_⟩
    have e : e7Rep56 (ZMod 2) (g * h) w - w =
        e7Rep56 (ZMod 2) g (e7Rep56 (ZMod 2) h w - w) + (e7Rep56 (ZMod 2) g w - w) := by
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    rw [e]
    refine add_mem ?_ (hg2 w hw)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hh2 w hw)
    rw [← hc, map_smul, hg1]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hv : e7Rep56 (ZMod 2) g⁻¹ e7Y56 = e7Y56 := by
      have := congrArg (e7Rep56 (ZMod 2) g⁻¹) hg1
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        at this
      exact this.symm
    refine ⟨hv, fun w hw => ?_⟩
    have e : e7Rep56 (ZMod 2) g⁻¹ w - w = - e7Rep56 (ZMod 2) g⁻¹ (e7Rep56 (ZMod 2) g w - w) := by
      rw [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
      abel
    rw [e]
    refine neg_mem ?_
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hg2 w hw)
    rw [← hc, map_smul, hv]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem wt0_dot (β : Fin (Tag.rank .E7) → ℤ) : e7Data.wt 0 ⬝ᵥ β = β e7n6 := by
  simp [dotProduct, e7_wt_zero]

theorem mem_RA_wt {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : β ∈ parabolicRadicalRoots .E7 {i | i ≠ e7n6}) :
    IsRoot .E7 β ∧ e7Data.wt 0 ⬝ᵥ β = 1 := by
  obtain ⟨⟨hroot, hpos⟩, hnot⟩ := hβ
  refine ⟨hroot, ?_⟩
  have h7 : β e7n6 ≠ 0 := fun h0 => hnot ⟨⟨hroot, fun i hi => by
    have : i = e7n6 := by simpa using hi
    rw [this]; exact h0⟩, hroot, hpos⟩
  obtain ⟨k, hk, rfl⟩ := exists_e8mRoot_eq hroot
  rw [wt0_dot]
  exact w0_c7_le_one ⟨k, hk⟩ hpos h7

theorem RA_mem {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (h : e7Data.wt 0 ⬝ᵥ β = 1) :
    β ∈ parabolicRadicalRoots .E7 {i | i ≠ e7n6} := by
  rw [wt0_dot] at h
  obtain ⟨k, hk, rfl⟩ := exists_e8mRoot_eq hβ
  have hpos := w0_RA_pos ⟨k, hk⟩ h
  refine ⟨⟨hβ, hpos⟩, fun ⟨⟨_, hz⟩, _⟩ => ?_⟩
  have := hz e7n6 (by simp)
  rw [h] at this
  exact one_ne_zero this

theorem pinnedElt_mem_W0stab {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (h : e7Data.wt 0 ⬝ᵥ β = 1) : pinnedElt .E7 β (1 : ZMod 2) ∈ W0stab := by
  refine ⟨?_, fun w hw => ?_⟩
  · unfold e7Y56
    rw [e7Rep56_pinnedElt_single hβ]
    rw [if_neg (by rw [h]; decide), add_zero]
  · rw [e7Rep56_pinnedElt_apply hβ, one_smul, add_sub_cancel_left, rootOp_apply_eq_sum]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases hwa : w a = 0
    · rw [hwa, zero_smul]
      exact zero_mem _
    · have hgr : 0 < wgrade a := by
        by_contra hle
        exact hwa (hw a (not_lt.mp hle))
      refine Submodule.smul_mem _ _ ?_
      rcases rootOp_single_cases (K := ZMod 2) hβ a with ⟨_, h2⟩ | ⟨h1, b, hb, h2⟩
      · rw [h2]
        exact zero_mem _
      · rw [h2]
        obtain ⟨k, hk, rfl⟩ := exists_e8mRoot_eq hβ
        have := w0_shift_zero a hgr ⟨k, hk⟩ h h1
        have hb0 : b = ⟨0, by decide⟩ := e7Data_valid.wt_injective (hb.trans this)
        rw [hb0]
        exact Submodule.mem_span_singleton_self _

theorem mem_QA_of_RA {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β)
    (h : e7Data.wt 0 ⬝ᵥ β = 1) :
    (pinnedElt .E7 β (1 : ZMod 2) : ModGL .E7 (ZMod 2)) ∈ QA :=
  Subgroup.mem_iSup_of_mem β (Subgroup.mem_iSup_of_mem (RA_mem hβ h)
    (Subgroup.subset_closure ⟨1, rfl⟩))

set_option maxRecDepth 20000 in
theorem mem_W0_iff (u : Fin e7Data.d →₀ ZMod 2) :
    (∀ q : ↥(adjointGroup .E7 (ZMod 2)), (q : ModGL .E7 (ZMod 2)) ∈ QA →
        e7Rep56 (ZMod 2) q u - u ∈ Submodule.span (ZMod 2) {(e7Y56 : Fin e7Data.d →₀ ZMod 2)}) ↔
      ∀ b : Fin e7Data.d, wgrade b ≤ 0 → u b = 0 := by
  constructor
  · intro h b hb
    obtain ⟨k, hk0, hkb, hne⟩ := w0_exists_RA b hb
    have hβ : IsRoot .E7 (e8mRoot k) := e8mRoot_isRoot k.2
    have hq := mem_QA_of_RA hβ hk0
    have hh := h _ hq
    obtain ⟨c, hc⟩ : ∃ c : Fin e7Data.d,
        e7Data.wt c = e7Data.wt b + MinData.toWeight (e8mRoot k) := by
      rcases rootOp_single_cases (K := ZMod 2) hβ b with ⟨h1, _⟩ | ⟨_, c, hc, _⟩
      · exact absurd hkb h1
      · exact ⟨c, hc⟩
    have hcoord := coord_pinned_sub hβ u hkb hc
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hh
    have hc0 : c ≠ ⟨0, by decide⟩ := fun h0 => hne (by rw [← hc, h0])
    have := congrArg (fun v : Fin e7Data.d →₀ ZMod 2 => v c) hs
    simp only [Finsupp.smul_apply, e7Y56, Finsupp.single_apply, smul_eq_mul] at this
    rw [if_neg (fun h' => hc0 h'.symm), mul_zero] at this
    rw [← hcoord]
    exact this.symm
  · intro hu q hq
    have hW : QA ≤ (W0stab).map (adjointGroup .E7 (ZMod 2)).subtype := by
      refine iSup₂_le fun β hβ => ?_
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨c, rfl⟩
      obtain ⟨hroot, h1⟩ := mem_RA_wt hβ
      have hc : c = 0 ∨ c = 1 := by
        revert c
        decide
      rcases hc with rfl | rfl
      · rw [CFSG.Blueprint.Chevalley.pinnedX_zero]
        exact one_mem _
      · exact ⟨pinnedElt .E7 β 1, pinnedElt_mem_W0stab hroot h1, rfl⟩
    obtain ⟨g, hg, hgq⟩ := hW hq
    have : g = q := Subtype.ext hgq
    subst this
    exact hg.2 u hu

@[expose] def W0 : Submodule (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
  Finsupp.supported (ZMod 2) (ZMod 2) {b : Fin e7Data.d | 0 < wgrade b}

theorem mem_W0 (u : Fin e7Data.d →₀ ZMod 2) : u ∈ W0 ↔ ∀ b, wgrade b ≤ 0 → u b = 0 := by
  rw [W0, Finsupp.mem_supported']
  exact ⟨fun h b hb => h b (by simpa using hb), fun h b hb => h b (by simpa using hb)⟩

theorem finrank_W0 : Module.finrank (ZMod 2) W0 = 28 := by
  rw [W0, (Finsupp.supportedEquivFinsupp (M := ZMod 2) (R := ZMod 2)
    {b : Fin e7Data.d | 0 < wgrade b}).finrank_eq, Module.finrank_finsupp_self]
  rw [Fintype.card_subtype]
  exact w0_card_pos

theorem mem_W0_iff' (u : Fin e7Data.d →₀ ZMod 2) :
    u ∈ W0 ↔ ∀ q : ↥(adjointGroup .E7 (ZMod 2)), (q : ModGL .E7 (ZMod 2)) ∈ QA →
        e7Rep56 (ZMod 2) q u - u ∈ Submodule.span (ZMod 2) {(e7Y56 : Fin e7Data.d →₀ ZMod 2)} :=
  (mem_W0 u).trans (mem_W0_iff u).symm

theorem e7Rep56_mem_W0 {s : ↥(adjointGroup .E7 (ZMod 2))}
    (hs : e7Rep56 (ZMod 2) s e7Y56 = e7Y56) {u : Fin e7Data.d →₀ ZMod 2} (hu : u ∈ W0) :
    e7Rep56 (ZMod 2) s u ∈ W0 := by
  rw [mem_W0_iff'] at hu ⊢
  intro q hq
  have hsP : (s : ModGL .E7 (ZMod 2)) ∈ parabolicSubgroup .E7 (ZMod 2) {i | i ≠ e7n6} :=
    (e7Rep56_e7Y56_eq_iff s).1 hs
  have hN : (s : ModGL .E7 (ZMod 2)) ∈ Subgroup.normalizer (QA : Set (ModGL .E7 (ZMod 2))) := by
    have := adjointGroup_inf_normalizer_parabolicRadical (τ := .E7) (K := ZMod 2)
      {i | i ≠ e7n6}
    rw [← this] at hsP
    exact hsP.2
  have hq' : ((s⁻¹ * q * s : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈ QA := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hN) (q : ModGL .E7 (ZMod 2))).1 hq
    simpa using h1
  have h2 := hu (s⁻¹ * q * s) hq'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
  have e : e7Rep56 (ZMod 2) q (e7Rep56 (ZMod 2) s u) - e7Rep56 (ZMod 2) s u =
      e7Rep56 (ZMod 2) s (e7Rep56 (ZMod 2) (s⁻¹ * q * s) u - u) := by
    rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp
  rw [e, ← hc, map_smul, hs]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_collSpace_iff (g : ↥(adjointGroup .E7 (ZMod 2))) (u : Fin e7Data.d →₀ ZMod 2) :
    u ∈ collSpace (e7Rep56 (ZMod 2) g e7Y56) ↔ e7Rep56 (ZMod 2) g⁻¹ u ∈ W0 := by
  constructor
  · rintro ⟨g', hg', hq⟩
    have hq' : e7Rep56 (ZMod 2) g'⁻¹ u ∈ W0 := (mem_W0_iff' _).2 hq
    have hs : e7Rep56 (ZMod 2) (g⁻¹ * g') e7Y56 = e7Y56 := by
      rw [map_mul, Module.End.mul_apply, hg']
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have := e7Rep56_mem_W0 hs hq'
    rw [← Module.End.mul_apply, ← map_mul] at this
    simpa using this
  · intro h
    refine ⟨g, rfl, fun q hq => ?_⟩
    exact (mem_W0_iff' _).1 h q hq

end Group

end CFSG.GF2Type.SmithTypeE.E8
