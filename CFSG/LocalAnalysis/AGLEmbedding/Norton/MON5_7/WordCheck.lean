module

public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton.MON5_7

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

@[expose] noncomputable def gw (w : List Native.Gen) : Gmat := ⟨wordLin w, wordLin_mem_Gmat w⟩

@[simp] theorem coe_gw (w : List Native.Gen) : ((gw w : Gmat) : SpaceB ≃ₗ[ℚ] SpaceB) = wordLin w :=
  rfl

theorem gw_nil : gw [] = 1 := Subtype.ext wordLin_nil

theorem gw_append (w₁ w₂ : List Native.Gen) : gw (w₁ ++ w₂) = gw w₂ * gw w₁ :=
  Subtype.ext (wordLin_append w₁ w₂)

@[expose] def agree (w₁ w₂ : List Native.Gen) : Bool :=
  w₁.all (fun g => g.validB) && w₂.all (fun g => g.validB) &&
    (Native.evalWord w₁ (aV ())).eqv (Native.evalWord w₂ (aV ())) &&
    (Native.evalWord w₁ (bV ())).eqv (Native.evalWord w₂ (bV ())) &&
    (Native.evalWord w₁ (wV ())).eqv (Native.evalWord w₂ (wV ()))

theorem wordLin_apply_eq_of_eqv {w₁ w₂ : List Native.Gen}
    (h₁ : ∀ g ∈ w₁, g.validB = true) (h₂ : ∀ g ∈ w₂, g.validB = true) {v : Native.DVec}
    (h : (Native.evalWord w₁ v).eqv (Native.evalWord w₂ v) = true) :
    wordLin w₁ (interp v) = wordLin w₂ (interp v) := by
  rw [← evalWord_sound w₁ h₁ v, ← evalWord_sound w₂ h₂ v]
  exact eqv_sound h

theorem agree_sound
    {w₁ w₂ : List Native.Gen} (h : agree w₁ w₂ = true) : gw w₁ = gw w₂ := by
  unfold agree at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hv₁, hv₂⟩, ha⟩, hb⟩, hw⟩ := h
  have h₁ : ∀ g ∈ w₁, g.validB = true := fun g hg => List.all_eq_true.1 hv₁ g hg
  have h₂ : ∀ g ∈ w₂, g.validB = true := fun g hg => List.all_eq_true.1 hv₂ g hg
  have key : ∀ v, (Native.evalWord w₁ v).eqv (Native.evalWord w₂ v) = true →
      ((wordLin w₁)⁻¹ * wordLin w₂) (interp v) = interp v := by
    intro v hv
    have e := wordLin_apply_eq_of_eqv h₁ h₂ hv
    rw [LinearEquiv.mul_apply, ← e]
    exact (wordLin w₁).symm_apply_apply (interp v)
  have hmem : (wordLin w₁)⁻¹ * wordLin w₂ ∈ Gmat :=
    mul_mem (inv_mem (wordLin_mem_Gmat w₁)) (wordLin_mem_Gmat w₂)
  have h1 := separation_witnesses _ hmem (key _ ha) (key _ hb) (key _ hw)
  refine Subtype.ext ?_
  show wordLin w₁ = wordLin w₂
  exact (inv_mul_eq_one.1 h1)

@[expose] def agreeAll (ps : List (List Native.Gen × List Native.Gen)) : Bool :=
  ps.all fun p => agree p.1 p.2

theorem agreeAll_sound
    {ps : List (List Native.Gen × List Native.Gen)} (h : agreeAll ps = true) :
    ∀ p ∈ ps, gw p.1 = gw p.2 := fun p hp => agree_sound (List.all_eq_true.1 h p hp)

theorem gw_ne_one_of_moveCheck {w : List Native.Gen}
    {v : Native.DVec} (h : EdgeNoncomm.moveCheck w v = true) : gw w ≠ 1 := by
  intro h1
  apply EdgeNoncomm.moveCheck_sound h
  have : wordLin w = 1 := congrArg Subtype.val h1
  rw [this]
  rfl

inductive SLPStep where
  | gen (i : ℕ)
  | mul (i j : ℕ)
  | inv (i : ℕ)
  deriving Inhabited

@[expose] def entryWord (gens : Array (List Native.Gen))
    (steps : Array (SLPStep × List Native.Gen)) (k : ℕ) : List Native.Gen :=
  match steps[k]!.1 with
  | .gen i => gens[i]!
  | _ => steps[k]!.2

@[expose] def stepOK (gens : Array (List Native.Gen)) (steps : Array (SLPStep × List Native.Gen))
    (k : ℕ) : Bool :=
  match steps[k]!.1 with
  | .gen i => decide (i < gens.size)
  | .mul i j => decide (i < k) && decide (j < k) &&
      agree steps[k]!.2 (entryWord gens steps j ++ entryWord gens steps i)
  | .inv i => decide (i < k) && agree (steps[k]!.2 ++ entryWord gens steps i) []

@[expose] def stepsOK (gens : Array (List Native.Gen)) (steps : Array (SLPStep × List Native.Gen))
    (lo hi : ℕ) : Bool :=
  (List.range' lo (hi - lo)).all (stepOK gens steps)

theorem stepOK_of_stepsOK {gens : Array (List Native.Gen)}
    {steps : Array (SLPStep × List Native.Gen)} {lo hi k : ℕ} (h : stepsOK gens steps lo hi = true)
    (hlo : lo ≤ k) (hhi : k < hi) : stepOK gens steps k = true :=
  List.all_eq_true.1 h k (List.mem_range'_1.2 ⟨hlo, by omega⟩)

theorem mem_closure_of_stepOK
    {gens : Array (List Native.Gen)} {steps : Array (SLPStep × List Native.Gen)}
    (h : ∀ k < steps.size, stepOK gens steps k = true) :
    ∀ k < steps.size, gw (entryWord gens steps k) ∈
      Subgroup.closure (Set.range fun i : Fin gens.size => gw gens[i]) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hs := h k hk
    unfold stepOK at hs
    unfold entryWord
    rcases hstep : steps[k]!.1 with i | ⟨i, j⟩ | i
    · rw [hstep] at hs
      have hi : i < gens.size := of_decide_eq_true hs
      refine Subgroup.subset_closure ⟨⟨i, hi⟩, ?_⟩
      show gw gens[i] = gw gens[i]!
      rw [getElem!_pos gens i hi]
    · rw [hstep] at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨⟨hik, hjk⟩, hag⟩ := hs
      have e := agree_sound hag
      rw [gw_append] at e
      rw [e]
      exact mul_mem (ih i hik (by omega)) (ih j hjk (by omega))
    · rw [hstep] at hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨hik, hag⟩ := hs
      have e := agree_sound hag
      rw [gw_append, gw_nil] at e
      rw [eq_inv_of_mul_eq_one_right e]
      exact inv_mem (ih i hik (by omega))

end CFSG.AGLEmbedding.Norton.MON5_7
