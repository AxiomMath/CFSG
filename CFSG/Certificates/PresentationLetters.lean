module

public import CFSG.Certificates.CosetFacts
public import Mathlib.GroupTheory.PresentedGroup

public section

namespace CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

noncomputable def presLetter (rels : Set (FreeGroup (Fin m))) (c : ℕ) : PresentedGroup rels :=
  if h : c / 2 < m then
    (if c % 2 = 0 then PresentedGroup.of ⟨c / 2, h⟩ else (PresentedGroup.of ⟨c / 2, h⟩)⁻¹)
  else 1

@[expose] def letterCode (x : Fin m × Bool) : ℕ := 2 * x.1.val + (if x.2 then 0 else 1)

@[expose] def invCode (c : ℕ) : ℕ := cond (Nat.beq (Nat.mod c 2) 0) (Nat.succ c) (Nat.pred c)

private theorem beq_mod_two_true {c : ℕ} (h : c % 2 = 0) : Nat.beq (Nat.mod c 2) 0 = true := by
  rw [Nat.beq_eq]; exact h

private theorem beq_mod_two_false {c : ℕ} (h : c % 2 = 1) : Nat.beq (Nat.mod c 2) 0 = false := by
  cases hb : Nat.beq (Nat.mod c 2) 0 with
  | false => rfl
  | true =>
    have : c % 2 = 0 := Nat.eq_of_beq_eq_true hb
    omega

theorem invCode_lt {c : ℕ} (hc : c < 2 * m) : invCode c < 2 * m := by
  unfold invCode
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [beq_mod_two_true h, Bool.cond_true, Nat.succ_eq_add_one]; omega
  · rw [beq_mod_two_false h, Bool.cond_false, Nat.pred_eq_sub_one]; omega

theorem presLetter_invCode (rels : Set (FreeGroup (Fin m))) {c : ℕ} (hc : c < 2 * m) :
    presLetter rels (invCode c) = (presLetter rels c)⁻¹ := by
  have h2 : c / 2 < m := by omega
  unfold invCode
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · rw [beq_mod_two_true h, Bool.cond_true, Nat.succ_eq_add_one]
    have h1 : (c + 1) / 2 = c / 2 := by omega
    have h3 : (c + 1) % 2 ≠ 0 := by omega
    have h1' : (c + 1) / 2 < m := by omega
    unfold presLetter
    rw [dite_eq_left h1', dite_eq_left h2, ite_eq_right h3, ite_eq_left h]
    congr 2
    exact Fin.ext h1
  · rw [beq_mod_two_false h, Bool.cond_false, Nat.pred_eq_sub_one]
    have h1 : (c - 1) / 2 = c / 2 := by omega
    have h3 : (c - 1) % 2 = 0 := by omega
    have h4 : c % 2 ≠ 0 := by omega
    have h1' : (c - 1) / 2 < m := by omega
    unfold presLetter
    rw [dite_eq_left h1', dite_eq_left h2, ite_eq_left h3, ite_eq_right h4, inv_inv]
    congr 1
    exact Fin.ext h1

theorem presLetter_letterCode (rels : Set (FreeGroup (Fin m))) (x : Fin m × Bool) :
    presLetter rels (letterCode x) = PresentedGroup.mk rels (FreeGroup.mk [x]) := by
  obtain ⟨i, b⟩ := x
  have hdiv : (2 * i.val + (if b then 0 else 1)) / 2 = i.val := by split <;> omega
  have hi : (2 * i.val + (if b then 0 else 1)) / 2 < m := by rw [hdiv]; exact i.isLt
  have hfin : (⟨(2 * i.val + (if b then 0 else 1)) / 2, hi⟩ : Fin m) = i := Fin.ext hdiv
  unfold presLetter letterCode
  rw [dite_eq_left hi, hfin]
  cases b with
  | true =>
    have : (2 * i.val + (if true = true then 0 else 1)) % 2 = 0 := by simp
    rw [ite_eq_left this]
    rfl
  | false =>
    have : ¬ (2 * i.val + (if false = true then 0 else 1)) % 2 = 0 := by simp
    rw [ite_eq_right this, show FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ from rfl, map_inv]
    rfl

theorem evalWord_presLetter (rels : Set (FreeGroup (Fin m))) (w : List (Fin m × Bool)) :
    evalWord (presLetter rels) (w.map letterCode) = PresentedGroup.mk rels (FreeGroup.mk w) := by
  induction w with
  | nil => simp; rfl
  | cons x w ih =>
    rw [List.map_cons, evalWord_cons, ih, presLetter_letterCode, ← map_mul, FreeGroup.mul_mk]
    rfl

theorem closure_presLetter (rels : Set (FreeGroup (Fin m))) :
    Subgroup.closure (presLetter rels '' Set.Iio (2 * m)) = ⊤ := by
  rw [eq_top_iff, ← PresentedGroup.closure_range_of]
  apply Subgroup.closure_le _ |>.mpr
  rintro _ ⟨i, rfl⟩
  apply Subgroup.subset_closure
  refine ⟨2 * i.val, by simp, ?_⟩
  have h : presLetter rels (letterCode (i, true)) = PresentedGroup.of i := by
    rw [presLetter_letterCode]; rfl
  simpa [letterCode] using h

@[expose] def codes (ws : List (List (Fin m × Bool))) : List (List ℕ) :=
  ws.map (List.map letterCode)

theorem lettersOK_codes (ws : List (List (Fin m × Bool))) : lettersOK (2 * m) (codes ws) = true := by
  simp only [lettersOK, codes, List.all_map, List.all_eq_true, Function.comp_apply, Nat.blt_eq]
  intro w _ x _
  obtain ⟨i, b⟩ := x
  simp only [letterCode]
  split <;> omega

theorem presLetter_eps (rels : Set (FreeGroup (Fin m))) : presLetter rels (2 * m) = 1 := by
  unfold presLetter
  rw [dite_eq_right (by omega)]

@[expose] def invLetter (m c : ℕ) : ℕ := cond (Nat.blt c (2 * m)) (invCode c) c

theorem invLetter_lt {c : ℕ} (hc : c < 2 * m) : invLetter m c < 2 * m := by
  unfold invLetter
  rw [show Nat.blt c (2 * m) = true by rw [Nat.blt_eq]; exact hc, Bool.cond_true]
  exact invCode_lt hc

theorem presLetter_invLetter (rels : Set (FreeGroup (Fin m))) {c : ℕ} (hc : c ≤ 2 * m) :
    presLetter rels (invLetter m c) = (presLetter rels c)⁻¹ := by
  unfold invLetter
  rcases Nat.lt_or_eq_of_le hc with hlt | heq
  · rw [show Nat.blt c (2 * m) = true by rw [Nat.blt_eq]; exact hlt, Bool.cond_true]
    exact presLetter_invCode rels hlt
  · subst heq
    rw [show Nat.blt (2 * m) (2 * m) = false by
      cases h : Nat.blt (2 * m) (2 * m) with
      | false => rfl
      | true => rw [Nat.blt_eq] at h; omega, Bool.cond_false, presLetter_eps, inv_one]

theorem index_le_of_facts_presented {rels : Set (FreeGroup (Fin m))}
    {H : Subgroup (PresentedGroup rels)} {N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl ffi : ℕ → ℕ} {live : ℕ → Bool}
    (relWords subWords : List (List (Fin m × Bool))) (ws : List (List ℕ))
    (hrels : ∀ w ∈ relWords, FreeGroup.mk w ∈ rels)
    (hsubs : ∀ w ∈ subWords, PresentedGroup.mk rels (FreeGroup.mk w) ∈ H)
    (hws : derivedOK (2 * m) (invLetter m) (codes relWords) ws = true)
    (hlive0 : live 0 = true) (hN : 0 < N)
    (hfacts : factsOK N (2 * m + 1) fx fc fy kind wi fs ft fo refs pl (invLetter m) ws
      (codes subWords) 0 F = true)
    (hcover : coverOK N (2 * m) F fx fc fy (invLetter m) ffi live 0 (N * (2 * m)) = true) :
    H.FiniteIndex ∧ H.index ≤ liveCount live N := by
  have hbase : ∀ r ∈ codes relWords, evalWord (presLetter rels) r = 1 := by
    intro w hw
    simp only [codes, List.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [evalWord_presLetter]
    exact PresentedGroup.one_of_mem (hrels v hv)
  have hlet : ∀ w ∈ ws ++ codes subWords, ∀ c ∈ w, c ≤ 2 * m := by
    intro w hw c hc
    rcases List.mem_append.mp hw with hw | hw
    · simp only [derivedOK, List.all_eq_true, Bool.and_eq_true, Nat.blt_eq] at hws
      exact Nat.lt_succ_iff.mp ((hws w hw).1 c hc)
    · have := lettersOK_codes subWords
      simp only [lettersOK, List.all_eq_true, Nat.blt_eq] at this
      exact Nat.le_of_lt (this w hw c hc)
  refine index_le_of_facts (gen := presLetter rels) (inv := invLetter m)
    (closure_presLetter rels) (fun c hc => presLetter_invLetter rels hc)
    (fun c hc => invLetter_lt hc) hlet
    (evalWord_of_derivedOK (presLetter_eps rels)
      (fun c hc => presLetter_invLetter rels (Nat.le_of_lt hc)) hbase hws) ?_ hlive0 hN hfacts
    hcover
  intro w hw
  simp only [codes, List.mem_map] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [evalWord_presLetter]
  exact hsubs v hv

theorem card_le_of_facts_presented {rels : Set (FreeGroup (Fin m))} {N F : ℕ}
    {fx fc fy kind wi fs ft fo refs pl ffi : ℕ → ℕ} {live : ℕ → Bool}
    (relWords : List (List (Fin m × Bool))) (ws : List (List ℕ))
    (hrels : ∀ w ∈ relWords, FreeGroup.mk w ∈ rels)
    (hws : derivedOK (2 * m) (invLetter m) (codes relWords) ws = true)
    (hlive0 : live 0 = true) (hN : 0 < N)
    (hfacts : factsOK N (2 * m + 1) fx fc fy kind wi fs ft fo refs pl (invLetter m) ws [] 0 F =
      true)
    (hcover : coverOK N (2 * m) F fx fc fy (invLetter m) ffi live 0 (N * (2 * m)) = true) :
    Finite (PresentedGroup rels) ∧ Nat.card (PresentedGroup rels) ≤ liveCount live N := by
  obtain ⟨h1, h2⟩ := index_le_of_facts_presented (H := ⊥) relWords [] ws hrels (by simp) hws
    hlive0 hN hfacts hcover
  rw [Subgroup.index_bot] at h2
  refine ⟨?_, h2⟩
  have := h1.index_ne_zero
  rw [Subgroup.index_bot] at this
  exact Nat.finite_of_card_ne_zero this

end CFSG.Certificates.CosetEnumeration
