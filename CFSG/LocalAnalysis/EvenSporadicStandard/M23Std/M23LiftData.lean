module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.M23FusionData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.LiftCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.LiftData

public section

namespace CFSG.EvenSporadicStandard.M23Std

open CFSG.EvenSporadicStandard.Wong77 CFSG.EvenSporadicStandard.Wong77.M23Sylow
  CFSG.EvenSporadicStandard.M23Std.FusionCheck CFSG.EvenSporadicStandard.M23Std.LiftCheck
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 100000 in
theorem liftCheck_true : liftCheck = true := by decide

theorem liftCheck_spec :
    (isInv lb1Tab = true ∧ isInv lb2Tab = true ∧ M23Sylow.comm lb1Tab lb2Tab = true ∧
      normOK (elemTabs 1) lb1Tab = true ∧ normOK (elemTabs 1) lb2Tab = true) ∧
    ((∀ c c' : Fin 4 → ZMod 2, monoTab basisTabs c = monoTab basisTabs c' → c = c') ∧
      (∀ y ∈ idTab :: elemTabs 1, ∃ c : Fin 4 → ZMod 2, monoTab basisTabs c = y)) ∧
    (∀ i : Fin 4, tmul (tmul lb1Tab (basisTabs i)) lb1Tab = monoTab basisTabs (liftA1 i) ∧
      tmul (tmul lb2Tab (basisTabs i)) lb2Tab = monoTab basisTabs (liftA2 i)) := by
  have h := liftCheck_true
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

@[expose] def lfEl (i : Nat) : Carrier .M23 := (invs16 1).getD (basisIdx.getD i 0) 1

@[expose] def b1El : Carrier .M23 := wordElt [genA, genB, genBi] b1Word

@[expose] def b2El : Carrier .M23 := wordElt [genA, genB, genBi] b2Word

theorem tab_lfEl (i : Fin 4) : tab (lfEl i.val) = basisTabs i := by
  rw [lfEl, tab_getD, tab_invs16]
  rfl

theorem tab_b1El : tab b1El = lb1Tab := by
  rw [b1El, tab_wordElt, tab_letters]
  rfl

theorem tab_b2El : tab b2El = lb2Tab := by
  rw [b2El, tab_wordElt, tab_letters]
  rfl

theorem lfEl_mem (i : Fin 4) : lfEl i.val ∈ invs16 1 := by
  have hlen := (invs16_spec 1).1
  have hi : basisIdx.getD i.val 0 < (invs16 1).length := by
    rw [hlen]
    fin_cases i <;> decide
  rw [lfEl, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem _

theorem tab_pow (g : Carrier .M23) (n : Nat) : tab (g ^ n) = powTab (tab g) n := by
  induction n with
  | zero => simp [powTab, tab_one]
  | succ n ih => rw [pow_succ', tab_mul, ih, powTab]

theorem tab_mon4 (f : Fin 4 → Carrier .M23) (c : Fin 4 → ZMod 2) :
    tab (mon4 f c) = monoTab (fun i => tab (f i)) c := by
  simp only [mon4, monoTab, tab_mul, tab_pow]

theorem liftData_pinned {F1 : Subgroup (Carrier .M23)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    LiftData (⊤ : Subgroup (Carrier .M23)) F1 := by
  obtain ⟨⟨hb1, hb2, hbc, hn1, hn2⟩, ⟨hinj, hcov⟩, hact⟩ := liftCheck_spec
  let f : Fin 4 → Carrier .M23 := fun i => lfEl i.val
  have htf : (fun i => tab (f i)) = basisTabs := funext tab_lfEl
  have hmono : ∀ c, tab (mon4 f c) = monoTab basisTabs c := fun c => by
    rw [tab_mon4, htf]
  have hsq : ∀ {b : Carrier .M23} {t : Tab}, tab b = t → isInv t = true → b * b = 1 := by
    intro b t hbt hinv
    unfold isInv at hinv
    have h2 := (of_decide_eq_true hinv).2
    exact tab_injective (by rw [tab_mul, tab_one, hbt]; exact h2)
  have hb1sq : b1El * b1El = 1 := hsq tab_b1El hb1
  have hb2sq : b2El * b2El = 1 := hsq tab_b2El hb2
  have hb1inv : b1El⁻¹ = b1El := inv_eq_of_mul_eq_one_right hb1sq
  have hb2inv : b2El⁻¹ = b2El := inv_eq_of_mul_eq_one_right hb2sq
  refine ⟨⟨f, b1El, b2El, fun i => (hmem1 _).2 (Or.inr (lfEl_mem i)), ?_, ?_,
    Subgroup.mem_top _, Subgroup.mem_top _,
    normalizes_of_normOK hmem1 (by rw [tab_b1El]; exact hn1),
    normalizes_of_normOK hmem1 (by rw [tab_b2El]; exact hn2), hb1sq, hb2sq, ?_, ?_, ?_⟩⟩
  · intro x hx
    have hxt : tab x ∈ idTab :: elemTabs 1 := by
      rcases (hmem1 x).1 hx with rfl | hxm
      · rw [tab_one]
        exact List.mem_cons_self
      · refine List.mem_cons_of_mem _ ?_
        rw [← tab_invs16]
        exact List.mem_map_of_mem hxm
    obtain ⟨c, hc⟩ := hcov _ hxt
    exact ⟨c, tab_injective (by rw [hmono, hc])⟩
  · intro c c' hcc
    exact hinj c c' (by rw [← hmono, ← hmono, hcc])
  · have h2 : tmul lb1Tab lb2Tab = tmul lb2Tab lb1Tab := by
      unfold M23Sylow.comm at hbc
      exact of_decide_eq_true hbc
    exact tab_injective (by rw [tab_mul, tab_mul, tab_b1El, tab_b2El]; exact h2)
  · intro i
    apply tab_injective
    rw [hb1inv, tab_mul, tab_mul, tab_b1El, hmono, tab_lfEl]
    exact (hact i).1
  · intro i
    apply tab_injective
    rw [hb2inv, tab_mul, tab_mul, tab_b2El, hmono, tab_lfEl]
    exact (hact i).2

end CFSG.EvenSporadicStandard.M23Std
