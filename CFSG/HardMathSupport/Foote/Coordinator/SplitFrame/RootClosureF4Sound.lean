module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4Pair
import all CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.RootClosureF4
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectionF4

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

namespace F4Closure

theorem ofFn_lin (a b : ℤ) (v w : Fin Tag.F4.rank → ℤ) :
    lin a b (List.ofFn v) (List.ofFn w) = List.ofFn (fun i => a * v i + b * w i) := by
  apply List.ext_getElem
  · simp [lin]
  · intro n h1 h2
    simp [lin]

theorem inS_ofFn (v : Fin Tag.F4.rank → ℤ) : inS (List.ofFn v) = true ↔ (3 : ℤ) ∣ v 1 := by
  have hlt : 1 < Tag.F4.rank := by decide
  have h1 : (List.ofFn v).getD 1 0 = v 1 := by
    simp [List.getD_eq_getElem?_getD, hlt] <;> rfl
  simp only [inS, h1, beq_iff_eq]
  omega

section Certs113


theorem isR_ofFn (v : Fin Tag.F4.rank → ℤ) : isR (List.ofFn v) = true ↔ IsRoot Tag.F4 v := by
  rw [(f4_root_certificate.1 v)]
  simp [isR]

theorem commPairs_eq_pairsL (v w : Fin Tag.F4.rank → ℤ) :
    commPairs .F4 v w = pairsL (List.ofFn v) (List.ofFn w) := by
  classical
  unfold commPairs pairsL
  refine List.filter_congr fun p _ => ?_
  have h : (p.1 • v + p.2 • w) = fun i => (p.1 : ℤ) * v i + (p.2 : ℤ) * w i := by
    funext i
    simp
  rw [ofFn_lin, ← h, Bool.eq_iff_iff, decide_eq_true_iff, isR_ofFn]

def PL (K : Type) [Field K] (H : Subgroup (ModGL Tag.F4 K)) (l : List ℤ) : Prop :=
  ∃ v : Fin Tag.F4.rank → ℤ, List.ofFn v = l ∧ IsRoot Tag.F4 v ∧ rootSubgroup Tag.F4 K v ≤ H

theorem PL_of_S0 {K : Type} [Field K] (H : Subgroup (ModGL Tag.F4 K))
    (hX : rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) ≤ H) {l : List ℤ} (hl : l ∈ S0) :
    PL K H l := by
  obtain ⟨hmem, hin⟩ := List.mem_filter.1 hl
  obtain ⟨v, rfl⟩ := exists_ofFn_of_length l Tag.F4.rank (f4_root_certificate.2.1 l hmem)
  have hroot : IsRoot Tag.F4 v := (f4_root_certificate.1 v).2 hmem
  have h3 : (3 : ℤ) ∣ v 1 := (inS_ofFn v).1 hin
  have hmemS : v ∈ cosetRoots Tag.F4 1 3 := ⟨hroot, by exact_mod_cast h3⟩
  exact ⟨v, rfl, hroot, (le_biSup (rootSubgroup Tag.F4 K) hmemS).trans hX⟩

end Certs113

section CertsAll


theorem stepNew_sound {K : Type} [Field K] {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (H : Subgroup (ModGL Tag.F4 K)) {a b : List ℤ} {k : ℕ} (ha : PL K H a) (hb : PL K H b)
    (hs : stepOK a b k = true) : ∀ x ∈ stepNew a b k, PL K H x := by
  obtain ⟨va, rfl, hva, hA⟩ := ha
  obtain ⟨vb, rfl, hvb, hB⟩ := hb
  have e11 : lin 1 1 (List.ofFn va) (List.ofFn vb) = List.ofFn (va + vb) := by
    rw [ofFn_lin]
    congr 1
    funext i
    simp
  have e12 : lin 1 2 (List.ofFn va) (List.ofFn vb) = List.ofFn (va + 2 • vb) := by
    rw [ofFn_lin]
    congr 1
    funext i
    simp
  have e1m2 : lin (-1) (-2) (List.ofFn va) (List.ofFn vb) = List.ofFn (-(va + 2 • vb)) := by
    rw [ofFn_lin]
    congr 1
    funext i
    simp
    ring
  have em11 : lin (-1) 1 (List.ofFn va) (List.ofFn vb) = List.ofFn (vb - va) := by
    rw [ofFn_lin]
    congr 1
    funext i
    simp
    ring
  unfold stepOK at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hs
  obtain ⟨⟨hab, hnr⟩, ⟨rfl, hP⟩ | ⟨⟨⟨⟨rfl, hP⟩, hn1⟩, hn2⟩, hP2⟩⟩ := hs
  · have hne : va ≠ vb := fun h => hab (by rw [h])
    have hnr' : ¬ IsRoot Tag.F4 (vb - va) := by
      rw [← isR_ofFn, ← em11]
      simpa using hnr
    have hP' : commPairs .F4 va vb = [(1, 1)] := by
      rw [commPairs_eq_pairsL]
      exact hP
    have hr11 : IsRoot Tag.F4 (va + vb) := by
      have h := (mem_commPairs.1
        (by rw [hP']; simp : ((1 : ℕ), (1 : ℕ)) ∈ commPairs .F4 va vb)).2
      simpa using h
    have hsub := rootSubgroup_add_le_single H hva hvb hne hP' hnr' hA hB
    have hnew : stepNew (List.ofFn va) (List.ofFn vb) 1 = [lin 1 1 (List.ofFn va) (List.ofFn vb)] := by
      simp [stepNew]
    intro x hx
    rw [hnew, List.mem_singleton] at hx
    subst hx
    exact ⟨va + vb, e11.symm, hr11, hsub⟩
  · have hne : va ≠ vb := fun h => hab (by rw [h])
    have hnr' : ¬ IsRoot Tag.F4 (vb - va) := by
      rw [← isR_ofFn, ← em11]
      simpa using hnr
    have hP' : commPairs .F4 va vb = [(1, 1), (1, 2)] := by
      rw [commPairs_eq_pairsL]
      exact hP
    have hne₂ : va + vb ≠ va + 2 • vb := by
      intro h
      apply hn1
      rw [e11, e12, h]
    have hne₃ : va + vb ≠ -(va + 2 • vb) := by
      intro h
      apply hn2
      rw [e11, e1m2, h]
    have hP₂ : commPairs .F4 (va + vb) (va + 2 • vb) = [] := by
      rw [commPairs_eq_pairsL, ← e11, ← e12]
      exact hP2
    have hr11 : IsRoot Tag.F4 (va + vb) := by
      have h := (mem_commPairs.1
        (by rw [hP']; simp : ((1 : ℕ), (1 : ℕ)) ∈ commPairs .F4 va vb)).2
      simpa using h
    have hr12 : IsRoot Tag.F4 (va + 2 • vb) := by
      have h := (mem_commPairs.1
        (by rw [hP']; simp : ((1 : ℕ), (2 : ℕ)) ∈ commPairs .F4 va vb)).2
      simpa using h
    obtain ⟨hsub1, hsub2⟩ :=
      rootSubgroup_add_le_double ht0 ht1 H hva hvb hne hP' hnr' hne₂ hne₃ hP₂ hA hB
    have hnew : stepNew (List.ofFn va) (List.ofFn vb) 2 =
        [lin 1 1 (List.ofFn va) (List.ofFn vb), lin 1 2 (List.ofFn va) (List.ofFn vb)] := by
      simp [stepNew]
    intro x hx
    rw [hnew] at hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨va + vb, e11.symm, hr11, hsub1⟩
    · exact ⟨va + 2 • vb, e12.symm, hr12, hsub2⟩

theorem runSteps_sound {K : Type} [Field K] {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (H : Subgroup (ModGL Tag.F4 K)) (L : List (ℕ × ℕ × ℕ)) :
    ∀ (D D' : List (List ℤ)), (∀ x ∈ D, PL K H x) →
      runSteps D L = some D' → ∀ x ∈ D', PL K H x := by
  induction L with
  | nil =>
    intro D D' hD h
    simp only [runSteps, Option.some.injEq] at h
    subst h
    exact hD
  | cons p L ih =>
    obtain ⟨i, j, k⟩ := p
    intro D D' hD h
    simp only [runSteps] at h
    split at h
    · rename_i a b ha hb
      by_cases hc : stepOK a b k = true
      · rw [if_pos hc] at h
        have hnew : ∀ x ∈ D ++ stepNew a b k, PL K H x := by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hD x hx
          · exact stepNew_sound ht0 ht1 H (hD a (List.mem_of_getElem? ha))
              (hD b (List.mem_of_getElem? hb)) hc x hx
        exact ih _ _ hnew h
      · rw [if_neg hc] at h
        simp at h
    · simp at h

theorem all_PL {K : Type} [Field K] {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (H : Subgroup (ModGL Tag.F4 K)) (hX : rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) ≤ H)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hβS : β ∉ cosetRoots Tag.F4 1 3)
    (hU : rootSubgroup Tag.F4 K β ≤ H) : ∀ x ∈ rootsL, PL K H x := by
  have hβin : inS (List.ofFn β) = false := by
    cases h : inS (List.ofFn β)
    · rfl
    · exact absurd ((inS_ofFn β).1 h) (fun hd => hβS ⟨hβ, by exact_mod_cast hd⟩)
  have hmem : List.ofFn β ∈ rootsL.filter fun x => !inS x := by
    rw [List.mem_filter]
    exact ⟨(f4_root_certificate.1 β).1 hβ, by simp [hβin]⟩
  have h := List.all_eq_true.1 tableOK_eq (List.ofFn β) hmem
  obtain ⟨L, hL⟩ : ∃ L, tableF4.lookup (List.ofFn β) = some L := by
    cases hT : tableF4.lookup (List.ofFn β) with
    | none => simp [hT] at h
    | some L => exact ⟨L, rfl⟩
  simp only [hL] at h
  unfold coverOK at h
  split at h
  · rename_i D hD
    have hS : ∀ l ∈ S0, PL K H l := fun l hl => PL_of_S0 H hX hl
    have hdom : ∀ x ∈ S0 ++ [List.ofFn β], PL K H x := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hS x hx
      · rw [List.mem_singleton] at hx
        rw [hx]
        exact ⟨β, rfl, hβ, hU⟩
    have hall := runSteps_sound ht0 ht1 H L (S0 ++ [List.ofFn β]) D hdom hD
    intro x hx
    exact hall x (mem_of_contains (List.all_eq_true.1 h x hx))
  · simp at h

end CertsAll

end F4Closure

section Closing


theorem eq_top_of_rootSubgroup_le_F4 {K : Type} [Field K] {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (H : Subgroup (ModGL Tag.F4 K)) (hH : H ≤ adjointGroup Tag.F4 K)
    (hX : rootSpan Tag.F4 K (cosetRoots Tag.F4 1 3) ≤ H)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hβS : β ∉ cosetRoots Tag.F4 1 3)
    (hU : rootSubgroup Tag.F4 K β ≤ H) : H = adjointGroup Tag.F4 K := by
  have hall := F4Closure.all_PL ht0 ht1 H hX hβ hβS hU
  refine le_antisymm hH ?_
  rw [adjointGroup_eq_rootSpan]
  refine iSup₂_le fun v hv => ?_
  obtain ⟨u, hu, -, hsub⟩ := hall (List.ofFn v)
    ((f4_root_certificate.1 v).1 (show IsRoot Tag.F4 v from hv))
  have huv : u = v := List.ofFn_injective hu
  subst huv
  exact hsub

end Closing

section Detection


theorem frameClosing_of_detection_F4 (K : Type) [Field K] [Finite K] (hK : 3 ≤ Nat.card K)
    (hD : FrameDetection .F4 K (cosetRoots .F4 1 3)) :
    FrameClosing .F4 K (cosetRoots .F4 1 3) := by
  obtain ⟨t, ht0, ht1⟩ : ∃ t : K, t ≠ 0 ∧ t ≠ 1 := by
    by_contra hex
    have hcon : ∀ x : K, x ≠ 0 → x = 1 := fun x hx => by
      by_contra h1
      exact hex ⟨x, hx, h1⟩
    classical
    haveI := Fintype.ofFinite K
    have h2 : Fintype.card K ≤ 2 := by
      calc Fintype.card K = (Finset.univ : Finset K).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset K).card := by
          refine Finset.card_le_card fun x _ => ?_
          by_cases hx : x = 0
          · simp [hx]
          · simp [hcon x hx]
        _ ≤ 2 := Finset.card_le_two
    rw [Nat.card_eq_fintype_card] at hK
    omega
  intro H hH hX hN
  obtain ⟨β, hβ, hβS, hU⟩ := exists_rootSubgroup_le_of_detection_F4 K hD hH hX hN
  exact eq_top_of_rootSubgroup_le_F4 ht0 ht1 H hH hX hβ hβS hU

end Detection

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
