module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def opOut : Op → Nat
  | .mul _ _ k => k
  | .pow _ _ k => k

@[expose] def ssaProg (prog : List Op) : Bool :=
  (List.range prog.length).all fun t => opOut (prog.getD t default) == t + 2

@[expose] def wordMax (w : Word) : Nat := w.foldl (fun m a => max m a.1) 0

@[expose] def factMax : MFact → Nat
  | .ord r _ => r
  | .conj h u w => max h (max (wordMax u) (wordMax w))
  | .ne w₁ w₂ _ => max (wordMax w₁) (wordMax w₂)
  | .eq w₁ w₂ => max (wordMax w₁) (wordMax w₂)

@[expose] def factsInRange {M V : Type} [Inhabited M] (O : Ops M V) (R : Array M) (nregs : Nat)
    (D : RSpec) (lo hi : Nat) : Bool :=
  D.facts.all fun f => !(decide (lo ≤ factMax f ∧ factMax f < hi)) || factOK O R nregs f

@[expose] def partCheck {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String) (nregs : Nat)
    (prog : List Op) (D : RSpec) (lo hi : Nat) : Bool :=
  factsInRange O (O.regsOf sA sB nregs (prog.take (hi - 2))) nregs D lo hi

@[expose] def partCheckFirst {M V : Type} [Inhabited M] (O : Ops M V) (sA sB : String)
    (nregs : Nat) (prog : List Op) (D : RSpec) (a b : Nat) : Bool :=
  let R := O.regsOf sA sB nregs (prog.take (a - 2))
  decide (2 ≤ a ∧ a ≤ b ∧ b ≤ nregs ∧ prog.length + 2 = nregs) && prog.all (Op.lt nregs) &&
  ssaProg prog && D.facts.all (fun f => decide (factMax f < nregs)) &&
  decide (D.rA < a ∧ D.rB < a) && O.eq R[D.rA]! (O.decode sA) && O.eq R[D.rB]! (O.decode sB) &&
  D.wf && factsInRange O R nregs D 0 a

section Proofs

variable {M V : Type} [Inhabited M] (O : Ops M V)

theorem getElem!_setIfInBounds_ne {α : Type} [Inhabited α] (R : Array α) (k r : Nat) (x : α)
    (h : k ≠ r) : (R.setIfInBounds k x)[r]! = R[r]! := by
  by_cases hr : r < R.size
  · have hr' : r < (R.setIfInBounds k x).size := by simpa using hr
    rw [getElem!_pos _ r hr', Array.getElem_setIfInBounds hr, getElem!_pos R r hr]
    simp [h]
  · have h2 : ¬ r < (R.setIfInBounds k x).size := by simpa using hr
    rw [getElem!_neg _ r h2, getElem!_neg R r hr]

theorem step_getElem!_ne (R : Array M) (op : Op) (r : Nat) (h : opOut op ≠ r) :
    (O.step R op)[r]! = R[r]! := by
  cases op with
  | mul i j k =>
    simp only [Ops.step, Array.set!_eq_setIfInBounds]
    exact getElem!_setIfInBounds_ne R k r _ h
  | pow e i k =>
    simp only [Ops.step, Array.set!_eq_setIfInBounds]
    exact getElem!_setIfInBounds_ne R k r _ h

theorem run_getElem!_of_out_ge :
    ∀ (L : List Op) (R : Array M) (m r : Nat), (∀ op ∈ L, m ≤ opOut op) → r < m →
      (O.run L R)[r]! = R[r]!
  | [], _, _, _, _, _ => rfl
  | op :: L, R, m, r, h, hr => by
    have h1 : opOut op ≠ r := by
      have := h op List.mem_cons_self
      omega
    have ih := run_getElem!_of_out_ge L (O.step R op) m r
      (fun op' h' => h op' (List.mem_cons_of_mem _ h')) hr
    simp only [Ops.run, List.foldl_cons] at ih ⊢
    rw [ih, step_getElem!_ne O R op r h1]

theorem opOut_of_ssaProg {prog : List Op} (h : ssaProg prog = true) (t : Nat)
    (ht : t < prog.length) : opOut prog[t] = t + 2 := by
  unfold ssaProg at h
  rw [List.all_eq_true] at h
  have := h t (List.mem_range.2 ht)
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some,
    beq_iff_eq] at this
  exact this

theorem regsOf_take_getElem! {prog : List Op} (hssa : ssaProg prog = true) (sA sB : String)
    (nregs n r : Nat) (hr : r < n + 2) :
    (O.regsOf sA sB nregs (prog.take n))[r]! = (O.regsOf sA sB nregs prog)[r]! := by
  have hout : ∀ op ∈ prog.drop n, n + 2 ≤ opOut op := by
    intro op hop
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hop
    have hi' : n + i < prog.length := by
      have := List.length_drop (l := prog) (i := n)
      omega
    have := opOut_of_ssaProg hssa (n + i) hi'
    rw [List.getElem_drop]
    omega
  have e : O.regsOf sA sB nregs prog =
      O.run (prog.drop n) (O.regsOf sA sB nregs (prog.take n)) := by
    unfold Ops.regsOf Ops.run
    rw [← List.foldl_append, List.take_append_drop]
  rw [e]
  exact (run_getElem!_of_out_ge O (prog.drop n) _ (n + 2) r hout hr).symm

theorem foldl_max_ge (w : Word) : ∀ (init : Nat),
    init ≤ w.foldl (fun m a => max m a.1) init ∧
      ∀ a ∈ w, a.1 ≤ w.foldl (fun m a => max m a.1) init := by
  induction w with
  | nil => intro init; exact ⟨Nat.le_refl _, fun a ha => absurd ha (by simp)⟩
  | cons b w ih =>
    intro init
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (max init b.1)
    refine ⟨by omega, fun a ha => ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · exact h2 a ha

theorem le_wordMax {w : Word} {a : Nat × Nat} (ha : a ∈ w) : a.1 ≤ wordMax w :=
  (foldl_max_ge w 0).2 a ha

theorem evalW_congr {R R' : Array M} :
    ∀ (w : Word), (∀ a ∈ w, R[a.1]! = R'[a.1]!) → evalW O R w = evalW O R' w
  | [], _ => rfl
  | a :: w, h => by
    simp only [evalW]
    rw [h a List.mem_cons_self, evalW_congr w (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem evalW_congr_of_le {R R' : Array M} (w : Word) (m : Nat) (hw : wordMax w ≤ m)
    (h : ∀ r ≤ m, R[r]! = R'[r]!) : evalW O R w = evalW O R' w :=
  evalW_congr O w fun a ha => h a.1 (Nat.le_trans (le_wordMax ha) hw)

theorem factOK_congr {R R' : Array M} (n : Nat) (f : MFact)
    (h : ∀ r ≤ factMax f, R[r]! = R'[r]!) : factOK O R n f = factOK O R' n f := by
  cases f with
  | ord r e => simp only [factOK]; rw [h r (Nat.le_refl _)]
  | conj k u w =>
    simp only [factMax] at h
    simp only [factOK]
    rw [h k (by omega), evalW_congr_of_le O u (max k (max (wordMax u) (wordMax w))) (by omega) h,
      evalW_congr_of_le O w (max k (max (wordMax u) (wordMax w))) (by omega) h]
  | ne w₁ w₂ t =>
    simp only [factMax] at h
    simp only [factOK]
    rw [evalW_congr_of_le O w₁ (max (wordMax w₁) (wordMax w₂)) (by omega) h,
      evalW_congr_of_le O w₂ (max (wordMax w₁) (wordMax w₂)) (by omega) h]
  | eq w₁ w₂ =>
    simp only [factMax] at h
    simp only [factOK]
    rw [evalW_congr_of_le O w₁ (max (wordMax w₁) (wordMax w₂)) (by omega) h,
      evalW_congr_of_le O w₂ (max (wordMax w₁) (wordMax w₂)) (by omega) h]

theorem factOK_of_factsInRange {prog : List Op} (hssa : ssaProg prog = true) (sA sB : String)
    (nregs lo hi : Nat) (D : RSpec) (hhi : 2 ≤ hi)
    (h : factsInRange O (O.regsOf sA sB nregs (prog.take (hi - 2))) nregs D lo hi = true)
    (f : MFact) (hf : f ∈ D.facts) (hlo : lo ≤ factMax f) (hhi' : factMax f < hi) :
    factOK O (O.regsOf sA sB nregs prog) nregs f = true := by
  unfold factsInRange at h
  rw [List.all_eq_true] at h
  have h1 := h f hf
  have hin : decide (lo ≤ factMax f ∧ factMax f < hi) = true := decide_eq_true ⟨hlo, hhi'⟩
  simp only [hin, Bool.not_true, Bool.false_or] at h1
  have hc : factOK O (O.regsOf sA sB nregs (prog.take (hi - 2))) nregs f =
      factOK O (O.regsOf sA sB nregs prog) nregs f :=
    factOK_congr O nregs f fun r hr =>
      regsOf_take_getElem! O hssa sA sB nregs (hi - 2) r (by omega)
  rw [← hc]
  exact h1

end Proofs

section Main

variable {M V : Type} [Inhabited M] (O : Ops M V)

theorem coreGenCheck_of_split (sA sB : String) (nregs : Nat) (prog : List Op) (D : RSpec)
    (a b : Nat)
    (h1 : partCheckFirst O sA sB nregs prog D a b = true)
    (h2 : partCheck O sA sB nregs prog D a b = true)
    (h3 : partCheck O sA sB nregs prog D b nregs = true) :
    coreGenCheck O sA sB nregs prog D = true := by
  unfold partCheckFirst at h1
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hab, hprog⟩, hssa⟩, hmax⟩, hr⟩, hA⟩, hB⟩, hwf⟩, hfirst⟩ := h1
  obtain ⟨ha2, hab', hbn, hlen⟩ := hab
  obtain ⟨hrA, hrB⟩ := hr
  have hfirst' : factsInRange O (O.regsOf sA sB nregs (prog.take (a - 2))) nregs D 0 a = true :=
    hfirst
  have h2' : factsInRange O (O.regsOf sA sB nregs (prog.take (b - 2))) nregs D a b = true := h2
  have h3' : factsInRange O (O.regsOf sA sB nregs (prog.take (nregs - 2))) nregs D b nregs =
      true := h3
  unfold coreGenCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by omega, hprog⟩, ?_⟩, by omega⟩, by omega⟩, ?_⟩, ?_⟩, hwf⟩
  · intro f hf
    have hm := hmax f hf
    by_cases hc1 : factMax f < a
    · exact factOK_of_factsInRange O hssa sA sB nregs 0 a D ha2 hfirst' f hf (Nat.zero_le _) hc1
    · by_cases hc2 : factMax f < b
      · exact factOK_of_factsInRange O hssa sA sB nregs a b D (by omega) h2' f hf (by omega) hc2
      · exact factOK_of_factsInRange O hssa sA sB nregs b nregs D (by omega) h3' f hf
          (by omega) hm
  · have := regsOf_take_getElem! O hssa sA sB nregs (a - 2) D.rA (by omega)
    rw [← this]
    exact hA
  · have := regsOf_take_getElem! O hssa sA sB nregs (a - 2) D.rB (by omega)
    rw [← this]
    exact hB

end Main

end CFSG.AGLEmbedding.R3
