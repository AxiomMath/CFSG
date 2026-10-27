module

public import Certificates.Data.Kernel.SmithL6KOp
public import CFSG.Certificates.Kernel.SmithL6KGSound
public import CFSG.Certificates.Kernel.SmithL6KTSound

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

theorem tvF_xor (p : Nat × Nat) (φ φ' : Nat) : tvF p (φ ^^^ φ') = tvF p φ ^^^ tvF p φ' := by
  unfold tvF
  rw [form_xor_left]
  cases form φ p.1 <;> cases form φ' p.1 <;>
    simp only [Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] <;>
    (apply Nat.eq_of_testBit_eq
     intro i
     simp only [Nat.testBit_xor]
     cases φ.testBit i <;> cases φ'.testBit i <;> cases p.2.testBit i <;> rfl)

theorem wordV_xor (w : List (Nat × Nat)) (x y : Nat) :
    wordV w (x ^^^ y) = wordV w x ^^^ wordV w y := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change tvA p (wordV w (x ^^^ y)) = tvA p (wordV w x) ^^^ tvA p (wordV w y)
    rw [ih, tvA_xor]

theorem wordF_xor (w : List (Nat × Nat)) (x y : Nat) :
    wordF w (x ^^^ y) = wordF w x ^^^ wordF w y := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    change tvF p (wordF w (x ^^^ y)) = tvF p (wordF w x) ^^^ tvF p (wordF w y)
    rw [ih, tvF_xor]

theorem wordId_basis {w : List (Nat × Nat)} (h : wordId w = true) :
    ∀ m < 6, wordV w (2 ^ m) = 2 ^ m ∧ wordF w (2 ^ m) = 2 ^ m := by
  unfold wordId at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem wordV_eq_self {w : List (Nat × Nat)} (h : wordId w = true) {x : Nat} (hx : x < 64) :
    wordV w x = x :=
  xorAdd_ext (G := fun x => x) (wordV_xor w) (fun _ _ => rfl) 6
    (fun m hm => (wordId_basis h m hm).1) x hx

theorem wordF_eq_self {w : List (Nat × Nat)} (h : wordId w = true) {x : Nat} (hx : x < 64) :
    wordF w x = x :=
  xorAdd_ext (G := fun x => x) (wordF_xor w) (fun _ _ => rfl) 6
    (fun m hm => (wordId_basis h m hm).2) x hx

theorem foldr_altW3 {α β : Type} (f : α → β → β) (p q : α) (x : β) :
    (altW p q 3).foldr f x = f p (f q (f p (f q (f p (f q x))))) := rfl

theorem foldr_altW4 {α β : Type} (f : α → β → β) (p q : α) (x : β) :
    (altW p q 4).foldr f x = f p (f q (f p (f q (f p (f q (f p (f q x))))))) := rfl

@[expose] def wordP (w : List (Nat × Nat)) (q : Nat × Nat) : Nat × Nat := (wordV w q.1, wordF w q.2)

theorem wordP_nil (q : Nat × Nat) : wordP [] q = q := rfl

theorem wordP_cons (p : Nat × Nat) (w : List (Nat × Nat)) (q : Nat × Nat) :
    wordP (p :: w) q = conjP p (wordP w q) := rfl

theorem wordP_self {w : List (Nat × Nat)} (hw : wordId w = true) {q : Nat × Nat} (h1 : q.1 < 64)
    (h2 : q.2 < 64) : wordP w q = q := by
  unfold wordP
  rw [wordV_eq_self hw h1, wordF_eq_self hw h2]

theorem tvPair_foldr {gs : List Nat} (hg : ∀ g ∈ gs, g < 1953) {x : Nat} (hx : x < 1953) :
    gs.foldr tvImg x < 1953 ∧ tvPair (gs.foldr tvImg x) = wordP (gs.map tvPair) (tvPair x) := by
  induction gs with
  | nil => exact ⟨hx, (wordP_nil _).symm⟩
  | cons g gs ih =>
    obtain ⟨h1, h2⟩ := ih fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')
    have hg0 := hg g List.mem_cons_self
    rw [List.foldr_cons, List.map_cons, wordP_cons]
    exact ⟨tvImg_lt hg0 h1, by rw [tvPair_tvImg hg0 h1, h2]⟩

theorem foldr_tvImg_self {gs : List Nat} (hg : ∀ g ∈ gs, g < 1953)
    (hw : wordId (gs.map tvPair) = true) {x : Nat} (hx : x < 1953) : gs.foldr tvImg x = x := by
  obtain ⟨h1, h2⟩ := tvPair_foldr hg hx
  have hp := tvP_tvPair hx
  rw [wordP_self hw hp.1 hp.2.1] at h2
  exact codeOf_tvPair_inj h1 hx (congrArg codeOf h2)

theorem altW_map {α β : Type} (f : α → β) (p q : α) (n : Nat) :
    (altW p q n).map f = altW (f p) (f q) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [altW, List.map_cons, ih]

theorem altW_mem {α : Type} {p q g : α} {n : Nat} (h : g ∈ altW p q n) : g = p ∨ g = q := by
  induction n with
  | zero => simp [altW] at h
  | succ n ih =>
    simp only [altW, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact ih h

theorem altW_lt {p q n : Nat} (hp : p < 1953) (hq : q < 1953) : ∀ g ∈ altW p q n, g < 1953 :=
  fun _ hg => (altW_mem hg).elim (fun h => h ▸ hp) (fun h => h ▸ hq)

section Packed

variable {C : Nat} (hC : ∀ k < 1953, fldW 12 C k = codeOf (tvPair k))
include hC

theorem pairK_eq {k : Nat} (hk : k < 1953) : pairK C k = tvPair k := by
  have hp := tvP_tvPair hk
  have e1 : fldW 12 C k / 64 = (tvPair k).1 := by rw [hC k hk, codeOf_div hp]
  have e2 : fldW 12 C k % 64 = (tvPair k).2 := by rw [hC k hk, codeOf_mod hp]
  exact (congrArg₂ Prod.mk e1 e2).trans (Prod.eta _)

theorem wordId_altW {a b n : Nat} (ha : a < 1953) (hb : b < 1953)
    (h : wordId (altW (pairK C a) (pairK C b) n) = true) :
    wordId ((altW a b n).map tvPair) = true := by
  rw [altW_map, ← pairK_eq hC ha, ← pairK_eq hC hb]
  exact h

theorem chkOrd4_of (h : ord4K C = true) : prChkOrd4 = true := by
  unfold ord4K at h
  unfold prChkOrd4
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h ⊢
  intro a ha
  rw [stabCls_eq hC ha]
  rcases h a ha with h6 | hw
  · exact Or.inl h6
  · refine Or.inr ?_
    unfold prOrd4
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro x hx
    have e := foldr_tvImg_self (gs := altW 0 a 4) (altW_lt (by decide) ha)
      (wordId_altW hC (by decide) ha hw) hx
    rw [foldr_altW4] at e
    exact e

theorem chkStd_of (h : stdK C = true) : prChkStd = true := by
  unfold stdK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h31⟩, hr⟩, hw⟩ := h
  rw [pairK_eq hC (k := 0) (by decide)] at h0
  rw [pairK_eq hC (k := 31) (by decide)] at h31
  unfold prChkStd prOrd3
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨h0, h31⟩, by rw [stabRep_eq hC (by decide)]; exact hr⟩, fun x hx => ?_⟩
  have e := foldr_tvImg_self (gs := altW 0 31 3) (altW_lt (by decide) (by decide))
    (wordId_altW hC (by decide) (by decide) hw) hx
  rw [foldr_altW3] at e
  exact e

end Packed

end CFSG.SmithL6.K
