module

public import Certificates.Data.Kernel.B3SixD
public import CFSG.Certificates.Kernel.B3SixKSound

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3

theorem eqD_sound {d e : FourD} (h : eqD d e = true) : d = e := by
  obtain ⟨T, H1, H2, R1, R2, L1, L2T, L1d, A1p, w⟩ := d
  obtain ⟨T', H1', H2', R1', R2', L1', L2T', L1d', A1p', w'⟩ := e
  simp only [eqD, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  rfl

def okC (s : Tab) : Prop := s.length = 6 ∧ ∀ e ∈ s, e < 8

theorem codeT_cons (x : ℕ) (xs : Tab) : codeT (x :: xs) = x + 8 * codeT xs := rfl

theorem codeT_inj : ∀ (a b : Tab), a.length = b.length → (∀ e ∈ a, e < 8) → (∀ e ∈ b, e < 8) →
    codeT a = codeT b → a = b
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | x :: xs, y :: ys, hl, ha, hb, hc => by
    rw [codeT_cons, codeT_cons] at hc
    have hx := ha x (by simp)
    have hy := hb y (by simp)
    have h1 : x = y := by omega
    have h2 : codeT xs = codeT ys := by omega
    subst h1
    rw [codeT_inj xs ys (by simpa using hl) (fun e he => ha e (by simp [he]))
      (fun e he => hb e (by simp [he])) h2]

theorem memN_iff (c : ℕ) : ∀ C : List ℕ, memN c C = true ↔ c ∈ C
  | [] => by simp [memN]
  | x :: xs => by
    have e : memN c (x :: xs) = (Nat.beq c x || memN c xs) := rfl
    rw [e, Bool.or_eq_true, memN_iff c xs, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl (Nat.eq_of_beq_eq_true h)
      · exact Or.inr h
    · rintro (h | h)
      · subst h
        exact Or.inl (Nat.beq_refl c)
      · exact Or.inr h

theorem memN_codeT {S : List Tab} (hS : ∀ s ∈ S, okC s) {y : Tab} (hy : okC y) :
    memN (codeT y) (S.map codeT) = S.contains y := by
  rw [Bool.eq_iff_iff, memN_iff, List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨s, hs, he⟩
    rw [codeT_inj s y (by rw [(hS s hs).1, hy.1]) (hS s hs).2 hy.2 he] at hs
    exact hs
  · intro h
    exact ⟨y, h, rfl⟩

theorem okC_of_isTab {s : Tab} (h : isTab 6 s = true) : okC s := by
  simp only [isTab, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, fun e he => by have := h.1.2 e he; omega⟩

theorem okC_mulT {a b : Tab} (ha : okC a) (hb : okC b) : okC (mulT a b) := by
  refine ⟨by simp [mulT, hb.1], ?_⟩
  simp only [mulT, List.mem_map]
  rintro e ⟨j, -, rfl⟩
  rw [List.getD_eq_getElem?_getD]
  cases h : a[j]? with
  | none => simp
  | some v => exact ha.2 v (List.mem_of_getElem? h)

theorem okC_invT {a : Tab} (ha : okC a) : okC (invT a) := by
  refine ⟨by simp [invT, ha.1], ?_⟩
  simp only [invT, List.mem_map]
  rintro e ⟨j, -, rfl⟩
  have := List.idxOf_le_length (a := j) (l := a)
  rw [ha.1] at this
  omega

theorem okC_idT : okC (idT 6) := by
  refine ⟨by simp [idT], fun e he => ?_⟩
  simp only [idT, List.mem_range] at he
  omega

theorem subOKN_eq (S : List Tab) : subOKN S = subOK 6 S := by
  simp only [subOKN, subOK]
  by_cases h : S.all (isTab 6) = true
  · have hS : ∀ s ∈ S, okC s := fun s hs => okC_of_isTab (List.all_eq_true.1 h s hs)
    have e2 : (S.all fun a => S.all fun b => memN (codeT (mulT a b)) (S.map codeT)) =
        S.all fun a => S.all fun b => S.contains (mulT a b) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor
      · intro H a ha b hb
        rw [← memN_codeT hS (okC_mulT (hS a ha) (hS b hb))]
        exact H a ha b hb
      · intro H a ha b hb
        rw [memN_codeT hS (okC_mulT (hS a ha) (hS b hb))]
        exact H a ha b hb
    have e3 : (S.all fun a => memN (codeT (invT a)) (S.map codeT)) =
        S.all fun a => S.contains (invT a) := by
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor
      · intro H a ha
        rw [← memN_codeT hS (okC_invT (hS a ha))]
        exact H a ha
      · intro H a ha
        rw [memN_codeT hS (okC_invT (hS a ha))]
        exact H a ha
    rw [memN_codeT hS okC_idT, e2, e3]
  · simp [h]

theorem chkGenTabsS_closeTK (gens : List Tab) :
    chkGenTabsS gens (closeTK 6 gens) = chkGenTabsK 6 gens := by
  simp only [chkGenTabsS, chkGenTabsK, chkGenTabs, closeTK, subOKN_eq]

theorem claimsGN_eq (k : Mod) (d : FourD) (S : List (List Tab)) :
    claimsGN k d S = claimsGK k d S := by
  simp only [claimsGN, claimsGK, jOKN, jOKK, chkGenTabsN, chkGenTabsS_closeTK]

theorem claimsLN_eq (d : FourD) (S : List (List Tab)) : claimsLN d S = claimsLK d S := by
  simp only [claimsLN, claimsLK, jOKN, jOKK, chkGenTabsN, chkGenTabsS_closeTK]

theorem chkStruct6X_D (P : List Tab) (k : Mod) (b : Bool) (e : ℕ) :
    chkStruct6X P k b e = chkStruct6D P (fourDX P k b) k b e := by
  simp only [chkStruct6X, chkStruct6D, subOKN_eq]

theorem chkGenG6X_D (P : List Tab) (k : Mod) : chkGenG6X P k = chkGenG6D (fourDX P k true) := by
  have h1 : (fourDX P k true).L2T =
      closeTK 6 ((fourDX P k true).H2.filter isEvenT ++ (fourDX P k true).T) := rfl
  have h2 : (fourDX P k true).L1d =
      closeTK 6 (commGens (fourDX P k true).L1 (fourDX P k true).L1) := rfl
  simp only [chkGenG6X, chkGenG6D, h1, h2, chkGenTabsS_closeTK, subOKN_eq]

theorem chkSubG6X_D (P : List Tab) (W : List (ℕ × ℕ × Tab)) (k : Mod) :
    chkSubG6X P W k = chkSubG6D P W (fourDX P k true) k := by
  simp only [chkSubG6X, chkSubG6D, claimsGN_eq]

theorem chkWitG6X_D (P : List Tab) (k : Mod) : chkWitG6X P k = chkWitG6D P (fourDX P k true) k :=
  rfl

theorem chkRG6X_D (P : List Tab) (k : Mod) : chkRG6X P k = chkRG6D (fourDX P k true) := rfl

theorem chkSubL6X_D (P : List Tab) (k : Mod) :
    chkSubL6X P k = chkSubL6D P (fourDX P k false) k := by
  simp only [chkSubL6X, chkSubL6D, claimsLN_eq]

theorem chkRL6X_D (P : List Tab) (k : Mod) : chkRL6X P k = chkRL6D (fourDX P k false) k := rfl

theorem chkG6_of_D (k : Mod) (d : FourD) (he : eqD (fourDX sym6K k true) d = true)
    (h1 : chkStruct6D sym6K d k true 4 = true) (h2 : chkGenG6D d = true)
    (h3 : chkSubG6D sym6K wG6 d k = true) (h4 : chkWitG6D sym6K d k = true)
    (h5 : chkRG6D d = true) : chkG6 k = true := by
  have hd := eqD_sound he
  subst hd
  exact chkG6_of_parts k ((chkStruct6X_D _ _ _ _).trans h1) ((chkGenG6X_D _ _).trans h2)
    ((chkSubG6X_D _ _ _).trans h3) ((chkWitG6X_D _ _).trans h4) ((chkRG6X_D _ _).trans h5)

theorem chkL6_of_D (k : Mod) (d : FourD) (he : eqD (fourDX sym6K k false) d = true)
    (h1 : chkStruct6D sym6K d k false 3 = true) (h2 : chkSubL6D sym6K d k = true)
    (h3 : chkRL6D d k = true) : chkL6 k = true := by
  have hd := eqD_sound he
  subst hd
  exact chkL6_of_parts k ((chkStruct6X_D _ _ _ _).trans h1) ((chkSubL6X_D _ _).trans h2)
    ((chkRL6X_D _ _).trans h3)

end CFSG.KC.B3Six
