module

public import Certificates.Data.Kernel.MatNK
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace CFSG.KC.MatNK

open CFSG.Quasithin.H13.MatNCert CFSG.KC.Mat8P

def NRel (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) : Prop :=
  a.2 = b.2 ∧ ∀ y, a.1.contains y = memLR b.1 y

def stepNH (n : ℕ) (gens : List (List ℕ)) (wx : List ℕ × List ℕ)
    (st : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) (i : ℕ) :
    Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ) :=
  let y := mulN (gens.getD i (oneN n)) wx.2
  if st.1.contains y then st else (st.1.insert y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)

def stepNT (n : ℕ) (gens : List (List ℕ)) (wx : List ℕ × List ℕ)
    (st : NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) (i : ℕ) :
    NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ) :=
  let y := mulN (gens.getD i (oneN n)) wx.2
  if memLR st.1 y then st else (insLR st.1 y, (i :: wx.1) :: st.2.1, (i :: wx.1, y) :: st.2.2)

theorem stepNRel (n : ℕ) (gens : List (List ℕ)) (wx : List ℕ × List ℕ) (i : ℕ)
    (a : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
    (b : NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)) (h : NRel a b) :
    NRel (stepNH n gens wx a i) (stepNT n gens wx b i) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h2, h1⟩ := h
  dsimp only at h2 h1
  subst h2
  unfold stepNH stepNT
  dsimp only
  rw [h1]
  by_cases hc : memLR b1 (mulN (gens.getD i (oneN n)) wx.2) = true
  · rw [if_pos hc, if_pos hc]
    exact ⟨rfl, h1⟩
  · rw [if_neg hc, if_neg hc]
    refine ⟨rfl, fun z => ?_⟩
    dsimp only
    rw [Std.HashSet.contains_insert, memLR_insLR, h1]

theorem foldl_relN {α β γ : Type} (R : α → β → Prop) (f : α → γ → α) (g : β → γ → β)
    (hfg : ∀ a b c, R a b → R (f a c) (g b c)) :
    ∀ (l : List γ) (a : α) (b : β), R a b → R (l.foldl f a) (l.foldl g b)
  | [], _, _, h => h
  | c :: l, a, b, h => foldl_relN R f g hfg l _ _ (hfg a b c h)

theorem bfsWN_eq (n : ℕ) (gens : List (List ℕ)) (cap : ℕ) :
    ∀ (fuel : ℕ) (seen : Std.HashSet (List ℕ)) (t : NT (List ℕ)) (acc : List (List ℕ))
      (fr : List (List ℕ × List ℕ)), (∀ y, seen.contains y = memLR t y) →
      bfsW n gens cap fuel seen acc fr = bfsWNT n gens cap fuel t acc fr
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, seen, t, acc, [], _ => by simp [bfsW, bfsWNT]
  | fuel + 1, seen, t, acc, wx :: fr, h => by
    simp only [bfsW, bfsWNT]
    split_ifs with hc
    · rfl
    · have hrel := foldl_relN NRel
        (fun st wx => (List.range gens.length).foldl (stepNH n gens wx) st)
        (fun st wx => (List.range gens.length).foldl (stepNT n gens wx) st)
        (fun a b wx hab => foldl_relN NRel _ _ (fun a b i hab => stepNRel n gens wx i a b hab) _ a b hab)
        (wx :: fr) (seen, acc, []) (t, acc, []) ⟨rfl, h⟩
      have key : ∀ (A : Std.HashSet (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ))
          (B : NT (List ℕ) × List (List ℕ) × List (List ℕ × List ℕ)), NRel A B →
          bfsW n gens cap fuel A.1 A.2.1 A.2.2 = bfsWNT n gens cap fuel B.1 B.2.1 B.2.2 := by
        rintro A B ⟨h2, h1⟩
        rw [h2]
        exact bfsWN_eq n gens cap fuel _ _ _ _ h1
      exact key _ _ hrel

theorem elemsOfN_toT (n : ℕ) (gens : List (List ℕ)) (cap : ℕ) :
    elemsOf n gens cap = elemsOfNT n gens cap := by
  rw [elemsOf, wordsOf, elemsOfNT, bfsWN_eq]
  intro y
  rw [Std.HashSet.contains_insert, memLR_insLR, Std.HashSet.contains_empty, memLR_empty]

end CFSG.KC.MatNK

end
