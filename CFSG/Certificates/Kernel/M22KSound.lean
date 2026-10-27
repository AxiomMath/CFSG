module

public import Certificates.Data.Kernel.M22K
public import CFSG.Certificates.Kernel.MatNKSound
public import CFSG.Certificates.Kernel.Mat12PSound

public section

namespace CFSG.KC.M22K

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H13.M22Cert CFSG.KC.Mat8P CFSG.KC.MatNK

def ORel (a : Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ))
    (b : NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) : Prop :=
  a.2 = b.2 ∧ ∀ y, a.1.contains y = memP b.1 y

def stepOH (gs : List (List ℕ)) (uw : ℕ × List ℕ)
    (st : Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) (i : ℕ) :
    Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ) :=
  let y := mvN (gs.getD i []) uw.1
  if st.1.contains y then st else (st.1.insert y, (y, i :: uw.2) :: st.2.1, (y, i :: uw.2) :: st.2.2)

def stepOT (gs : List (List ℕ)) (uw : ℕ × List ℕ)
    (st : NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) (i : ℕ) :
    NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ) :=
  let y := CFSG.KC.Mat12P.mvNR (gs.getD i []) uw.1
  if memP st.1 y then st else (insP st.1 y, (y, i :: uw.2) :: st.2.1, (y, i :: uw.2) :: st.2.2)

theorem stepORel (gs : List (List ℕ)) (uw : ℕ × List ℕ) (i : ℕ)
    (a : Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ))
    (b : NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)) (h : ORel a b) :
    ORel (stepOH gs uw a i) (stepOT gs uw b i) := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨h2, h1⟩ := h
  dsimp only at h2 h1
  subst h2
  unfold stepOH stepOT
  dsimp only
  rw [h1, CFSG.KC.Mat12P.mvNR_eq]
  by_cases hc : memP b1 (mvN (gs.getD i []) uw.1) = true
  · rw [if_pos hc, if_pos hc]
    exact ⟨rfl, h1⟩
  · rw [if_neg hc, if_neg hc]
    refine ⟨rfl, fun z => ?_⟩
    dsimp only
    rw [Std.HashSet.contains_insert, memP_insP, h1]

theorem orbBfs_toT (gs : List (List ℕ)) :
    ∀ (fuel : ℕ) (seen : Std.HashSet ℕ) (t : NT ℕ) (acc fr : List (ℕ × List ℕ)),
      (∀ y, seen.contains y = memP t y) → orbBfs gs fuel seen acc fr = orbBfsT gs fuel t acc fr
  | 0, _, _, _, _, _ => rfl
  | fuel + 1, seen, t, acc, [], _ => by simp [orbBfs, orbBfsT]
  | fuel + 1, seen, t, acc, uw :: fr, h => by
    simp only [orbBfs, orbBfsT]
    have hrel := foldl_relN ORel
      (fun st uw => (List.range gs.length).foldl (stepOH gs uw) st)
      (fun st uw => (List.range gs.length).foldl (stepOT gs uw) st)
      (fun a b uw hab => foldl_relN ORel _ _ (fun a b i hab => stepORel gs uw i a b hab) _ a b hab)
      (uw :: fr) (seen, acc, []) (t, acc, []) ⟨rfl, h⟩
    have key : ∀ (A : Std.HashSet ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ))
        (B : NT ℕ × List (ℕ × List ℕ) × List (ℕ × List ℕ)), ORel A B →
        orbBfs gs fuel A.1 A.2.1 A.2.2 = orbBfsT gs fuel B.1 B.2.1 B.2.2 := by
      rintro A B ⟨h2, h1⟩
      rw [h2]
      exact orbBfs_toT gs fuel _ _ _ _ h1
    exact key _ _ hrel

theorem orbL_toT : orbL = (orbBfsT gG 100 (insP (.tip []) v0) [(v0, [])] [(v0, [])]).reverse := by
  rw [orbL, orbBfs_toT]
  intro y
  rw [Std.HashSet.contains_insert, memP_insP, Std.HashSet.contains_empty, memP_empty]

end CFSG.KC.M22K

end
