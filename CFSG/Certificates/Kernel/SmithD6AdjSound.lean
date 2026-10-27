module

public import Certificates.Data.Kernel.SmithD6.AdjK
public import CFSG.Certificates.Kernel.KeyTreeChunksSound

public section

namespace CFSG.KD.SmithD6Adj

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem moveGo_sound (x : Nat) : ∀ gs : List (List (Nat × Nat × Bool)), moveGo x gs = true →
    ∃ ts ∈ gs, rhoT ts x ≠ 0 ∧ KT.memB (rhoT ts x) wt64Tree = true
  | [], h => absurd h (by simp [moveGo])
  | ts :: gs, h => by
    have e : moveGo x (ts :: gs) = strictB (rhoT ts x)
        (fun r => bIf(Nat.beq r 0, moveGo x gs, KT.memB r wt64Tree)) := rfl
    rw [e, strictB_eq] at h
    by_cases h0 : rhoT ts x = 0
    · rw [h0] at h
      obtain ⟨ts', hm, h1⟩ := moveGo_sound x gs h
      exact ⟨ts', List.mem_cons_of_mem _ hm, h1⟩
    · have hb : Nat.beq (rhoT ts x) 0 = false :=
        Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
      rw [hb] at h
      exact ⟨ts, List.mem_cons_self, h0, h⟩

theorem adjOK_sound {x : Nat} (h : adjOK x = true) :
    (rhoT (JT.gensT.getD 0 []) x = 0 ∨ KT.memB (rhoT (JT.gensT.getD 0 []) x) wt64Tree = true) ∧
    (rhoT (JT.gensT.getD 0 []) x = 0 →
      ∃ ts ∈ JT.gensT, rhoT ts x ≠ 0 ∧ KT.memB (rhoT ts x) wt64Tree = true) := by
  unfold adjOK at h
  rw [strictB_eq] at h
  by_cases h0 : rhoT (JT.gensT.getD 0 []) x = 0
  · rw [h0] at h
    exact ⟨Or.inl h0, fun _ => moveGo_sound x _ h⟩
  · have hb : Nat.beq (rhoT (JT.gensT.getD 0 []) x) 0 = false :=
      Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
    rw [hb] at h
    exact ⟨Or.inr h, fun h' => absurd h' h0⟩

theorem adjGo_sound : ∀ l : List Nat, adjGo l = true → ∀ x ∈ l, adjOK x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: l, h, x, hx => by
    have e : adjGo (y :: l) = bAnd(adjOK y, adjGo l) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact adjGo_sound l h2 x hx

end CFSG.KD.SmithD6Adj

end
