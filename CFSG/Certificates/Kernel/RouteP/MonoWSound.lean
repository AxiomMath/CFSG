module

public import CFSG.Certificates.Kernel.RouteP.MonoSet
public import Certificates.Data.Kernel.RouteP.MonoW

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Benes CFSG.KC.Fi24Net
  CFSG.KC.RouteP CFSG.KS.Fi24Net

theorem eW_surj {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} :
    ∀ (w : List Int), (∀ z ∈ w, LOK NW KA KB z) → ∀ {N : Nat}, N < 920808 →
      ∃ M < 920808, eW NW KA KB w M = N
  | [], _, N, hN => ⟨N, hN, rfl⟩
  | z :: w, h, N, hN => by
    obtain ⟨M1, h1, e1⟩ := eL_surj (h z List.mem_cons_self) hN
    obtain ⟨M, hM, e⟩ := eW_surj w (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) h1
    exact ⟨M, hM, by rw [eW_cons, e, e1]⟩

theorem memS_imgW_iff {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {w : List Int}
    (hw : ∀ z ∈ w, LOK NW KA KB z) (s : Nat) {N : Nat} (hN : N < 920808)
    (h : memS (imgW NW KA KB w s) N = true) :
    ∃ M < 920808, memS s M = true ∧ eW NW KA KB w M = N := by
  obtain ⟨M, hM, rfl⟩ := eW_surj w hw hN
  exact ⟨M, hM, by rwa [memS_imgW w hw s hM] at h, rfl⟩

theorem roundW_cons (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (w : List Int) (ws : List (List Int))
    (s : Nat) : roundW NW KA KB (w :: ws) s = Nat.lor (roundW NW KA KB ws s) (imgW NW KA KB w s) := by
  change strictN (roundW NW KA KB ws s) (fun t => Nat.lor t (imgW NW KA KB w s)) = _
  exact strictN_eq' _ _

theorem memS_roundW (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (s N : Nat) :
    ∀ ws : List (List Int), memS (roundW NW KA KB ws s) N = true →
      memS s N = true ∨ ∃ w ∈ ws, memS (imgW NW KA KB w s) N = true
  | [], h => Or.inl h
  | w :: ws, h => by
    rw [roundW_cons, memS_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · rcases memS_roundW NW KA KB s N ws h with h | ⟨w', hw', h⟩
      · exact Or.inl h
      · exact Or.inr ⟨w', List.mem_cons_of_mem w hw', h⟩
    · exact Or.inr ⟨w, List.mem_cons_self, h⟩

theorem closeW_succ (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (ws : List (List Int)) (n s : Nat) :
    closeW NW KA KB ws (n + 1) s = closeW NW KA KB ws n (roundW NW KA KB ws s) :=
  strictN_eq' _ _

theorem closeW_min {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {ws : List (List Int)}
    (hg : ∀ w ∈ ws, ∀ z ∈ w, LOK NW KA KB z) (P : Nat → Prop)
    (hP : ∀ N < 920808, P N → ∀ w ∈ ws, P (eW NW KA KB w N)) :
    ∀ n s, (∀ N < 920808, memS s N = true → P N) →
      ∀ N < 920808, memS (closeW NW KA KB ws n s) N = true → P N
  | 0, _, h => h
  | n + 1, s, h => by
    rw [closeW_succ]
    refine closeW_min hg P hP n _ fun N hN hm => ?_
    rcases memS_roundW NW KA KB s N ws hm with hm | ⟨w, hw, hm⟩
    · exact h N hN hm
    · obtain ⟨M, hM, hMs, rfl⟩ := memS_imgW_iff (hg w hw) s hN hm
      exact hP M hM (h M hM hMs) w hw

end CFSG.KS.RouteP

end
