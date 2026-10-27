module

public import CFSG.Certificates.Kernel.M24G.BfsFacts
import all CFSG.Certificates.Kernel.M24G.BfsFacts

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem loopG_sim {β γ : Type} {c : β → Prop} [DecidablePred c] {c' : γ → Prop} [DecidablePred c']
    {F : β → β} {F' : γ → γ} (R : β → γ → Prop) (hc : ∀ b b', R b b' → (c b ↔ c' b'))
    (hF : ∀ b b', R b b' → c b → R (F b) (F' b')) :
    ∀ n b b', R b b' → R (loopG c F n b) (loopG c' F' n b')
  | 0, _, _, h => h
  | n + 1, b, b', h => by
    simp only [loopG]
    by_cases hb : c b
    · rw [if_pos hb, if_pos ((hc b b' h).1 hb)]
      exact loopG_sim R hc hF n _ _ (hF b b' h hb)
    · rw [if_neg hb, if_neg (fun hb' => hb ((hc b b' h).2 hb'))]
      exact h

variable {α β : Type} [Inhabited α] [Inhabited β]

@[expose] def StepsRel (f : α → β) (X : α → Prop) : List (α → α) → List (β → β) → Prop
  | [], [] => True
  | s :: ss, s' :: ss' => (∀ y, X y → X (s y) ∧ f (s y) = s' (f y)) ∧ StepsRel f X ss ss'
  | _, _ => False

def MapRel (f : α → β) (X : α → Prop) (st : BSt α) (st' : BSt β) : Prop :=
  st'.1 = st.1.map f ∧ st'.2 = st.2 ∧ ∀ x ∈ st.1, X x

theorem map_get! {f : α → β} {a : Array α} {i : Nat} (hi : i < a.size) :
    (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos a i hi]

theorem fold_map_sim {key : α → Nat} {key' : β → Nat} {f : α → β} {X : α → Prop}
    (hk : ∀ x, X x → key' (f x) = key x) {x : α} (hx : X x) (h : Nat) :
    ∀ (ss : List (α → α)) (ss' : List (β → β)), StepsRel f X ss ss' →
      ∀ (st : BSt α) (st' : BSt β), MapRel f X st st' →
        MapRel f X (ss.foldl (bfsAdd key x h) st) (ss'.foldl (bfsAdd key' (f x) h) st')
  | [], [], _, _, _, hR => hR
  | s :: ss, s' :: ss', hs, st, st', hR => by
    rw [List.foldl_cons, List.foldl_cons]
    refine fold_map_sim hk hx h ss ss' hs.2 _ _ ?_
    obtain ⟨hXs, hfs⟩ := hs.1 x hx
    obtain ⟨e1, e2, hX⟩ := hR
    obtain ⟨L, R⟩ := st
    obtain ⟨L', R'⟩ := st'
    dsimp only at e1 e2 hX
    subst e1 e2
    have hkey : key' (s' (f x)) = key (s x) := by rw [← hfs, hk _ hXs]
    unfold bfsAdd
    dsimp only
    rw [hkey]
    split
    · refine ⟨by rw [Array.map_push, hfs], by rw [Array.size_map], fun y hy => ?_⟩
      rcases Array.mem_push.1 hy with hy | rfl
      · exact hX y hy
      · exact hXs
    · exact ⟨rfl, rfl, hX⟩
  | [], _ :: _, hs, _, _, _ => hs.elim
  | _ :: _, [], hs, _, _, _ => hs.elim

theorem head_map_sim {key : α → Nat} {key' : β → Nat} {steps : List (α → α)}
    {steps' : List (β → β)} {f : α → β} {X : α → Prop} (hk : ∀ x, X x → key' (f x) = key x)
    (hs : StepsRel f X steps steps') (st : BSt α) (st' : BSt β) (hR : MapRel f X st st')
    (hg : bfsGo st) : MapRel f X (bfsHead key steps st) (bfsHead key' steps' st') := by
  obtain ⟨e1, e2, hX⟩ := hR
  obtain ⟨L, R⟩ := st
  obtain ⟨L', R'⟩ := st'
  dsimp only at e1 e2 hX
  subst e1 e2
  unfold bfsGo at hg
  dsimp only at hg
  have hx : X L[R'.2.2.2]! := by
    rw [getElem!_pos L _ hg]
    exact hX _ (Array.getElem_mem hg)
  have hR' := fold_map_sim (key := key) (key' := key') hk hx R'.2.2.2 steps steps' hs
    (L, R'.1, R'.2.1, R'.2.2.1, 0) (L.map f, R'.1, R'.2.1, R'.2.2.1, 0) ⟨rfl, rfl, hX⟩
  unfold bfsHead
  dsimp only
  rw [map_get! hg]
  obtain ⟨r1, r2, r3⟩ := hR'
  refine ⟨r1, ?_, r3⟩
  rw [r2]

theorem bfsM24_map {key : α → Nat} {key' : β → Nat} {steps : List (α → α)}
    {steps' : List (β → β)} {base : α} {base' : β} (f : α → β) (X : α → Prop)
    (hb : f base = base') (hX : X base) (hk : ∀ x, X x → key' (f x) = key x)
    (hs : StepsRel f X steps steps') (fuel : Nat) :
    Native.bfs key' steps' base' fuel =
        ((Native.bfs key steps base fuel).1.map f, (Native.bfs key steps base fuel).2.1,
          (Native.bfs key steps base fuel).2.2) ∧
      ∀ x ∈ (Native.bfs key steps base fuel).1, X x := by
  subst hb
  have hR := loopG_sim (c := bfsGo) (c' := bfsGo) (F := bfsHead key steps)
    (F' := bfsHead key' steps') (MapRel f X)
    (fun b b' h => by
      unfold bfsGo
      rw [h.1, Array.size_map, h.2.1])
    (fun b b' h hg => head_map_sim hk hs b b' h hg) fuel (bfsInit key base)
    (bfsInit key' (f base))
    ⟨by simp [bfsInit], by simp [bfsInit, hk base hX], fun x hx => by
      simp only [bfsInit, Array.mem_singleton] at hx
      exact hx ▸ hX⟩
  rw [bfs_eq_loop, bfs_eq_loop]
  obtain ⟨r1, r2, r3⟩ := hR
  refine ⟨?_, r3⟩
  rw [r1, r2]

end CFSG.KC.M24G
