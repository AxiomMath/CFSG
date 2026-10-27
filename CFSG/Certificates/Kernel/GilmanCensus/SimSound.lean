module

import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.MemoSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census Std

@[expose] def Sim {α : Type} (dt : Data) (p : CM α) (v : α) (b : Bool) : Prop :=
  ∀ c, CacheOK dt c → (p.run c).1 = v ∧ CacheOK dt (p.run c).2 ∧ (p.run c).2.bad = (c.bad || b)

theorem sim_pure {α : Type} (dt : Data) (v : α) : Sim dt (pure v) v false :=
  fun c hc => ⟨rfl, hc, by rw [Bool.or_false]; rfl⟩

theorem sim_congr {α : Type} {dt : Data} {p : CM α} {v v' : α} {b b' : Bool} (h : Sim dt p v b)
    (hv : v = v') (hb : b = b') : Sim dt p v' b' := by
  subst hv hb
  exact h

theorem sim_bind {α β : Type} {dt : Data} {p : CM α} {f : α → CM β} {v : α} {w : β} {b b' : Bool}
    (hp : Sim dt p v b) (hf : Sim dt (f v) w b') : Sim dt (p >>= f) w (b || b') := by
  intro c hc
  obtain ⟨h1, h2, h3⟩ := hp c hc
  have e : (p >>= f).run c = (f (p.run c).1).run (p.run c).2 := rfl
  rw [e]
  generalize p.run c = r at h1 h2 h3
  obtain ⟨a, s⟩ := r
  dsimp only at h1 h2 h3 ⊢
  subst h1
  obtain ⟨g1, g2, g3⟩ := hf s h2
  exact ⟨g1, g2, by rw [g3, h3, Bool.or_assoc]⟩

theorem sim_markBad (dt : Data) : Sim dt markBad () true :=
  fun c hc => ⟨rfl, ⟨hc.1, hc.2⟩, by rw [Bool.or_true]; rfl⟩

@[expose] def orFold {α β : Type} (g : β → α → β) (bf : β → α → Bool) : List α → β → Bool
  | [], _ => false
  | a :: l, s => bf s a || orFold g bf l (g s a)

theorem sim_forIn {α β : Type} (dt : Data) (g : β → α → β) (bf : β → α → Bool)
    (f : α → β → CM (ForInStep β)) (hf : ∀ a s, Sim dt (f a s) (ForInStep.yield (g s a)) (bf s a)) :
    ∀ (l : List α) (init : β), Sim dt (forIn l init f) (l.foldl g init) (orFold g bf l init)
  | [], init => sim_pure dt init
  | a :: l, init => by
    rw [List.forIn_cons]
    exact sim_bind (hf a init) (sim_forIn dt g bf f hf l (g init a))

theorem orFold_false {α β : Type} (g : β → α → β) : ∀ (l : List α) (s : β),
    orFold g (fun _ _ => false) l s = false
  | [], _ => rfl
  | _ :: l, s => by rw [orFold, orFold_false g l, Bool.or_false]

theorem foldl_push_filter {α : Type} (P : α → Bool) : ∀ (l : List α) (acc : Array α),
    l.foldl (fun r a => if P a = true then r.push a else r) acc = acc ++ (l.filter P).toArray
  | [], acc => by simp
  | a :: l, acc => by
    rw [List.foldl_cons, foldl_push_filter P l, List.filter_cons]
    by_cases h : P a = true
    · simp [h]
    · simp [h]

theorem sim_kernelM (dt : Data) (m : Nat) : Sim dt (kernelM dt m) (kerPure dt m) false :=
  fun _ hc => let h := kernelM_ok hc m; ⟨h.1, h.2.1, by rw [h.2.2, Bool.or_false]⟩

end Certificates.GilmanCensusK

end
