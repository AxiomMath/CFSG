module

public import Certificates.Data.Kernel.AS91K468.K46
public import CFSG.Certificates.Kernel.Mat8PSound

public section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K
open CFSG.GF2Type.Smith1979.GammaU

section

variable {σ κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ] [LawfulHashable κ]
  (enc : ℕ → σ) (key : σ → κ) (D : ℕ → Prop)

@[expose] def SRel (h : Std.HashSet κ) (t : NT ℕ) : Prop :=
  ∀ q, D q → h.contains (key (enc q)) = memP t q

@[expose] def stepH (acc : List σ × Std.HashSet κ) (t : σ) : List σ × Std.HashSet κ :=
  if acc.2.contains (key t) then acc else (t :: acc.1, acc.2.insert (key t))

theorem foldl_stepN (hk : ∀ a b, D a → D b → (key (enc a) == key (enc b)) = (a == b)) :
    ∀ (L : List ℕ), (∀ x ∈ L, D x) → ∀ (l : List ℕ) (h : Std.HashSet κ) (t : NT ℕ),
      (∀ q ∈ l, D q) → SRel enc key D h t →
      ((L.map enc).foldl (stepH key) (l.map enc, h)).1 = (L.foldl stepN (l, t)).1.map enc ∧
      SRel enc key D ((L.map enc).foldl (stepH key) (l.map enc, h)).2 (L.foldl stepN (l, t)).2 ∧
      ∀ q ∈ (L.foldl stepN (l, t)).1, D q
  | [], _, l, h, t, hl, hr => ⟨rfl, hr, hl⟩
  | x :: L, hL, l, h, t, hl, hr => by
    have hx : D x := hL x List.mem_cons_self
    have hL' : ∀ y ∈ L, D y := fun y hy => hL y (List.mem_cons_of_mem x hy)
    rw [List.map_cons, List.foldl_cons, List.foldl_cons]
    have hc : h.contains (key (enc x)) = memP t x := hr x hx
    by_cases hm : memP t x = true
    · have e1 : stepH key (l.map enc, h) (enc x) = (l.map enc, h) := by
        simp only [stepH, hc, hm, if_true]
      have e2 : stepN (l, t) x = (l, t) := by simp only [stepN, hm, if_true]
      rw [e1, e2]
      exact foldl_stepN hk L hL' l h t hl hr
    · have hm' : memP t x = false := by simpa using hm
      have e1 : stepH key (l.map enc, h) (enc x) =
          ((x :: l).map enc, h.insert (key (enc x))) := by
        simp only [stepH, hc, hm', Bool.false_eq_true, if_false, List.map_cons]
      have e2 : stepN (l, t) x = (x :: l, insP t x) := by
        simp only [stepN, hm', Bool.false_eq_true, if_false]
      rw [e1, e2]
      refine foldl_stepN hk L hL' (x :: l) _ _ ?_ ?_
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hx
        · exact hl q hq
      · intro q hq
        rw [Std.HashSet.contains_insert, memP_insP, hk x q hx hq, hr q hq]

theorem flat_encN (fs : List (σ → σ)) (fsQ : List (ℕ → ℕ))
    (hf : ∀ q, D q → fs.map (fun f => f (enc q)) = (fsQ.map fun f => f q).map enc) :
    ∀ fr : List ℕ, (∀ q ∈ fr, D q) →
      (fr.map enc).flatMap (fun s => fs.map fun f => f s) =
        (fr.flatMap fun s => fsQ.map fun f => f s).map enc
  | [], _ => rfl
  | s :: fr, hfr => by
    rw [List.map_cons, List.flatMap_cons, List.flatMap_cons, List.map_append,
      hf s (hfr s List.mem_cons_self), flat_encN fs fsQ hf fr fun q hq => hfr q (List.mem_cons_of_mem s hq)]

theorem flat_D (fsQ : List (ℕ → ℕ)) (hd : ∀ q, D q → ∀ f ∈ fsQ, D (f q)) (fr : List ℕ)
    (hfr : ∀ q ∈ fr, D q) : ∀ t ∈ fr.flatMap (fun s => fsQ.map fun f => f s), D t := by
  intro t ht
  obtain ⟨s, hs, hs'⟩ := List.mem_flatMap.1 ht
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hs'
  exact hd s (hfr s hs) f hf

theorem bfsClosure_N (hk : ∀ a b, D a → D b → (key (enc a) == key (enc b)) = (a == b))
    (fs : List (σ → σ)) (fsQ : List (ℕ → ℕ))
    (hf : ∀ q, D q → fs.map (fun f => f (enc q)) = (fsQ.map fun f => f q).map enc)
    (hd : ∀ q, D q → ∀ f ∈ fsQ, D (f q)) :
    ∀ (fuel : ℕ) (fr vis : List ℕ) (h : Std.HashSet κ) (t : NT ℕ), (∀ q ∈ fr, D q) →
      (∀ q ∈ vis, D q) → SRel enc key D h t →
      bfsClosure key fs fuel (fr.map enc) h (vis.map enc) = (closN fsQ fuel fr t vis).map enc ∧
        ∀ q ∈ closN fsQ fuel fr t vis, D q
  | 0, fr, vis, h, t, hfr, hvis, _ => by
    refine ⟨by rw [bfsClosure, closN, List.map_append], fun q hq => ?_⟩
    rw [closN] at hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hfr q hq
    · exact hvis q hq
  | fuel + 1, fr, vis, h, t, hfr, hvis, hr => by
    have e1 : bfsRound key fs (fr.map enc) h =
        ((fr.flatMap fun s => fsQ.map fun f => f s).map enc).foldl (stepH key)
          (([] : List ℕ).map enc, h) := by
      rw [bfsRound, flat_encN enc D fs fsQ hf fr hfr]
      rfl
    have e2 : roundN fsQ fr t = (fr.flatMap fun s => fsQ.map fun f => f s).foldl stepN ([], t) :=
      rfl
    obtain ⟨r1, r2, r3⟩ := foldl_stepN enc key D hk _ (flat_D D fsQ hd fr hfr) [] h t
      (by simp) hr
    have hfv : ∀ q ∈ fr ++ vis, D q := fun q hq => by
      rcases List.mem_append.1 hq with hq | hq
      · exact hfr q hq
      · exact hvis q hq
    simp only [bfsClosure, closN]
    rw [e1, e2, r1, List.isEmpty_map]
    split_ifs with he
    · exact ⟨by rw [List.map_append], hfv⟩
    · rw [← List.map_append]
      exact bfsClosure_N hk fs fsQ hf hd fuel _ _ _ _ r3 hfv r2

end

end Certificates.Kernel.AS91K468
