module

public import Certificates.Data.Kernel.Misc.ClosK
public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs

public section

namespace CFSG.KC.ClosK

open CFSG.Quasithin.RuRank3 CFSG.Monster.B.Co2.Native

@[expose] def clInner (n : ℕ) (gens : Array (Array ℕ)) (g : Array ℕ) (k : ℕ)
    (L : Array (Array ℕ)) : Id (ForInStep (Array (Array ℕ))) :=
  if (!L.any fun e => eqA n e (compA n gens[k]! g)) = true then
    ForInStep.yield (L.push (compA n gens[k]! g))
  else ForInStep.yield L

@[expose] def clOuter (n : ℕ) (gens : Array (Array ℕ)) (_ : ℕ) (s : Array (Array ℕ) × ℕ) :
    Id (ForInStep (Array (Array ℕ) × ℕ)) :=
  if s.2 < s.1.size then
    ForInStep.yield (forIn (m := Id) [:gens.size] s.1 (clInner n gens s.1[s.2]!), s.2 + 1)
  else ForInStep.yield (s.1, s.2)

theorem closureList_eq_cl (n : ℕ) (gens : Array (Array ℕ)) (cap : ℕ) :
    closureList n gens cap = (forIn (m := Id) [:cap] (#[idA n], 0) (clOuter n gens)).1 := rfl

@[expose] def insA (n : ℕ) (gens : Array (Array ℕ)) (g : Array ℕ) (L : Array (Array ℕ)) (k : ℕ) :
    Array (Array ℕ) :=
  if (!L.any fun e => eqA n e (compA n gens[k]! g)) = true then L.push (compA n gens[k]! g) else L

@[expose] def stepA (n : ℕ) (gens : Array (Array ℕ)) (s : Array (Array ℕ) × ℕ) :
    Array (Array ℕ) × ℕ :=
  if s.2 < s.1.size then ((List.range' 0 gens.size).foldl (insA n gens s.1[s.2]!) s.1, s.2 + 1)
  else (s.1, s.2)

theorem forIn_range_eq_foldl {β : Type} (m : ℕ) (b : β) (f : ℕ → β → Id (ForInStep β))
    (g : β → ℕ → β) (hf : ∀ k b, f k b = ForInStep.yield (g b k)) :
    forIn (m := Id) [:m] b f = (List.range' 0 m).foldl g b := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have hs : Std.Legacy.Range.size [:m] = m := by simp [Std.Legacy.Range.size]
  simp only [hs]
  have e : f = fun k b => pure (ForInStep.yield (g b k)) := by
    funext k b
    exact hf k b
  rw [e, List.forIn_pure_yield_eq_foldl]
  rfl

theorem closureList_eq_stepA (n : ℕ) (gens : Array (Array ℕ)) (cap : ℕ) :
    closureList n gens cap =
      ((List.range' 0 cap).foldl (fun s _ => stepA n gens s) (#[idA n], 0)).1 := by
  rw [closureList_eq_cl, forIn_range_eq_foldl cap _ _ (fun s _ => stepA n gens s)]
  intro k s
  unfold clOuter stepA
  split
  · rw [forIn_range_eq_foldl gens.size _ _ (insA n gens s.1[s.2]!)]
    intro k' L
    unfold clInner insA
    split <;> rfl
  · rfl

theorem closK_eq_foldl (pc : ℕ → ℕ → ℕ) (gs : ℕ → ℕ) (ng : ℕ) (s : List ℕ × ℕ) :
    ∀ c, closK pc gs ng c s = (List.range' 0 c).foldl (fun s _ => stepK pc gs ng s) s
  | 0 => rfl
  | c + 1 => by
    rw [closK, closK_eq_foldl pc gs ng s c, List.range'_concat, List.foldl_append]
    rfl

section

variable {n e : ℕ} {u : ℕ → Array ℕ} {pc : ℕ → ℕ → ℕ} {C : ℕ → Prop}
  {gens : Array (Array ℕ)} {gs : ℕ → ℕ}

theorem insA_eq
    (hcomp : ∀ p q, C p → C q → compA n (u p) (u q) = u (pc p q))
    (heq : ∀ p q, C p → C q → eqA n (u p) (u q) = Nat.beq p q)
    (hC : ∀ p q, C p → C q → C (pc p q))
    (hg : ∀ k < gens.size, gens[k]! = u (gs k) ∧ C (gs k))
    {gp : ℕ} (hgp : C gp) : ∀ (l : List ℕ), (∀ k ∈ l, k < gens.size) →
    ∀ (Lp : List ℕ), (∀ x ∈ Lp, C x) →
      l.foldl (insA n gens (u gp)) (Lp.map u).toArray =
        ((l.foldl (insK pc gs gp) Lp).map u).toArray ∧ ∀ x ∈ l.foldl (insK pc gs gp) Lp, C x
  | [], _, Lp, hLp => ⟨rfl, hLp⟩
  | k :: l, hl, Lp, hLp => by
    have hk : k < gens.size := hl k (by simp)
    obtain ⟨hgk, hCk⟩ := hg k hk
    have hh : C (pc (gs k) gp) := hC _ _ hCk hgp
    have hany : ((Lp.map u).toArray.any fun x => eqA n x (compA n gens[k]! (u gp))) =
        Lp.any fun x => Nat.beq x (pc (gs k) gp) := by
      rw [hgk, hcomp _ _ hCk hgp, List.any_toArray, List.any_map]
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true, Function.comp_apply]
      constructor
      · rintro ⟨x, hx, h⟩
        exact ⟨x, hx, by rwa [heq _ _ (hLp x hx) hh] at h⟩
      · rintro ⟨x, hx, h⟩
        exact ⟨x, hx, by rwa [heq _ _ (hLp x hx) hh]⟩
    have step : insA n gens (u gp) (Lp.map u).toArray k = ((insK pc gs gp Lp k).map u).toArray ∧
        ∀ x ∈ insK pc gs gp Lp k, C x := by
      unfold insA insK
      rw [hany]
      cases hb : Lp.any fun x => Nat.beq x (pc (gs k) gp)
      · refine ⟨?_, ?_⟩
        · rw [hgk, hcomp _ _ hCk hgp]
          simp
        · intro x hx
          simp only [cond_false, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hLp x hx
          · exact hh
      · exact ⟨by simp, by simpa using hLp⟩
    rw [List.foldl_cons, List.foldl_cons, step.1]
    exact insA_eq hcomp heq hC hg hgp l (fun k' hk' => hl k' (by simp [hk'])) _ step.2

theorem closureList_eq_closK
    (hcomp : ∀ p q, C p → C q → compA n (u p) (u q) = u (pc p q))
    (heq : ∀ p q, C p → C q → eqA n (u p) (u q) = Nat.beq p q)
    (hC : ∀ p q, C p → C q → C (pc p q))
    (hg : ∀ k < gens.size, gens[k]! = u (gs k) ∧ C (gs k))
    (he : idA n = u e) (hCe : C e) (cap : ℕ) :
    closureList n gens cap = ((closK pc gs gens.size cap ([e], 0)).1.map u).toArray ∧
      ∀ x ∈ (closK pc gs gens.size cap ([e], 0)).1, C x := by
  rw [closureList_eq_stepA, closK_eq_foldl]
  have one : ∀ (Lp : List ℕ) (hp : ℕ), (∀ x ∈ Lp, C x) →
      stepA n gens ((Lp.map u).toArray, hp) =
          (((stepK pc gs gens.size (Lp, hp)).1.map u).toArray, (stepK pc gs gens.size (Lp, hp)).2) ∧
        ∀ x ∈ (stepK pc gs gens.size (Lp, hp)).1, C x := by
    intro Lp hp h3
    unfold stepA stepK
    simp only [List.size_toArray, List.length_map]
    by_cases hlt : hp < Lp.length
    · have hb : Nat.blt hp Lp.length = true := Nat.blt_eq.mpr hlt
      have hget : (Lp.map u).toArray[hp]! = u (Lp.getD hp 0) := by
        rw [List.getElem!_toArray, getElem!_pos _ hp (by simpa using hlt), List.getElem_map,
          List.getD_eq_getElem _ _ hlt]
      have hC0 : C (Lp.getD hp 0) := h3 _ (by rw [List.getD_eq_getElem _ _ hlt]; simp)
      have hin := insA_eq hcomp heq hC hg hC0 (List.range' 0 gens.size)
        (fun k hk => by simpa using (List.mem_range'_1.mp hk).2) Lp h3
      have hr : List.range gens.size = List.range' 0 gens.size := List.range_eq_range'
      rw [if_pos hlt, hb, cond_true, hget, hr, hin.1]
      exact ⟨rfl, hin.2⟩
    · have hb : Nat.blt hp Lp.length = false := by
        rw [Bool.eq_false_iff]
        intro h
        exact hlt (Nat.blt_eq.mp h)
      rw [if_neg hlt, hb, cond_false]
      exact ⟨rfl, h3⟩
  have key : ∀ (l : List ℕ) (Lp : List ℕ) (hp : ℕ), (∀ x ∈ Lp, C x) →
      l.foldl (fun s _ => stepA n gens s) ((Lp.map u).toArray, hp) =
          (((l.foldl (fun s _ => stepK pc gs gens.size s) (Lp, hp)).1.map u).toArray,
            (l.foldl (fun s _ => stepK pc gs gens.size s) (Lp, hp)).2) ∧
        ∀ x ∈ (l.foldl (fun s _ => stepK pc gs gens.size s) (Lp, hp)).1, C x := by
    intro l
    induction l with
    | nil => exact fun Lp hp h3 => ⟨rfl, h3⟩
    | cons a l ih =>
      intro Lp hp h3
      obtain ⟨o1, o2⟩ := one Lp hp h3
      rw [List.foldl_cons, List.foldl_cons, o1]
      exact ih _ _ o2
  have h0 : (#[idA n], 0) = (([e].map u).toArray, 0) := by simp [he]
  obtain ⟨k1, k2⟩ := key (List.range' 0 cap) [e] 0 (by simpa using hCe)
  rw [h0, k1]
  exact ⟨rfl, k2⟩

end

theorem lEq_spec (f : ℕ → ℕ) : ∀ (L : List ℕ) (j m : ℕ), lEq f L j m = true →
    j + L.length = m ∧ L = (List.range' j L.length).map f
  | [], j, m, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, rfl⟩
  | x :: xs, j, m, h => by
    unfold lEq at h
    cases hx : Nat.beq x (f j)
    · rw [hx] at h
      exact absurd h Bool.false_ne_true
    · rw [hx, cond_true] at h
      obtain ⟨ih1, ih2⟩ := lEq_spec f xs (j + 1) m h
      refine ⟨by simp only [List.length_cons]; omega, ?_⟩
      rw [List.length_cons, List.range'_succ, List.map_cons, ← ih2, Nat.eq_of_beq_eq_true hx]

theorem lEq_sound {f : ℕ → ℕ} {L : List ℕ} {m : ℕ} (h : lEq f L 0 m = true) :
    L = (List.range m).map f := by
  obtain ⟨h1, h2⟩ := lEq_spec f L 0 m h
  rw [h2, ← List.range_eq_range']
  congr 2
  omega

end CFSG.KC.ClosK

end
