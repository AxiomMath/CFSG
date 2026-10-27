module

public import CFSG.Sporadic.SuzRecog.LevelTwoCheck
public import CFSG.Certificates.Kernel.Spor.KeyBfsGen

public section

namespace CFSG.KS.OrbElems

open CFSG.KS.KeyBfsG CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.KS.KeyBfs (push_lt push_eq)

@[expose] def stE (gs : Array Elt) (k : Nat) (u : Elt) : Elt :=
  (compA 1782 gs[k]!.1 u.1, compA 1782 u.2 gs[k]!.2)

@[expose] def orbSt (gs : Array Elt) (s x : Nat) : Nat := actV gs[s]!.1 gs[s]!.2 x

@[expose] def orbKey (gs : Array Elt) (b : Nat) : Array Nat × Array Nat × Array Nat :=
  keyBfsG (fun x => x) (orbSt gs) gs.size b b 2997

abbrev OSt := Std.HashMap Nat Elt × Array Nat

@[expose] def innerO (gs : Array Elt) (x : Nat) (e ei : Array Nat) (k : Nat) (s : OSt) :
    Id (ForInStep OSt) :=
  if (!s.1.contains (actV gs[k]!.1 gs[k]!.2 x)) = true then
    pure (ForInStep.yield (s.1.insert (actV gs[k]!.1 gs[k]!.2 x)
      (compA 1782 gs[k]!.1 e, compA 1782 ei gs[k]!.2), s.2.push (actV gs[k]!.1 gs[k]!.2 x)))
  else pure (ForInStep.yield (s.1, s.2))

@[expose] def outerO (gs : Array Elt) (h : Nat) (s : OSt) : Id (ForInStep OSt) :=
  if h < s.2.size then
    pure (ForInStep.yield (Id.run (forIn (List.range' 0 gs.size) (s.1, s.2)
      (innerO gs s.2[h]! (s.1.getD s.2[h]! eltOne).1 (s.1.getD s.2[h]! eltOne).2))))
  else pure (ForInStep.yield (s.1, s.2))

theorem orbitElems_eq (gs : Array Elt) (b : Nat) :
    orbitElems gs b = (Id.run (forIn (List.range' 0 2997)
      (((∅ : Std.HashMap Nat Elt).insert b eltOne, #[b]) : OSt) (outerO gs))).1 := by
  unfold orbitElems
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem forIn_rel {β γ : Type} (R : Nat → β → γ → Prop) (f : Nat → β → Id (ForInStep β))
    (g : Nat → γ → Id (ForInStep γ)) :
    ∀ (n s : Nat) (b : β) (c : γ),
      (∀ j < n, ∀ b c, R j b c → ∃ b' c', f (s + j) b = pure (ForInStep.yield b') ∧
        g (s + j) c = pure (ForInStep.yield c') ∧ R (j + 1) b' c') →
      R 0 b c → R n (Id.run (forIn (List.range' s n) b f)) (Id.run (forIn (List.range' s n) c g))
  | 0, _, _, _, _, h0 => h0
  | n + 1, s, b, c, h, h0 => by
    obtain ⟨b', c', hf, hg, h1⟩ := h 0 (by omega) b c h0
    rw [Nat.add_zero] at hf hg
    rw [List.range'_succ, List.forIn_cons, List.forIn_cons, hf, hg]
    exact forIn_rel (fun j => R (j + 1)) f g n (s + 1) b' c'
      (fun j hj b c hR => by
        obtain ⟨b'', c'', e1, e2, e3⟩ := h (j + 1) (by omega) b c hR
        exact ⟨b'', c'', by rw [← e1]; congr 1; omega, by rw [← e2]; congr 1; omega, e3⟩) h1

@[expose] def Rel (gs : Array Elt) (o : OSt) (t : GSt Nat) : Prop :=
  o.2 = t.1 ∧ t.2.1.size = t.1.size ∧ t.2.2.1.size = t.1.size ∧ 0 < t.1.size ∧
    (∀ y, o.1.contains y = t.2.2.2.contains y) ∧
    (∀ i < t.1.size, o.1.contains t.1[i]! = true) ∧
    o.1.getD t.1[0]! eltOne = eltOne ∧
    ∀ i < t.1.size, 0 < i → t.2.1[i]! < i ∧ t.2.2.1[i]! < gs.size ∧
      o.1.getD t.1[i]! eltOne = stE gs t.2.2.1[i]! (o.1.getD t.1[t.2.1[i]!]! eltOne)

theorem getD_insert_ne {m : Std.HashMap Nat Elt} {y z : Nat} {v : Elt} (h : y ≠ z) :
    (m.insert y v).getD z eltOne = m.getD z eltOne := by
  rw [Std.HashMap.getD_insert]
  simp [h]

theorem rel_inner {gs : Array Elt} {h k x : Nat} {u : Elt} {o : OSt} {t : GSt Nat}
    (hk : k < gs.size) (hR : Rel gs o t) (hh : h < t.1.size) (hx : t.1[h]! = x)
    (hu : o.1.getD t.1[h]! eltOne = u) :
    ∃ o' t', innerO gs x u.1 u.2 k o = pure (ForInStep.yield o') ∧
      innerG (fun x => x) (orbSt gs) h k t = pure (ForInStep.yield t') ∧
      Rel gs o' t' ∧ h < t'.1.size ∧ t'.1[h]! = x ∧ o'.1.getD t'.1[h]! eltOne = u := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hR
  subst hx
  set y := actV gs[k]!.1 gs[k]!.2 t.1[h]! with hy
  by_cases hc : t.2.2.2.contains y = true
  · refine ⟨(o.1, o.2), (t.1, t.2.1, t.2.2.1, t.2.2.2), ?_, ?_, ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩,
      hh, rfl, hu⟩
    · unfold innerO
      rw [← hy, e5, hc]
      rfl
    · unfold innerG orbSt
      rw [← hy, hc]
      rfl
  · have hnc : t.2.2.2.contains y = false := Bool.eq_false_iff.2 hc
    have hne : ∀ i < t.1.size, y ≠ t.1[i]! := by
      intro i hi e
      have := e6 i hi
      rw [← e, e5, hnc] at this
      exact Bool.false_ne_true this
    refine ⟨(o.1.insert y (compA 1782 gs[k]!.1 u.1, compA 1782 u.2 gs[k]!.2), o.2.push y),
      (t.1.push y, t.2.1.push h, t.2.2.1.push k, t.2.2.2.insert y), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold innerO
      rw [← hy, e5, hnc]
      rfl
    · unfold innerG orbSt
      rw [← hy, hnc]
      rfl
    · refine ⟨by rw [e1], by simp [e2], by simp [e3], by simp, fun z => ?_, fun i hi => ?_, ?_,
        fun i hi hi0 => ?_⟩
      · simp only
        rw [Std.HashMap.contains_insert, Std.HashSet.contains_insert, e5]
      · simp only [Array.size_push] at hi
        simp only
        rw [Std.HashMap.contains_insert]
        rcases Nat.lt_or_ge i t.1.size with a | a
        · rw [push_lt a, e6 i a, Bool.or_true]
        · have : i = t.1.size := by omega
          subst this
          rw [push_eq, beq_self_eq_true, Bool.true_or]
      · simp only
        rw [push_lt e4, getD_insert_ne (hne 0 e4), e7]
      · simp only [Array.size_push] at hi
        simp only
        rcases Nat.lt_or_ge i t.1.size with a | a
        · obtain ⟨f1, f2, f3⟩ := e8 i a hi0
          rw [push_lt a, push_lt (by omega : i < t.2.1.size), push_lt (by omega : i < t.2.2.1.size),
            push_lt (by omega : t.2.1[i]! < t.1.size), getD_insert_ne (hne i a),
            getD_insert_ne (hne _ (by omega))]
          exact ⟨f1, f2, f3⟩
        · have : i = t.1.size := by omega
          subst this
          have p1 : (t.2.1.push h)[t.1.size]! = h := by rw [← e2]; exact push_eq
          have p2 : (t.2.2.1.push k)[t.1.size]! = k := by rw [← e3]; exact push_eq
          rw [push_eq, p1, p2, push_lt hh, getD_insert_ne (hne h hh), hu]
          refine ⟨hh, hk, ?_⟩
          rw [Std.HashMap.getD_insert]
          simp only [beq_self_eq_true, ↓reduceIte]
          rfl
    · simp only [Array.size_push]
      omega
    · exact push_lt hh
    · simp only
      rw [push_lt hh, getD_insert_ne (hne h hh), hu]

theorem rel_outer {gs : Array Elt} {h : Nat} {o : OSt} {t : GSt Nat} (hR : Rel gs o t) :
    ∃ o' t', outerO gs h o = pure (ForInStep.yield o') ∧
      outerG (fun x => x) (orbSt gs) gs.size h t = pure (ForInStep.yield t') ∧ Rel gs o' t' := by
  by_cases hh : h < t.1.size
  · have ho : h < o.2.size := by rw [hR.1]; exact hh
    set u := o.1.getD o.2[h]! eltOne with hu
    refine ⟨Id.run (forIn (List.range' 0 gs.size) (o.1, o.2) (innerO gs o.2[h]! u.1 u.2)),
      Id.run (forIn (List.range' 0 gs.size) (t.1, t.2.1, t.2.2.1, t.2.2.2)
        (innerG (fun x => x) (orbSt gs) h)),
      by simp only [outerO, ho, ↓reduceIte, hu], by simp only [outerG, hh, ↓reduceIte], ?_⟩
    have := forIn_rel (fun _ o1 t1 => Rel gs o1 t1 ∧ h < t1.1.size ∧ t1.1[h]! = o.2[h]! ∧
        o1.1.getD t1.1[h]! eltOne = u)
      (innerO gs o.2[h]! u.1 u.2) (innerG (fun x => x) (orbSt gs) h) gs.size 0 (o.1, o.2)
      (t.1, t.2.1, t.2.2.1, t.2.2.2)
      (fun j hj o1 t1 hP => by
        obtain ⟨o', t', a1, a2, a3, a4, a5, a6⟩ :=
          rel_inner (k := 0 + j) (by omega) hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
        exact ⟨o', t', a1, a2, a3, a4, a5, a6⟩)
      ⟨hR, hh, by rw [hR.1], by rw [hu, hR.1]⟩
    exact this.1
  · have ho : ¬ h < o.2.size := by rw [hR.1]; exact hh
    exact ⟨(o.1, o.2), (t.1, t.2.1, t.2.2.1, t.2.2.2), by simp only [outerO, ho, ↓reduceIte],
      by simp only [outerG, hh, ↓reduceIte], hR⟩

theorem orbitElems_tree (gs : Array Elt) (b : Nat) :
    (orbitElems gs b).getD (orbKey gs b).1[0]! eltOne = eltOne ∧
      ∀ i < (orbKey gs b).1.size, 0 < i → (orbKey gs b).2.1[i]! < i ∧
        (orbKey gs b).2.2[i]! < gs.size ∧
        (orbitElems gs b).getD (orbKey gs b).1[i]! eltOne =
          stE gs (orbKey gs b).2.2[i]! ((orbitElems gs b).getD
            (orbKey gs b).1[(orbKey gs b).2.1[i]!]! eltOne) := by
  have h0 : Rel gs ((∅ : Std.HashMap Nat Elt).insert b eltOne, #[b]) (initG b b) := by
    refine ⟨rfl, rfl, rfl, by simp [initG], fun y => ?_, fun i hi => ?_, ?_, fun i hi hi0 => ?_⟩
    · simp [initG, Std.HashMap.contains_insert, Std.HashSet.contains_insert]
    · have : i = 0 := by simp [initG] at hi; omega
      subst this
      simp [initG]
    · simp [initG]
    · simp [initG] at hi
      omega
  have := forIn_rel (fun _ o t => Rel gs o t) (outerO gs) (outerG (fun x => x) (orbSt gs) gs.size)
    2997 0 _ _ (fun _ _ o t hR => rel_outer hR) h0
  rw [orbitElems_eq, orbKey, keyBfsG_eq]
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := this
  exact ⟨e7, fun i hi hi0 => e8 i hi hi0⟩

end CFSG.KS.OrbElems

end
