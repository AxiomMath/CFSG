module

public import Certificates.Data.U43Model
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Data.Set.Card

public section

namespace CFSG.KS.U43Mod

open CFSG.KGroups.U43 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

abbrev St : Type := Std.HashSet (ℕ × ℕ × ℕ) × Array (Array ℕ) × Array ℕ × Array ℕ

@[expose] def innerG (step : ℕ → Array ℕ → Array ℕ) (h : ℕ) (x : Array ℕ) (s : St) (j : ℕ) : St :=
  if (!s.1.contains (keyOf (step j x))) = true then
    (s.1.insert (keyOf (step j x)), s.2.1.push (step j x), s.2.2.1.push h, s.2.2.2.push j)
  else s

@[expose] def outerG (step : ℕ → Array ℕ → Array ℕ) (k : ℕ) (s : St) (h : ℕ) : St :=
  if h < s.2.1.size then (List.range' 0 k).foldl (innerG step h s.2.1[h]!) s else s

@[expose] def initS (x0 : Array ℕ) : St :=
  (({} : Std.HashSet (ℕ × ℕ × ℕ)).insert (keyOf x0), #[x0], #[0], #[0])

theorem forIn_yield_foldl {α β : Type} (l : List α) (init : β) (f : α → β → Id (ForInStep β))
    (g : β → α → β) (hf : ∀ a b, f a b = pure (ForInStep.yield (g b a))) :
    forIn l init f = pure (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons, hf]
    exact ih _

theorem bfsRec_eq (step : ℕ → Array ℕ → Array ℕ) (k cap : ℕ) (x0 : Array ℕ) :
    bfsRec step k cap x0 =
      ⟨((List.range cap).foldl (outerG step k) (initS x0)).2.1,
        ((List.range cap).foldl (outerG step k) (initS x0)).2.2.1,
        ((List.range cap).foldl (outerG step k) (initS x0)).2.2.2⟩ := by
  unfold bfsRec
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [forIn_yield_foldl _ _ _ (outerG step k) ?_]
  · rw [List.range_eq_range']
    rfl
  · intro h s
    unfold outerG
    by_cases hc : h < s.2.1.size
    · rw [if_pos hc, if_pos hc, forIn_yield_foldl _ _ _ (innerG step h s.2.1[h]!) ?_]
      · rfl
      · intro j s'
        unfold innerG
        by_cases hc' : (!s'.1.contains (keyOf (step j s.2.1[h]!))) = true
        · rw [if_pos hc', if_pos hc']
        · rw [if_neg hc', if_neg hc']
    · rw [if_neg hc, if_neg hc]

theorem push_get_lt {α : Type} [Inhabited α] {a : Array α} {x : α} {i : ℕ} (h : i < a.size) :
    (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos (a.push x) i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt]

theorem push_get_eq {α : Type} [Inhabited α] {a : Array α} {x : α} : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by simp), Array.getElem_push_eq]

structure Inv (step : ℕ → Array ℕ → Array ℕ) (k : ℕ) (x0 : Array ℕ) (s : St) : Prop where
  szp : s.2.2.1.size = s.2.1.size
  szl : s.2.2.2.size = s.2.1.size
  pos : 0 < s.2.1.size
  head : s.2.1[0]! = x0
  der : ∀ i, 0 < i → i < s.2.1.size →
    s.2.2.1[i]! < i ∧ s.2.2.2[i]! < k ∧ s.2.1[i]! = step s.2.2.2[i]! s.2.1[s.2.2.1[i]!]!
  seen : ∀ key, s.1.contains key = true ↔ ∃ i < s.2.1.size, keyOf s.2.1[i]! = key
  nodup : ∀ i < s.2.1.size, ∀ i' < s.2.1.size, keyOf s.2.1[i]! = keyOf s.2.1[i']! → i = i'

@[expose] def Ext (s s' : St) : Prop :=
  s.2.1.size ≤ s'.2.1.size ∧ ∀ i < s.2.1.size, s'.2.1[i]! = s.2.1[i]!

theorem Ext.refl (s : St) : Ext s s := ⟨le_rfl, fun _ _ => rfl⟩

theorem Ext.trans {s s' s'' : St} (h : Ext s s') (h' : Ext s' s'') : Ext s s'' :=
  ⟨h.1.trans h'.1, fun i hi => (h'.2 i (Nat.lt_of_lt_of_le hi h.1)).trans (h.2 i hi)⟩

theorem inv_init (step : ℕ → Array ℕ → Array ℕ) (k : ℕ) (x0 : Array ℕ) :
    Inv step k x0 (initS x0) where
  szp := rfl
  szl := rfl
  pos := by simp [initS]
  head := rfl
  der := fun i hi hi' => by simp [initS] at hi'; omega
  seen := fun key => by
    simp only [initS, Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false,
      beq_iff_eq]
    constructor
    · intro h
      exact ⟨0, by simp, h⟩
    · rintro ⟨i, hi, h⟩
      simp at hi
      subst hi
      exact h
  nodup := fun i hi i' hi' _ => by simp [initS] at hi hi'; omega

theorem inv_innerG {step : ℕ → Array ℕ → Array ℕ} {k : ℕ} {x0 : Array ℕ} {s : St} {h j : ℕ}
    {x : Array ℕ} (H : Inv step k x0 s) (hh : h < s.2.1.size) (hx : s.2.1[h]! = x) (hj : j < k) :
    Inv step k x0 (innerG step h x s j) ∧ Ext s (innerG step h x s j) ∧
      (innerG step h x s j).1.contains (keyOf (step j x)) = true := by
  obtain ⟨seen, L, par, lab⟩ := s
  dsimp only at H hh hx
  unfold innerG
  dsimp only
  by_cases hc : (!seen.contains (keyOf (step j x))) = true
  · rw [if_pos hc]
    have hc' : seen.contains (keyOf (step j x)) = false := by simpa using hc
    have hsz : (L.push (step j x)).size = L.size + 1 := Array.size_push _
    have hpar : par.size = L.size := H.szp
    have hlab : lab.size = L.size := H.szl
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by simp, fun i hi => push_get_lt hi⟩, ?_⟩
    · simp [hpar]
    · simp [hlab]
    · simp
    · rw [push_get_lt H.pos]
      exact H.head
    · intro i hi0 hi
      dsimp only at hi ⊢
      rw [hsz] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · obtain ⟨d1, d2, d3⟩ := H.der i hi0 hi
        rw [push_get_lt (hpar ▸ hi), push_get_lt (hlab ▸ hi), push_get_lt hi,
          push_get_lt (Nat.lt_trans d1 hi)]
        exact ⟨d1, d2, d3⟩
      · have e1 : (par.push h)[L.size]! = h := by
          rw [← hpar]
          exact push_get_eq
        have e2 : (lab.push j)[L.size]! = j := by
          rw [← hlab]
          exact push_get_eq
        rw [e1, e2, push_get_eq, push_get_lt hh, hx]
        exact ⟨hh, hj, rfl⟩
    · intro key
      dsimp only
      rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, H.seen, hsz]
      constructor
      · rintro (e | ⟨i, hi, e⟩)
        · exact ⟨L.size, Nat.lt_succ_self _, by rw [push_get_eq, e]⟩
        · exact ⟨i, Nat.lt_succ_of_lt hi, by rw [push_get_lt hi, e]⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inr ⟨i, hi, by rw [← push_get_lt hi]; exact e⟩
        · left
          rw [← e, push_get_eq]
    · intro i hi i' hi' e
      dsimp only at hi hi' e
      rw [hsz] at hi hi'
      have hnew : ∀ i < L.size, keyOf L[i]! ≠ keyOf (step j x) := by
        intro i hi e'
        have := (H.seen _).2 ⟨i, hi, e'⟩
        rw [hc'] at this
        exact Bool.false_ne_true this
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
      · rw [push_get_lt hi, push_get_lt hi'] at e
        exact H.nodup i hi i' hi' e
      · rw [push_get_lt hi, push_get_eq] at e
        exact absurd e (hnew i hi)
      · rw [push_get_lt hi', push_get_eq] at e
        exact absurd e.symm (hnew i' hi')
      · rfl
    · simp
  · rw [if_neg hc]
    refine ⟨H, Ext.refl _, by simpa using hc⟩

theorem inv_inner_fold {step : ℕ → Array ℕ → Array ℕ} {k : ℕ} {x0 : Array ℕ} {h : ℕ}
    {x : Array ℕ} : ∀ (l : List ℕ) (s : St), (∀ j ∈ l, j < k) → Inv step k x0 s →
      h < s.2.1.size → s.2.1[h]! = x →
      Inv step k x0 (l.foldl (innerG step h x) s) ∧ Ext s (l.foldl (innerG step h x) s) ∧
        ∀ j ∈ l, (l.foldl (innerG step h x) s).1.contains (keyOf (step j x)) = true
  | [], s, _, H, _, _ => ⟨H, Ext.refl _, fun _ hj => absurd hj List.not_mem_nil⟩
  | j :: l, s, hl, H, hh, hx => by
    obtain ⟨H1, E1, C1⟩ := inv_innerG H hh hx (hl j List.mem_cons_self)
    have hh' : h < (innerG step h x s j).2.1.size := Nat.lt_of_lt_of_le hh E1.1
    have hx' : (innerG step h x s j).2.1[h]! = x := (E1.2 h hh).trans hx
    obtain ⟨H2, E2, C2⟩ := inv_inner_fold l _ (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
      H1 hh' hx'
    refine ⟨H2, E1.trans E2, fun j' hj' => ?_⟩
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hj' with rfl | hj'
    · obtain ⟨i, hi, e⟩ := (H1.seen _).1 C1
      refine (H2.seen _).2 ⟨i, Nat.lt_of_lt_of_le hi E2.1, ?_⟩
      rw [E2.2 i hi, e]
    · exact C2 j' hj'

@[expose] def Done (step : ℕ → Array ℕ → Array ℕ) (k h : ℕ) (s : St) : Prop :=
  ∀ i < h, i < s.2.1.size → ∀ j < k, ∃ i' < s.2.1.size, keyOf s.2.1[i']! = keyOf (step j s.2.1[i]!)

theorem inv_outer (step : ℕ → Array ℕ → Array ℕ) (k : ℕ) (x0 : Array ℕ) : ∀ h : ℕ,
    Inv step k x0 ((List.range h).foldl (outerG step k) (initS x0)) ∧
      Done step k h ((List.range h).foldl (outerG step k) (initS x0))
  | 0 => ⟨inv_init step k x0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | h + 1 => by
    obtain ⟨H, D⟩ := inv_outer step k x0 h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range h).foldl (outerG step k) (initS x0) = s at H D
    unfold outerG
    by_cases hc : h < s.2.1.size
    · rw [if_pos hc]
      obtain ⟨H2, E2, C2⟩ := inv_inner_fold (h := h) (x := s.2.1[h]!) (List.range' 0 k) s
        (fun j hj => by simpa using hj) H hc rfl
      refine ⟨H2, fun i hi hi2 j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · obtain ⟨i', hi', e⟩ := D i hi (Nat.lt_trans hi hc) j hj
        refine ⟨i', Nat.lt_of_lt_of_le hi' E2.1, ?_⟩
        rw [E2.2 i' hi', E2.2 i (Nat.lt_trans hi hc), e]
      · rw [E2.2 i hc]
        exact (H2.seen _).1 (C2 j (by simpa using hj))
    · rw [if_neg hc]
      refine ⟨H, fun i hi hi2 j hj => D i ?_ hi2 j hj⟩
      omega

theorem bfsRec_spec (step : ℕ → Array ℕ → Array ℕ) (k cap : ℕ) (x0 : Array ℕ) :
    (bfsRec step k cap x0).par.size = (bfsRec step k cap x0).L.size ∧
    (bfsRec step k cap x0).lab.size = (bfsRec step k cap x0).L.size ∧
    0 < (bfsRec step k cap x0).L.size ∧ (bfsRec step k cap x0).L[0]! = x0 ∧
    (∀ i, 0 < i → i < (bfsRec step k cap x0).L.size →
      (bfsRec step k cap x0).par[i]! < i ∧ (bfsRec step k cap x0).lab[i]! < k ∧
      (bfsRec step k cap x0).L[i]! = step (bfsRec step k cap x0).lab[i]!
        (bfsRec step k cap x0).L[(bfsRec step k cap x0).par[i]!]!) ∧
    (∀ i < (bfsRec step k cap x0).L.size, ∀ i' < (bfsRec step k cap x0).L.size,
      keyOf (bfsRec step k cap x0).L[i]! = keyOf (bfsRec step k cap x0).L[i']! → i = i') ∧
    (∀ i < (bfsRec step k cap x0).L.size, i < cap → ∀ j < k,
      ∃ i' < (bfsRec step k cap x0).L.size,
        keyOf (bfsRec step k cap x0).L[i']! = keyOf (step j (bfsRec step k cap x0).L[i]!)) := by
  obtain ⟨H, D⟩ := inv_outer step k x0 cap
  rw [bfsRec_eq]
  exact ⟨H.szp, H.szl, H.pos, H.head, H.der, H.nodup, fun i hi hic j hj => D i hic hi j hj⟩

theorem bfsRec_derivOK (n : ℕ) (step : ℕ → Array ℕ → Array ℕ) (k cap : ℕ) (x0 : Array ℕ) :
    derivOK n step k x0 (bfsRec step k cap x0) (bfsRec step k cap x0).L.size = true := by
  obtain ⟨h1, h2, -, h4, h5, -, -⟩ := bfsRec_spec step k cap x0
  have heq : ∀ t : Array ℕ, eqA n t t = true := fun t => by
    rw [eqA, allLt_iff]
    intro i _
    exact beq_self_eq_true _
  simp only [derivOK, Bool.and_eq_true, beq_iff_eq, h1, h2, h4, heq, and_true, true_and,
    allLt_iff, Bool.or_eq_true, decide_eq_true_eq]
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact Or.inl rfl
  · obtain ⟨d1, d2, d3⟩ := h5 i hi0 hi
    rw [d3]
    exact Or.inr ⟨⟨d1, d2⟩, heq _⟩

theorem bfsRec_keysNodup (step : ℕ → Array ℕ → Array ℕ) (k cap : ℕ) (x0 : Array ℕ) :
    keysNodup (bfsRec step k cap x0).L = true := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := bfsRec_spec step k cap x0
  rw [keysNodup, decide_eq_true_eq, List.nodup_iff_injective_get]
  intro a b e
  simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at e
  have ha : (a : ℕ) < (bfsRec step k cap x0).L.size := by simpa using a.2
  have hb : (b : ℕ) < (bfsRec step k cap x0).L.size := by simpa using b.2
  refine Fin.ext (h6 a ha b hb ?_)
  rw [getElem!_pos (bfsRec step k cap x0).L (a : ℕ) ha,
    getElem!_pos (bfsRec step k cap x0).L (b : ℕ) hb]
  exact e

theorem bfsRec_enum {α : Type*} {step : ℕ → Array ℕ → Array ℕ} {k cap : ℕ} {x0 : Array ℕ}
    (rep : Array ℕ → α → Prop) (X : Set α) (f : ℕ → α → α) (a0 : α) (hX : X.Finite)
    (h0 : rep x0 a0) (ha0 : a0 ∈ X)
    (hstep : ∀ t a, rep t a → a ∈ X → ∀ j < k, rep (step j t) (f j a) ∧ f j a ∈ X)
    (hkey : ∀ t t' a a', rep t a → rep t' a' → a ∈ X → a' ∈ X → (keyOf t = keyOf t' ↔ a = a'))
    (hgen : ∀ Y : Set α, a0 ∈ Y → (∀ a ∈ Y, ∀ j < k, f j a ∈ Y) → X ⊆ Y)
    (hcap : X.ncard ≤ cap) :
    (bfsRec step k cap x0).L.size = X.ncard ∧
      (∀ i < (bfsRec step k cap x0).L.size, ∃ a ∈ X, rep (bfsRec step k cap x0).L[i]! a) ∧
      ∀ a ∈ X, ∃ i < (bfsRec step k cap x0).L.size, rep (bfsRec step k cap x0).L[i]! a := by
  obtain ⟨-, -, h1, h4, h5, h6, h7⟩ := bfsRec_spec step k cap x0
  set L := (bfsRec step k cap x0).L
  set N := L.size
  have hrep : ∀ i < N, ∃ a ∈ X, rep L[i]! a := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨a0, ha0, h4 ▸ h0⟩
      · obtain ⟨d1, d2, d3⟩ := h5 i hi0 hi
        obtain ⟨a, ha, hra⟩ := ih _ d1 (Nat.lt_trans d1 hi)
        obtain ⟨hr, hm⟩ := hstep _ a hra ha _ d2
        exact ⟨_, hm, d3 ▸ hr⟩
  have : Nonempty α := ⟨a0⟩
  choose! e heX her using hrep
  let R : Set ℕ := ↑(Finset.range N)
  have hmem : ∀ i, i ∈ R ↔ i < N := fun i => by simp [R]
  have hRc : R.ncard = N := by rw [Set.ncard_coe_finset, Finset.card_range]
  have hinj : Set.InjOn e R := by
    intro i hi i' hi' he
    have hi : i < N := (hmem i).1 hi
    have hi' : i' < N := (hmem i').1 hi'
    exact h6 i hi i' hi' ((hkey _ _ _ _ (her i hi) (her i' hi') (heX i hi) (heX i' hi')).2 he)
  have hNle : N ≤ X.ncard := by
    have := Set.ncard_le_ncard_of_injOn e (fun i hi => heX i ((hmem i).1 hi)) hinj hX
    rwa [hRc] at this
  have hsub : X ⊆ e '' R := by
    refine hgen _ ⟨0, (hmem 0).2 h1, ?_⟩ ?_
    · have hr0 : rep L[0]! a0 := h4 ▸ h0
      exact (hkey _ _ _ _ (her 0 h1) hr0 (heX 0 h1) ha0).1 rfl
    · rintro _ ⟨i, hi, rfl⟩ j hj
      have hi : i < N := (hmem i).1 hi
      obtain ⟨hr, hm⟩ := hstep _ _ (her i hi) (heX i hi) j hj
      obtain ⟨i', hi', ek⟩ := h7 i hi (by omega) j hj
      exact ⟨i', (hmem i').2 hi', (hkey _ _ _ _ (her i' hi') hr (heX i' hi') hm).1 ek⟩
  have hXeq : X = e '' R := by
    refine hsub.antisymm ?_
    rintro _ ⟨i, hi, rfl⟩
    exact heX i ((hmem i).1 hi)
  refine ⟨?_, fun i hi => ⟨e i, heX i hi, her i hi⟩, fun a ha => ?_⟩
  · rw [hXeq, hinj.ncard_image, hRc]
  · obtain ⟨i, hi, rfl⟩ := hsub ha
    exact ⟨i, (hmem i).1 hi, her i ((hmem i).1 hi)⟩

end CFSG.KS.U43Mod

end
