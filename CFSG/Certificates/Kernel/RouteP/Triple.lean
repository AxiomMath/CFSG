module

public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.RouteP.Plane
public import Mathlib

public section

namespace CFSG.KS.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KS.PK
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] def codeImg (p : Nat → Nat) (c : Nat) : Nat :=
  576 * p (c / 576) + 24 * p (c / 24 % 24) + p (c % 24)

@[expose] def tripF (pa pb : Array Nat) (l c : Nat) : Nat :=
  if l = 0 then codeImg (fun i => pa[i]!) c else codeImg (fun i => pb[i]!) c

abbrev TS := Array Nat × Array Nat × Array Nat × Array Nat × Array Nat × Array Nat

@[expose] def letterT (pa pb : Array Nat) (h : Nat) (b : TS) (a : Nat) : TS :=
  if (b.fst[576 * (if (a == 0) = true then pa else pb)[b.snd.fst[h]!]! +
        24 * (if (a == 0) = true then pa else pb)[b.snd.snd.fst[h]!]! +
        (if (a == 0) = true then pa else pb)[b.snd.snd.snd.fst[h]!]!]! == 13824) = true then
    (b.fst.set!
        (576 * (if (a == 0) = true then pa else pb)[b.snd.fst[h]!]! +
            24 * (if (a == 0) = true then pa else pb)[b.snd.snd.fst[h]!]! +
          (if (a == 0) = true then pa else pb)[b.snd.snd.snd.fst[h]!]!)
        b.snd.fst.size,
      b.snd.fst.push (if (a == 0) = true then pa else pb)[b.snd.fst[h]!]!,
      b.snd.snd.fst.push (if (a == 0) = true then pa else pb)[b.snd.snd.fst[h]!]!,
      b.snd.snd.snd.fst.push (if (a == 0) = true then pa else pb)[b.snd.snd.snd.fst[h]!]!,
      b.snd.snd.snd.snd.fst.push h, b.snd.snd.snd.snd.snd.push a)
  else b

@[expose] def stepTr (pa pb : Array Nat) (b : TS) (h : Nat) : TS :=
  if h < b.snd.fst.size then (List.range' 0 2).foldl (letterT pa pb h) b else b

@[expose] def initTr : TS := ((Array.replicate 13824 13824).set! 26 0, #[0], #[1], #[2], #[0], #[0])

@[expose] def finalTr (b : TS) : TripleTree :=
  { us := b.snd.fst, vs := b.snd.snd.fst, ws := b.snd.snd.snd.fst, par := b.snd.snd.snd.snd.fst,
    lab := b.snd.snd.snd.snd.snd, pos := b.fst }

theorem foldl_fixedT {β : Type} (g : β → Nat → β) (b : β) :
    ∀ l : List Nat, (∀ h ∈ l, g b h = b) → l.foldl g b = b
  | [], _ => rfl
  | h :: l, H => by
    rw [List.foldl_cons, H h (List.mem_cons_self ..)]
    exact foldl_fixedT g b l fun h' hh' => H h' (List.mem_cons_of_mem _ hh')

theorem forIn_range'_breakT {β : Type} (f : Nat → β → β) (c : Nat → β → Prop)
    [∀ h b, Decidable (c h b)] (hmono : ∀ h h' b, h ≤ h' → ¬ c h b → ¬ c h' b) :
    ∀ (k s : Nat) (b : β),
      forIn (m := Id) (List.range' s k) b
          (fun h b => if c h b then pure (ForInStep.yield (f h b)) else pure (ForInStep.done b)) =
        (List.range' s k).foldl (fun b h => if c h b then f h b else b) b
  | 0, _, _ => rfl
  | k + 1, s, b => by
    rw [List.range'_succ, List.forIn_cons, List.foldl_cons]
    by_cases hc : c s b
    · simp only [hc, if_true, pure_bind]
      exact forIn_range'_breakT f c hmono k (s + 1) (f s b)
    · simp only [hc, if_false, pure_bind]
      refine (foldl_fixedT _ b _ fun h hh => ?_).symm
      rw [List.mem_range'_1] at hh
      exact if_neg (hmono s h b (by omega) hc)

theorem ite_pure_yieldT {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

theorem tripleBFS_eq_foldl (pa pb : Array Nat) :
    tripleBFS pa pb = finalTr ((List.range 13824).foldl (stepTr pa pb) initTr) := by
  unfold tripleBFS
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ite_pure_yieldT, List.forIn_pure_yield_eq_foldl, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, bind_pure, Prod.eta]
  rw [List.range_eq_range']
  exact congrArg finalTr (forIn_range'_breakT (β := TS)
    (fun h b => (List.range' 0 2).foldl (letterT pa pb h) b) (fun h b => h < b.snd.fst.size)
    (fun h h' b hh hc hc' => hc (by omega)) 13824 0 initTr)

structure TRel (s : BS) (b : TS) : Prop where
  size : b.1.size = 13824
  us : b.2.1 = (s.pts.map (· / 576)).toArray
  vs : b.2.2.1 = (s.pts.map fun c => c / 24 % 24).toArray
  ws : b.2.2.2.1 = (s.pts.map (· % 24)).toArray
  par : b.2.2.2.2.1 = s.par.toArray
  lab : b.2.2.2.2.2 = s.lab.toArray
  pos : ∀ x < 13824, b.1[x]! = if x ∈ s.pts then s.pts.idxOf x else 13824
  nodup : s.pts.Nodup
  lt : ∀ p ∈ s.pts, p < 13824

theorem getElem!_mapT (f : Nat → Nat) (l : List Nat) {h : Nat} (hh : h < l.length) :
    ((l.map f).toArray)[h]! = f (l.getD h 0) := by
  rw [getElem!_pos _ h (by simpa using hh)]
  simp [List.getD_eq_getElem?_getD, hh]

theorem length_le_of_nodupT {n : Nat} {l : List Nat} (hl : l.Nodup) (h : ∀ p ∈ l, p < n) :
    l.length ≤ n := by
  have := hl.length_le_of_subset (l₂ := List.range n) fun p hp => List.mem_range.2 (h p hp)
  simpa using this

variable {pa pb : Array Nat}

theorem tripF_lt (hpa : ∀ i < 24, pa[i]! < 24) (hpb : ∀ i < 24, pb[i]! < 24) (l : Nat) {c : Nat}
    (hc : c < 13824) : tripF pa pb l c < 13824 := by
  unfold tripF
  simp only [codeImg]
  have h1 : c / 576 < 24 := by omega
  have h2 : c / 24 % 24 < 24 := Nat.mod_lt _ (by decide)
  have h3 : c % 24 < 24 := Nat.mod_lt _ (by decide)
  split
  · have := hpa _ h1; have := hpa _ h2; have := hpa _ h3; omega
  · have := hpb _ h1; have := hpb _ h2; have := hpb _ h3; omega

theorem letterT_rel (hpa : ∀ i < 24, pa[i]! < 24) (hpb : ∀ i < 24, pb[i]! < 24) {s : BS} {b : TS}
    (hs : TRel s b) {h : Nat} (hh : h < s.pts.length) {a : Nat} :
    TRel (BS.letter (tripF pa pb) h (s.pts.getD h 0) s a) (letterT pa pb h b a) := by
  set x := s.pts.getD h 0 with hx
  have hxl : x < 13824 := hs.lt _ (by simp [hx, List.getD_eq_getElem?_getD, hh])
  have hu : b.2.1[h]! = x / 576 := by rw [hs.us, getElem!_mapT _ _ hh]
  have hv : b.2.2.1[h]! = x / 24 % 24 := by rw [hs.vs, getElem!_mapT (fun c => c / 24 % 24) _ hh]
  have hw : b.2.2.2.1[h]! = x % 24 := by rw [hs.ws, getElem!_mapT _ _ hh]
  set p := if (a == 0) = true then pa else pb with hp
  have hpp : ∀ i < 24, p[i]! < 24 := by
    intro i hi
    rw [hp]
    split
    · exact hpa i hi
    · exact hpb i hi
  have hF : tripF pa pb a x = 576 * p[x / 576]! + 24 * p[x / 24 % 24]! + p[x % 24]! := by
    unfold tripF codeImg
    rw [hp]
    by_cases ha : a = 0
    · subst ha; simp
    · simp [ha]
  have hq := tripF_lt hpa hpb a hxl
  have h1 : x / 576 < 24 := by omega
  have h2 : x / 24 % 24 < 24 := Nat.mod_lt _ (by decide)
  have h3 : x % 24 < 24 := Nat.mod_lt _ (by decide)
  have d1 : tripF pa pb a x / 576 = p[x / 576]! := by
    rw [hF]; have := hpp _ h1; have := hpp _ h2; have := hpp _ h3; omega
  have d2 : tripF pa pb a x / 24 % 24 = p[x / 24 % 24]! := by
    rw [hF]; have := hpp _ h1; have := hpp _ h2; have := hpp _ h3; omega
  have d3 : tripF pa pb a x % 24 = p[x % 24]! := by
    rw [hF]; have := hpp _ h1; have := hpp _ h2; have := hpp _ h3; omega
  have hlen : s.pts.length ≤ 13824 := length_le_of_nodupT hs.nodup hs.lt
  have hv' := hs.pos _ hq
  unfold BS.letter letterT
  rw [hu, hv, hw, ← hp, ← hF]
  by_cases hmem : tripF pa pb a x ∈ s.pts
  · have hne : b.1[tripF pa pb a x]! ≠ 13824 := by
      rw [hv', if_pos hmem]
      have := List.idxOf_lt_length_of_mem hmem
      omega
    rw [if_pos hmem, if_neg (by simpa using hne)]
    exact hs
  · rw [if_neg hmem, hv', if_neg hmem, if_pos (by simp)]
    have hsz : b.2.1.size = s.pts.length := by rw [hs.us]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Array.size_set!]
      exact hs.size
    · change b.2.1.push _ = _
      rw [hs.us, List.push_toArray, List.map_append, ← d1]
      rfl
    · change b.2.2.1.push _ = _
      rw [hs.vs, List.push_toArray, List.map_append, ← d2]
      rfl
    · change b.2.2.2.1.push _ = _
      rw [hs.ws, List.push_toArray, List.map_append, ← d3]
      rfl
    · change b.2.2.2.2.1.push h = _
      rw [hs.par, List.push_toArray]
    · change b.2.2.2.2.2.push a = _
      rw [hs.lab, List.push_toArray]
    · intro y hy
      by_cases e : y = tripF pa pb a x
      · subst e
        rw [Array.getElem!_set!_self _ _ _ (by rw [hs.size]; exact hq), hsz, if_pos (by simp),
          List.idxOf_append, if_neg hmem]
        simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), hs.pos y hy]
        by_cases hy' : y ∈ s.pts
        · rw [if_pos hy', if_pos (List.mem_append_left _ hy'), List.idxOf_append, if_pos hy']
        · rw [if_neg hy', if_neg]
          simp [hy', e]
    · rw [List.nodup_append]
      refine ⟨hs.nodup, by simp, ?_⟩
      intro a' ha b' hb
      rw [List.mem_singleton] at hb
      rintro rfl
      exact hmem (hb ▸ ha)
    · intro q hq'
      rcases List.mem_append.1 hq' with hq' | hq'
      · exact hs.lt q hq'
      · rw [List.mem_singleton] at hq'
        exact hq' ▸ hq

theorem stepTr_rel (hpa : ∀ i < 24, pa[i]! < 24) (hpb : ∀ i < 24, pb[i]! < 24) {s : BS} {b : TS}
    (hs : TRel s b) (h : Nat) :
    TRel (BS.step (tripF pa pb) [0, 1] s h) (stepTr pa pb b h) := by
  unfold BS.step stepTr
  have hsz : b.2.1.size = s.pts.length := by rw [hs.us]; simp
  by_cases hh : h < s.pts.length
  · rw [if_pos hh, if_pos (hsz ▸ hh)]
    have e : List.range' 0 2 = [0, 1] := rfl
    rw [e]
    simp only [List.foldl_cons, List.foldl_nil]
    have r0 := letterT_rel (a := 0) hpa hpb hs hh
    have hpts : (BS.letter (tripF pa pb) h (s.pts.getD h 0) s 0).pts.getD h 0 = s.pts.getD h 0 := by
      unfold BS.letter
      split
      · rfl
      · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hh]
    have hh' : h < (BS.letter (tripF pa pb) h (s.pts.getD h 0) s 0).pts.length := by
      unfold BS.letter
      split
      · exact hh
      · simp; omega
    have r1 := letterT_rel (a := 1) hpa hpb r0 hh'
    rwa [hpts] at r1
  · rw [if_neg hh, if_neg (by omega)]
    exact hs

theorem initTr_rel : TRel ⟨[26], [0], [0]⟩ initTr := by
  refine ⟨by simp [initTr], rfl, rfl, rfl, rfl, rfl, ?_, by simp, ?_⟩
  · intro x hx
    simp only [initTr]
    by_cases e : x = 26
    · subst e
      rw [Array.getElem!_set!_self _ _ _ (by simp)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), getElem!_pos _ _ (by simpa using hx),
        Array.getElem_replicate]
      simp [e]
  · intro p hp
    simp only [List.mem_singleton] at hp
    omega

theorem trun_rel (hpa : ∀ i < 24, pa[i]! < 24) (hpb : ∀ i < 24, pb[i]! < 24) (k : Nat) :
    TRel ((List.range k).foldl (BS.step (tripF pa pb) [0, 1]) ⟨[26], [0], [0]⟩)
      ((List.range k).foldl (stepTr pa pb) initTr) := by
  induction k with
  | zero => exact initTr_rel
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    exact stepTr_rel hpa hpb ih k

theorem idxOf_getDT {l : List Nat} (hnd : l.Nodup) {k : Nat} (hk : k < l.length) :
    l.idxOf (l.getD k 0) = k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.Nodup.idxOf_getElem hnd k hk

theorem getD_memT {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
  exact List.getElem_mem h

theorem getD_idxOfT {l : List Nat} {q : Nat} (hq : q ∈ l) : l.getD (l.idxOf q) 0 = q := by
  simp [List.getD_eq_getElem?_getD, List.idxOf_lt_length_of_mem hq]

set_option maxRecDepth 100000 in
theorem tripleOK_tripleBFS (hsa : pa.size = 24) (hsb : pb.size = 24)
    (hpa : ∀ i < 24, pa[i]! < 24) (hpb : ∀ i < 24, pb[i]! < 24)
    (hall : ∀ P : Nat → Prop, P 26 → (∀ x, P x → P (tripF pa pb 0 x) ∧ P (tripF pa pb 1 x)) →
      ∀ u < 24, ∀ v < 24, ∀ w < 24, u ≠ v → u ≠ w → v ≠ w → P (576 * u + 24 * v + w)) :
    tripleOK pa pb (tripleBFS pa pb) = true := by
  have hF : ∀ l ∈ [0, 1], ∀ x < 13824, tripF pa pb l x < 13824 :=
    fun l _ x hx => tripF_lt hpa hpb l hx
  have hok := run_ok hF (by decide : 26 < 13824)
  have hcl := run_closed hF (by decide : 26 < 13824)
  have hrel := trun_rel hpa hpb 13824
  unfold BS.run at hok hcl
  rw [tripleBFS_eq_foldl]
  generalize (List.range 13824).foldl (BS.step (tripF pa pb) [0, 1]) ⟨[26], [0], [0]⟩ = s
    at hok hcl hrel
  generalize (List.range 13824).foldl (stepTr pa pb) initTr = b at hrel
  have hmem : ∀ u < 24, ∀ v < 24, ∀ w < 24, u ≠ v → u ≠ w → v ≠ w →
      576 * u + 24 * v + w ∈ s.pts := by
    refine hall (· ∈ s.pts) ?_ ?_
    · rw [← hok.root]
      simp [List.getD_eq_getElem?_getD, hok.pos]
    · intro x hx
      exact ⟨hcl x hx 0 (by simp), hcl x hx 1 (by simp)⟩
  have hlenpar := hok.len_par
  have hlenlab := hok.len_lab
  have hus : ∀ k < s.pts.length, b.2.1[k]! = s.pts.getD k 0 / 576 := fun k hk => by
    rw [hrel.us, getElem!_mapT _ _ hk]
  have hvs : ∀ k < s.pts.length, b.2.2.1[k]! = s.pts.getD k 0 / 24 % 24 := fun k hk => by
    rw [hrel.vs, getElem!_mapT (fun c => c / 24 % 24) _ hk]
  have hws : ∀ k < s.pts.length, b.2.2.2.1[k]! = s.pts.getD k 0 % 24 := fun k hk => by
    rw [hrel.ws, getElem!_mapT _ _ hk]
  have hpar : ∀ k < s.pts.length, b.2.2.2.2.1[k]! = s.par.getD k 0 := fun k hk => by
    rw [hrel.par, getElem!_pos _ k (by simp [hlenpar, hk])]
    simp [List.getD_eq_getElem?_getD, hlenpar, hk]
  have hlab : ∀ k < s.pts.length, b.2.2.2.2.2[k]! = s.lab.getD k 0 := fun k hk => by
    rw [hrel.lab, getElem!_pos _ k (by simp [hlenlab, hk])]
    simp [List.getD_eq_getElem?_getD, hlenlab, hk]
  have hsz : b.2.1.size = s.pts.length := by rw [hrel.us]; simp
  unfold tripleOK finalTr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true, and_assoc]
  have h0 := hok.pos
  have hr := hok.root
  refine ⟨hsa, hsb, by rw [hrel.vs, hrel.us]; simp, by rw [hrel.ws, hrel.us]; simp,
    by rw [hrel.par, hrel.us]; simp [hlenpar], by rw [hrel.lab, hrel.us]; simp [hlenlab],
    by rw [hsz]; exact h0, by rw [hus 0 h0, hr], by rw [hvs 0 h0, hr], by rw [hws 0 h0, hr], ?_, ?_⟩
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro k hk1 hk
    rw [hsz] at hk
    have hpk := hok.par_lt k hk1 hk
    have hlk := hok.lab_mem k hk1 hk
    have hek := hok.edge k hk1 hk
    have hpl : s.par.getD k 0 < s.pts.length := by omega
    have hxl : s.pts.getD (s.par.getD k 0) 0 < 13824 := hok.lt _ (getD_memT hpl)
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
    rw [hpar k hk]
    refine ⟨hpk, ?_⟩
    rw [hlab k hk]
    unfold tripleEdge
    simp only [Bool.and_eq_true, beq_iff_eq, hpar k hk]
    rw [hus k hk, hvs k hk, hws k hk, hus _ hpl, hvs _ hpl, hws _ hpl, ← hek]
    set x := s.pts.getD (s.par.getD k 0) 0
    have h1 : x / 576 < 24 := by omega
    have h2 : x / 24 % 24 < 24 := Nat.mod_lt _ (by decide)
    have h3 : x % 24 < 24 := Nat.mod_lt _ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlk
    rcases hlk with e | e
    · left
      rw [e]
      refine ⟨rfl, ?_⟩
      unfold tripF codeImg
      simp only [if_pos]
      have := hpa _ h1; have := hpa _ h2; have := hpa _ h3
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
    · right
      rw [e]
      refine ⟨rfl, ?_⟩
      unfold tripF codeImg
      simp only [one_ne_zero, if_false]
      have := hpb _ h1; have := hpb _ h2; have := hpb _ h3
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro u _ hu
    rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro v _ hv
    rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro w _ hw
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    by_cases e1 : u = v
    · simp [e1]
    by_cases e2 : u = w
    · simp [e2]
    by_cases e3 : v = w
    · simp [e3]
    simp only [e1, e2, e3, false_or]
    have hc := hmem u hu v hv w hw e1 e2 e3
    have hcl' : 576 * u + 24 * v + w < 13824 := by omega
    have hidx := List.idxOf_lt_length_of_mem hc
    rw [hrel.pos _ hcl', if_pos hc, hsz, hus _ hidx, hvs _ hidx, hws _ hidx, getD_idxOfT hc]
    refine ⟨⟨⟨hidx, ?_⟩, ?_⟩, ?_⟩ <;> omega

@[expose] def bitK (S k : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight S k) 1) 1

theorem bitK_eq (S k : Nat) : bitK S k = S.testBit k := by
  unfold bitK
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have e1 : Nat.land (Nat.shiftRight S k) 1 = S / 2 ^ k % 2 := by
    change (S >>> k) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [e1]
  rcases Nat.mod_two_eq_zero_or_one (S / 2 ^ k) with h | h <;> rw [h] <;> rfl

@[expose] noncomputable def orSel2 (c : Nat → Bool) (f g : Nat → Nat) (n acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k ih a => strictN (nIf(c k, Nat.lor a (Nat.lor (Nat.shiftLeft 1 (f k))
      (Nat.shiftLeft 1 (g k))), a)) ih) n acc

theorem strictN_eqT (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nIf_eqT (c : Bool) (t e : Nat) : nIf(c, t, e) = if c then t else e := by
  cases c <;> rfl

theorem testBit_one_shiftLeft (m y : Nat) : (Nat.shiftLeft 1 m).testBit y = decide (m = y) := by
  change (1 <<< m).testBit y = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem testBit_orSel2 (c : Nat → Bool) (f g : Nat → Nat) (n : Nat) :
    ∀ acc y, (orSel2 c f g n acc).testBit y = true ↔
      acc.testBit y = true ∨ ∃ k < n, c k = true ∧ (f k = y ∨ g k = y) := by
  induction n with
  | zero =>
    intro acc y
    simp [orSel2]
  | succ k ih =>
    intro acc y
    have e : orSel2 c f g (k + 1) acc = orSel2 c f g k (if c k then Nat.lor acc
        (Nat.lor (Nat.shiftLeft 1 (f k)) (Nat.shiftLeft 1 (g k))) else acc) := by
      change strictN _ _ = _
      rw [strictN_eqT, nIf_eqT]
      rfl
    rw [e, ih]
    constructor
    · rintro (h | ⟨k', hk', h⟩)
      · by_cases hc : c k = true
        · rw [if_pos hc] at h
          change (acc ||| (Nat.shiftLeft 1 (f k) ||| Nat.shiftLeft 1 (g k))).testBit y = true at h
          rw [Nat.testBit_or, Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft] at h
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with h | h
          · exact Or.inl h
          · exact Or.inr ⟨k, by omega, hc, h⟩
        · rw [if_neg hc] at h
          exact Or.inl h
      · exact Or.inr ⟨k', by omega, h⟩
    · rintro (h | ⟨k', hk', hc, h⟩)
      · left
        split
        · change (acc ||| _).testBit y = true
          rw [Nat.testBit_or, h, Bool.true_or]
        · exact h
      · by_cases e' : k' = k
        · subst e'
          left
          rw [if_pos hc]
          change (acc ||| (Nat.shiftLeft 1 (f k') ||| Nat.shiftLeft 1 (g k'))).testBit y = true
          rw [Nat.testBit_or, Nat.testBit_or, testBit_one_shiftLeft, testBit_one_shiftLeft]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr h
        · exact Or.inr ⟨k', by omega, hc, h⟩

@[expose] def pAK (i : Nat) : Nat := planeAList.getD i 0

@[expose] def pBK (i : Nat) : Nat := planeBList.getD i 0

@[expose] noncomputable def imgK (Fr : Nat) : Nat :=
  orSel2 (bitK Fr) (codeImg pAK) (codeImg pBK) 13824 0

@[expose] noncomputable def layersK (k R Fr : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun R _ => R)
    (fun _ ih R Fr => strictN (imgK Fr) (fun I => strictN (Nat.lor R I) (fun R' =>
      strictN (Nat.xor I (Nat.land I R)) (fun F' => ih R' F')))) k R Fr

@[expose] def distK (k : Nat) : Bool :=
  !(Nat.beq (k / 576) (k / 24 % 24)) && !(Nat.beq (k / 576) (k % 24)) &&
    !(Nat.beq (k / 24 % 24) (k % 24))

@[expose] noncomputable def tgtK : Nat := orSel2 distK (fun k => k) (fun k => k) 13824 0

set_option maxRecDepth 100000 in
theorem tripReach_eq :
    Nat.land tgtK (layersK 37 (Nat.shiftLeft 1 26) (Nat.shiftLeft 1 26)) = tgtK := by
  decide +kernel

theorem layersK_sound (P : Nat → Prop)
    (hcl : ∀ x, P x → P (codeImg pAK x) ∧ P (codeImg pBK x)) :
    ∀ k R Fr, (∀ y, R.testBit y = true → P y) → (∀ y, Fr.testBit y = true → P y) →
      ∀ y, (layersK k R Fr).testBit y = true → P y := by
  intro k
  induction k with
  | zero => intro R Fr hR _ y hy; exact hR y hy
  | succ k ih =>
    intro R Fr hR hF y hy
    have e0 : layersK (k + 1) R Fr = strictN (imgK Fr) (fun I => strictN (Nat.lor R I)
        (fun R' => strictN (Nat.xor I (Nat.land I R)) (fun F' => layersK k R' F'))) := rfl
    have e : layersK (k + 1) R Fr = layersK k (Nat.lor R (imgK Fr))
        (Nat.xor (imgK Fr) (Nat.land (imgK Fr) R)) := by
      rw [e0, strictN_eqT, strictN_eqT, strictN_eqT]
    rw [e] at hy
    have hI : ∀ z, (imgK Fr).testBit z = true → P z := by
      intro z hz
      unfold imgK at hz
      rw [testBit_orSel2] at hz
      rcases hz with hz | ⟨j, -, hj, hz⟩
      · simp at hz
      · rw [bitK_eq] at hj
        have := hcl j (hF j hj)
        rcases hz with hz | hz
        · rw [← hz]; exact this.1
        · rw [← hz]; exact this.2
    refine ih _ _ ?_ ?_ y hy
    · intro z hz
      change (R ||| imgK Fr).testBit z = true at hz
      rw [Nat.testBit_or, Bool.or_eq_true] at hz
      rcases hz with hz | hz
      · exact hR z hz
      · exact hI z hz
    · intro z hz
      change (imgK Fr ^^^ (imgK Fr &&& R)).testBit z = true at hz
      rw [Nat.testBit_xor, Nat.testBit_and] at hz
      apply hI z
      cases h : (imgK Fr).testBit z
      · rw [h] at hz; simp at hz
      · rfl

theorem pAK_eq : ∀ i : Fin 24, planeAArr[i.val]! = pAK i.val := by decide

theorem pBK_eq : ∀ i : Fin 24, planeBArr[i.val]! = pBK i.val := by decide

theorem codeImg_congr {p q : Nat → Nat} (h : ∀ i < 24, p i = q i) {c : Nat} (hc : c < 13824) :
    codeImg p c = codeImg q c := by
  unfold codeImg
  rw [h _ (by omega), h _ (Nat.mod_lt _ (by decide)), h _ (Nat.mod_lt _ (by decide))]

theorem tripReach_sound (P : Nat → Prop) (h26 : P 26)
    (hcl : ∀ x, P x → P (tripF planeAArr planeBArr 0 x) ∧ P (tripF planeAArr planeBArr 1 x)) :
    ∀ u < 24, ∀ v < 24, ∀ w < 24, u ≠ v → u ≠ w → v ≠ w → P (576 * u + 24 * v + w) := by
  let Q : Nat → Prop := fun x => x < 13824 ∧ P x
  have hA : ∀ x < 13824, tripF planeAArr planeBArr 0 x = codeImg pAK x := fun x hx => by
    unfold tripF
    rw [if_pos rfl]
    exact codeImg_congr (fun i hi => pAK_eq ⟨i, hi⟩) hx
  have hB : ∀ x < 13824, tripF planeAArr planeBArr 1 x = codeImg pBK x := fun x hx => by
    unfold tripF
    rw [if_neg (by decide)]
    exact codeImg_congr (fun i hi => pBK_eq ⟨i, hi⟩) hx
  have hpa : ∀ i < 24, planeAArr[i]! < 24 := fun i hi => by
    have : ∀ i : Fin 24, planeAArr[i.val]! < 24 := by decide
    exact this ⟨i, hi⟩
  have hpb : ∀ i < 24, planeBArr[i]! < 24 := fun i hi => by
    have : ∀ i : Fin 24, planeBArr[i.val]! < 24 := by decide
    exact this ⟨i, hi⟩
  have hclQ : ∀ x, Q x → Q (codeImg pAK x) ∧ Q (codeImg pBK x) := by
    rintro x ⟨hx, hPx⟩
    have h := hcl x hPx
    rw [hA x hx, hB x hx] at h
    refine ⟨⟨?_, h.1⟩, ⟨?_, h.2⟩⟩
    · rw [← hA x hx]; exact tripF_lt hpa hpb 0 hx
    · rw [← hB x hx]; exact tripF_lt hpa hpb 1 hx
  have h1 : ∀ y, (Nat.shiftLeft 1 26).testBit y = true → Q y := by
    intro y hy
    rw [testBit_one_shiftLeft, decide_eq_true_eq] at hy
    subst hy
    exact ⟨by decide, h26⟩
  have hreach := layersK_sound Q hclQ 37 _ _ h1 h1
  intro u hu v hv w hw e1 e2 e3
  have hc : 576 * u + 24 * v + w < 13824 := by omega
  have ht : tgtK.testBit (576 * u + 24 * v + w) = true := by
    unfold tgtK
    rw [testBit_orSel2]
    refine Or.inr ⟨576 * u + 24 * v + w, hc, ?_, Or.inl rfl⟩
    unfold distK
    have d1 : (576 * u + 24 * v + w) / 576 = u := by omega
    have d2 : (576 * u + 24 * v + w) / 24 % 24 = v := by omega
    have d3 : (576 * u + 24 * v + w) % 24 = w := by omega
    rw [d1, d2, d3]
    simp only [Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨⟨Bool.eq_false_iff.2 fun h => e1 (Nat.eq_of_beq_eq_true h),
      Bool.eq_false_iff.2 fun h => e2 (Nat.eq_of_beq_eq_true h)⟩,
      Bool.eq_false_iff.2 fun h => e3 (Nat.eq_of_beq_eq_true h)⟩
  have e := tripReach_eq
  generalize layersK 37 (Nat.shiftLeft 1 26) (Nat.shiftLeft 1 26) = L at e hreach
  generalize tgtK = T at e ht
  have h2 : (Nat.land T L).testBit (576 * u + 24 * v + w) = T.testBit (576 * u + 24 * v + w) := by
    rw [e]
  have hl : Nat.land T L = T &&& L := rfl
  rw [hl, Nat.testBit_and, ht, Bool.true_and] at h2
  exact (hreach _ h2).2

theorem tripleCheck_eq_true : tripleCheck () = true := by
  unfold tripleCheck tripleTree
  refine tripleOK_tripleBFS (by decide) (by decide) ?_ ?_ ?_
  · intro i hi
    have : ∀ i : Fin 24, planeAArr[i.val]! < 24 := by decide
    exact this ⟨i, hi⟩
  · intro i hi
    have : ∀ i : Fin 24, planeBArr[i.val]! < 24 := by decide
    exact this ⟨i, hi⟩
  · intro P h26 hcl
    exact tripReach_sound P h26 hcl

end CFSG.KS.RouteP

end
