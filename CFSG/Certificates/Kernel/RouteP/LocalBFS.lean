module

public import CFSG.Certificates.Kernel.Spor.PK.BFS
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.RouteP.Bridge
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.KS.RouteP

open CFSG.Sporadic.Th.Native CFSG.KS.PK
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

abbrev LS := Table × Table × Table

@[expose] def bodyL (g1 g2 : Table) (h : Nat) (b : LS) : LS :=
  if (b.1[ap g1 b.2.1[h]!.toNat]! == none32) = true then
    if ((Array.set! b.1 (ap g1 b.2.1[h]!.toNat) (UInt32.ofNat (Array.size b.2.1)))[
        ap g2 b.2.1[h]!.toNat]! == none32) = true then
      ((Array.set! b.1 (ap g1 b.2.1[h]!.toNat) (UInt32.ofNat (Array.size b.2.1))).set!
          (ap g2 b.2.1[h]!.toNat)
          (UInt32.ofNat (Array.push b.2.1 (UInt32.ofNat (ap g1 b.2.1[h]!.toNat))).size),
        (Array.push b.2.1 (UInt32.ofNat (ap g1 b.2.1[h]!.toNat))).push
          (UInt32.ofNat (ap g2 b.2.1[h]!.toNat)),
        (Array.push b.2.2 (UInt32.ofNat (h ||| 1 <<< 30))).push (UInt32.ofNat (h ||| 2 <<< 30)))
    else
      (Array.set! b.1 (ap g1 b.2.1[h]!.toNat) (UInt32.ofNat (Array.size b.2.1)),
        Array.push b.2.1 (UInt32.ofNat (ap g1 b.2.1[h]!.toNat)),
        Array.push b.2.2 (UInt32.ofNat (h ||| 1 <<< 30)))
  else
    if (b.1[ap g2 b.2.1[h]!.toNat]! == none32) = true then
      (Array.set! b.1 (ap g2 b.2.1[h]!.toNat) (UInt32.ofNat (Array.size b.2.1)),
        Array.push b.2.1 (UInt32.ofNat (ap g2 b.2.1[h]!.toNat)),
        Array.push b.2.2 (UInt32.ofNat (h ||| 2 <<< 30)))
    else b

@[expose] def letterL (g : Table) (c h p : Nat) (b : LS) : LS :=
  if (b.1[ap g p]! == none32) = true then
    (b.1.set! (ap g p) (UInt32.ofNat b.2.1.size), b.2.1.push (UInt32.ofNat (ap g p)),
      b.2.2.push (UInt32.ofNat (h ||| c)))
  else b

theorem bodyL_eq (g1 g2 : Table) (h : Nat) (b : LS) :
    bodyL g1 g2 h b = letterL g2 (2 <<< 30) h (ap b.2.1 h) (letterL g1 (1 <<< 30) h (ap b.2.1 h) b) := by
  unfold bodyL letterL ap
  by_cases c1 : (b.1[(g1[(b.2.1[h]!).toNat]!).toNat]! == none32) = true
  · simp only [if_pos c1]
  · simp only [if_neg c1]

@[expose] def initL (n root : Nat) : LS :=
  ((Array.replicate n none32).set! root 0, #[UInt32.ofNat root], #[0])

@[expose] def stepL (g1 g2 : Table) (b : LS) (h : Nat) : LS :=
  if h < b.2.1.size then bodyL g1 g2 h b else b

theorem foldl_fixedL {β : Type} (g : β → Nat → β) (b : β) :
    ∀ l : List Nat, (∀ h ∈ l, g b h = b) → l.foldl g b = b
  | [], _ => rfl
  | h :: l, H => by
    rw [List.foldl_cons, H h (List.mem_cons_self ..)]
    exact foldl_fixedL g b l fun h' hh' => H h' (List.mem_cons_of_mem _ hh')

theorem forIn_range'_breakL {β : Type} (f : Nat → β → β) (c : Nat → β → Prop)
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
      exact forIn_range'_breakL f c hmono k (s + 1) (f s b)
    · simp only [hc, if_false, pure_bind]
      refine (foldl_fixedL _ b _ fun h hh => ?_).symm
      rw [List.mem_range'_1] at hh
      exact if_neg (hmono s h b (by omega) hc)

theorem ite_pure_yieldL {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b)) =
      pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

@[expose] def finalL (b : LS) : Table × Table × Table := (b.2.1, b.2.2, b.1)

theorem localBFS_eq_foldl (n root : Nat) (g1 g2 : Table) :
    localBFS n root g1 g2 = finalL ((List.range n).foldl (stepL g1 g2) (initL n root)) := by
  unfold localBFS
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ite_pure_yieldL, List.forIn_pure_yield_eq_foldl, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, pure_bind, bind_pure, Prod.eta]
  rw [List.range_eq_range']
  exact congrArg finalL (forIn_range'_breakL (β := LS) (fun h b => bodyL g1 g2 h b)
    (fun h b => h < b.2.1.size) (fun h h' b hh hc hc' => hc (by omega)) n 0 (initL n root))

@[expose] def lF (g1 g2 : Table) (l x : Nat) : Nat := if l = 1 then ap g1 x else ap g2 x

@[expose] def packPL (h l : Nat) : UInt32 := UInt32.ofNat (h ||| (l <<< 30))

theorem toNat_ofNat_ltL {k : Nat} (hk : k < 2 ^ 32) : (UInt32.ofNat k).toNat = k := by
  rw [UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt hk

theorem ofNat_ne_none32L {k : Nat} (hk : k + 1 < 2 ^ 32) : UInt32.ofNat k ≠ none32 () := by
  intro h
  have h1 := congrArg UInt32.toNat h
  rw [toNat_ofNat_ltL (by omega)] at h1
  have h2 : (none32 ()).toNat = 4294967295 := rfl
  rw [h2] at h1
  omega

theorem pack_eq {h l : Nat} (hh : h < 2 ^ 30) : h ||| (l <<< 30) = l * 2 ^ 30 + h := by
  rw [Nat.or_comm,← Nat.shiftLeft_add_eq_or_of_lt hh, Nat.shiftLeft_eq]

structure RelL (n : Nat) (s : BS) (b : LS) : Prop where
  size : b.1.size = n
  pts : b.2.1 = (s.pts.map UInt32.ofNat).toArray
  pl : b.2.2 = (List.zipWith packPL s.par s.lab).toArray
  len : s.par.length = s.lab.length
  pos : ∀ x < n, b.1[x]! = if x ∈ s.pts then UInt32.ofNat (s.pts.idxOf x) else none32 ()
  nodup : s.pts.Nodup
  lt : ∀ p ∈ s.pts, p < n

theorem length_le_of_nodupL {n : Nat} {l : List Nat} (hl : l.Nodup) (h : ∀ p ∈ l, p < n) :
    l.length ≤ n := by
  have := hl.length_le_of_subset (l₂ := List.range n) fun p hp => List.mem_range.2 (h p hp)
  simpa using this

theorem letterL_rel {n : Nat} (hn : n < 2 ^ 32) {g : Table} {F : Nat → Nat → Nat} {l : Nat}
    {s : BS} {b : LS} (hs : RelL n s b) {h p : Nat} (hg : ap g p = F l p) (hq : F l p < n) :
    RelL n (BS.letter F h p s l) (letterL g (l <<< 30) h p b) := by
  have hlen : s.pts.length ≤ n := length_le_of_nodupL hs.nodup hs.lt
  have hv := hs.pos _ hq
  unfold BS.letter letterL
  rw [hg]
  by_cases hmem : F l p ∈ s.pts
  · have hne : b.1[F l p]! ≠ none32 () := by
      rw [hv, if_pos hmem]
      exact ofNat_ne_none32L (by have := List.idxOf_lt_length_of_mem hmem; omega)
    rw [if_pos hmem, if_neg (by simpa using hne)]
    exact hs
  · rw [if_neg hmem, hv, if_neg hmem, if_pos (by simp)]
    have hsz : b.2.1.size = s.pts.length := by rw [hs.pts]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Array.size_set!]
      exact hs.size
    · change b.2.1.push (UInt32.ofNat (F l p)) = _
      rw [hs.pts, List.push_toArray, List.map_append]
      rfl
    · change b.2.2.push (UInt32.ofNat (h ||| l <<< 30)) = _
      rw [hs.pl, List.push_toArray, List.zipWith_append hs.len]
      rfl
    · simp [hs.len]
    · intro x hx
      by_cases e : x = F l p
      · subst e
        rw [Array.getElem!_set!_self _ _ _ (by rw [hs.size]; exact hq), hsz, if_pos (by simp),
          List.idxOf_append, if_neg hmem]
        simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), hs.pos x hx]
        by_cases hx' : x ∈ s.pts
        · rw [if_pos hx', if_pos (List.mem_append_left _ hx'), List.idxOf_append, if_pos hx']
        · rw [if_neg hx', if_neg]
          simp [hx', e]
    · rw [List.nodup_append]
      refine ⟨hs.nodup, by simp, ?_⟩
      intro a ha b' hb
      rw [List.mem_singleton] at hb
      rintro rfl
      exact hmem (hb ▸ ha)
    · intro q hq'
      rcases List.mem_append.1 hq' with hq' | hq'
      · exact hs.lt q hq'
      · rw [List.mem_singleton] at hq'
        exact hq' ▸ hq

theorem getD_memL {l : List Nat} {i : Nat} (h : i < l.length) : l.getD i 0 ∈ l := by
  simp [List.getD_eq_getElem?_getD, h]

theorem ap_mapOfNatL {n : Nat} (hn : n < 2 ^ 32) {l : List Nat} (hl : ∀ p ∈ l, p < n)
    {h : Nat} (hh : h < l.length) : ap ((l.map UInt32.ofNat).toArray) h = l.getD h 0 := by
  unfold ap
  rw [getElem!_pos _ h (by simpa using hh)]
  simp only [List.getElem_toArray, List.getElem_map]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh, Option.getD_some,
    toNat_ofNat_ltL (Nat.lt_trans (hl _ (List.getElem_mem hh)) hn)]

theorem stepL_rel {n : Nat} (hn : n < 2 ^ 32) {g1 g2 : Table}
    (h1 : ∀ x < n, ap g1 x < n) (h2 : ∀ x < n, ap g2 x < n) {s : BS} {b : LS}
    (hs : RelL n s b) (h : Nat) :
    RelL n (BS.step (lF g1 g2) [1, 2] s h) (stepL g1 g2 b h) := by
  unfold BS.step stepL
  have hsz : b.2.1.size = s.pts.length := by rw [hs.pts]; simp
  by_cases hh : h < s.pts.length
  · rw [if_pos hh, if_pos (hsz ▸ hh), bodyL_eq]
    have hap : ap b.2.1 h = s.pts.getD h 0 := by
      rw [hs.pts]
      exact ap_mapOfNatL hn hs.lt hh
    rw [hap]
    have hp := hs.lt _ (getD_memL hh)
    simp only [List.foldl_cons, List.foldl_nil]
    have e1 : ap g1 (s.pts.getD h 0) = lF g1 g2 1 (s.pts.getD h 0) := by simp [lF]
    have e2 : ap g2 (s.pts.getD h 0) = lF g1 g2 2 (s.pts.getD h 0) := by simp [lF]
    have r1 := letterL_rel (l := 1) (h := h) hn hs e1 (by rw [← e1]; exact h1 _ hp)
    exact letterL_rel (l := 2) (h := h) hn r1 e2 (by rw [← e2]; exact h2 _ hp)
  · rw [if_neg hh, if_neg (by omega)]
    exact hs

theorem initL_rel {n root : Nat} (hr : root < n) : RelL n ⟨[root], [0], [0]⟩ (initL n root) := by
  refine ⟨?_, rfl, rfl, rfl, ?_, by simp, ?_⟩
  · simp [initL]
  · intro x hx
    simp only [initL]
    by_cases e : x = root
    · subst e
      rw [Array.getElem!_set!_self _ _ _ (by simp [hr])]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm e), getElem!_pos _ _ (by simpa using hx),
        Array.getElem_replicate]
      simp [e]
  · intro p hp
    simp only [List.mem_singleton] at hp
    omega

theorem runL_rel {n root : Nat} (hn : n < 2 ^ 32) (hr : root < n) {g1 g2 : Table}
    (h1 : ∀ x < n, ap g1 x < n) (h2 : ∀ x < n, ap g2 x < n) (k : Nat) :
    RelL n ((List.range k).foldl (BS.step (lF g1 g2) [1, 2]) ⟨[root], [0], [0]⟩)
      ((List.range k).foldl (stepL g1 g2) (initL n root)) := by
  induction k with
  | zero => exact initL_rel hr
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    exact stepL_rel hn h1 h2 ih k

theorem getD_idxOfL {l : List Nat} {q : Nat} (hq : q ∈ l) : l.getD (l.idxOf q) 0 = q := by
  simp [List.getD_eq_getElem?_getD, List.idxOf_lt_length_of_mem hq]

theorem idxOf_getDL {l : List Nat} (hnd : l.Nodup) {k : Nat} (hk : k < l.length) :
    l.idxOf (l.getD k 0) = k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.Nodup.idxOf_getElem hnd k hk

private theorem treePar_eq (x : Nat) : treePar x = x &&& 0x3FFFFFFF := rfl

private theorem treeLab_eq (x : Nat) : treeLab x = x >>> 30 := rfl

theorem treeCheck_of {n : Nat} (hn : n < 2 ^ 30) (h0 : 0 < n) {g1 g2 : Table}
    (h1 : ∀ x < n, ap g1 x < n) (h2 : ∀ x < n, ap g2 x < n)
    (hall : ∀ P : Nat → Prop, P 0 → (∀ x, P x → P (ap g1 x) ∧ P (ap g2 x)) → ∀ x < n, P x) :
    treeCheck n g1 g2 = true := by
  have hn32 : n < 2 ^ 32 := Nat.lt_trans hn (by decide)
  have hF : ∀ l ∈ [1, 2], ∀ x < n, lF g1 g2 l x < n := by
    intro l _ x hx
    unfold lF
    split
    · exact h1 x hx
    · exact h2 x hx
  have hok := run_ok hF h0
  have hcl := run_closed hF h0
  have hrel := runL_rel hn32 h0 h1 h2 n
  unfold BS.run at hok hcl
  unfold treeCheck
  rw [localBFS_eq_foldl]
  unfold finalL
  simp only
  generalize (List.range n).foldl (BS.step (lF g1 g2) [1, 2]) ⟨[0], [0], [0]⟩ = s at hok hcl hrel
  generalize (List.range n).foldl (stepL g1 g2) (initL n 0) = b at hrel ⊢
  have hmem : ∀ x < n, x ∈ s.pts := by
    refine hall (· ∈ s.pts) ?_ ?_
    · rw [← hok.root]
      exact getD_memL hok.pos
    · intro x hx
      exact ⟨by simpa [lF] using hcl x hx 1 (by simp), by simpa [lF] using hcl x hx 2 (by simp)⟩
  have hlen : s.pts.length = n := by
    refine Nat.le_antisymm hok.le ?_
    have := (List.nodup_range (n := n)).length_le_of_subset
      (l₂ := s.pts) fun x hx => hmem x (List.mem_range.1 hx)
    simpa using this
  have hptsz : b.2.1.size = n := by rw [hrel.pts]; simp [hlen]
  have hpts : ∀ k < n, ap b.2.1 k = s.pts.getD k 0 := fun k hk => by
    rw [hrel.pts]
    exact ap_mapOfNatL hn32 hok.lt (by omega)
  have hpos : ∀ x < n, ap b.1 x = s.pts.idxOf x := fun x hx => by
    unfold ap
    rw [hrel.pos x hx, if_pos (hmem x hx), toNat_ofNat_ltL]
    have := List.idxOf_lt_length_of_mem (hmem x hx)
    omega
  have hpl : ∀ k < n, ((b.2.2)[k]!).toNat = s.par.getD k 0 ||| (s.lab.getD k 0 <<< 30) := by
    intro k hk
    rw [hrel.pl, getElem!_pos _ k (by simp [hok.len_par, hok.len_lab, hlen, hk])]
    simp only [List.getElem_toArray, List.getElem_zipWith, packPL]
    rw [toNat_ofNat_ltL]
    · simp [List.getD_eq_getElem?_getD, hok.len_par, hok.len_lab, hlen, hk]
    · by_cases hk0 : k = 0
      · subst hk0
        have e1 := hok.par0
        have e2 := hok.lab0
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
          (by rw [hok.len_par, hlen]; exact hk : 0 < s.par.length),
          List.getElem?_eq_getElem (by rw [hok.len_lab, hlen]; exact hk : 0 < s.lab.length),
          Option.getD_some] at e1 e2
        rw [e1, e2]
        decide
      · have hpar := hok.par_lt k (by omega) (by omega)
        have hlab := hok.lab_mem k (by omega) (by omega)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
          (by rw [hok.len_par, hlen]; exact hk : k < s.par.length),
          List.getElem?_eq_getElem (by rw [hok.len_lab, hlen]; exact hk : k < s.lab.length),
          Option.getD_some] at hpar hlab
        rw [pack_eq (by omega)]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hlab
        rcases hlab with e | e <;> rw [e] <;> omega
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hptsz, ?_⟩
  unfold CFSG.Sporadic.Th.Native.treeOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨h0, by rw [hpts 0 h0, hok.root]⟩, ?_⟩
  rw [CFSG.Sporadic.Th.allIn_eq_true]
  intro k _ hk
  have hkl : k < s.pts.length := by omega
  have hkmem := getD_memL hkl
  have hkn := hok.lt _ hkmem
  unfold treeCheckAt
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true]
  rw [hpts k hk]
  have ha := h1 _ hkn
  have hb := h2 _ hkn
  refine ⟨⟨⟨⟨⟨⟨hkn, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hpos _ hkn, idxOf_getDL hok.nodup hkl]
  · rw [hpos _ ha, ← hlen]; exact List.idxOf_lt_length_of_mem (hmem _ ha)
  · rw [hpos _ ha, hpts _ (by rw [← hlen]; exact List.idxOf_lt_length_of_mem (hmem _ ha)),
      getD_idxOfL (hmem _ ha)]
  · rw [hpos _ hb, ← hlen]; exact List.idxOf_lt_length_of_mem (hmem _ hb)
  · rw [hpos _ hb, hpts _ (by rw [← hlen]; exact List.idxOf_lt_length_of_mem (hmem _ hb)),
      getD_idxOfL (hmem _ hb)]
  · by_cases hk0 : k = 0
    · exact Or.inl hk0
    · right
      have hpar := hok.par_lt k (by omega) hkl
      have hlab := hok.lab_mem k (by omega) hkl
      have hedge := hok.edge k (by omega) hkl
      rw [hpl k hk, pack_eq (by omega)]
      have ep : treePar (s.lab.getD k 0 * 2 ^ 30 + s.par.getD k 0) = s.par.getD k 0 := by
        rw [treePar_eq, show (0x3FFFFFFF : Nat) = 2 ^ 30 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]
        omega
      have el : treeLab (s.lab.getD k 0 * 2 ^ 30 + s.par.getD k 0) = s.lab.getD k 0 := by
        rw [treeLab_eq, Nat.shiftRight_eq_div_pow]
        omega
      rw [ep, el, hpts _ (by omega)]
      refine ⟨hpar, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlab
      rcases hlab with e | e
      · left
        rw [e] at hedge ⊢
        exact ⟨rfl, by simpa [lF] using hedge⟩
      · right
        rw [e] at hedge ⊢
        exact ⟨rfl, by simpa [lF] using hedge⟩

end CFSG.KS.RouteP

end
