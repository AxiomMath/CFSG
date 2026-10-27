module

public import CFSG.Certificates.Kernel.VecKTrees
public import CFSG.Certificates.Kernel.Fi23Tr.Bits
import CFSG.Certificates.Kernel.Fi22LH.Loops
import CFSG.Certificates.Kernel.Fi22LH.TreeSpec
import CFSG.Certificates.Kernel.Fi23Tr.TrBFS
import Mathlib.Data.Finset.Card

public section

namespace CFSG.KS.Fi23Tr

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.KS.Fi22LH

theorem inTreeB_of_reach {n root : Nat} {letters : Array Table} {lv : Array Nat} (hn : n < 2 ^ 32)
    (hr : root < n) (hlv : ∀ l ∈ lv, l < 2 ^ 32) (hL : ∀ l ∈ lv, ∀ x < n, ap letters[l]! x < n)
    {p : Nat} (hp : CFSG.KC.VecK.Reach (· ∈ lv) (fun l x => ap letters[l]! x) root p) :
    inTreeB (treeBFS n root letters lv) p = true := by
  have H := (CFSG.KC.VecK.treeBFS_spec hn hr hlv hL).facts
  obtain ⟨t, ht, e⟩ := (H.reach_iff p).1 hp
  have hpos := H.ix_pt t ht
  rw [e] at hpos
  unfold inTreeB
  rw [hpos, e]
  simp [ht]

theorem domWit_spec {O : WOrbit} {D bi : Table} {C : Array Nat} {f : Nat}
    (h : ∃ x ∈ C, tauAct O D bi x f = f) :
    domWit O D bi C f ∈ C ∧ tauAct O D bi (domWit O D bi C f) f = f := by
  unfold domWit
  cases hc : C.find? (fun x => tauAct O D bi x f == f) with
  | none =>
    obtain ⟨x, hx, e⟩ := h
    have := Array.find?_eq_none.1 hc x hx
    rw [e, beq_self_eq_true] at this
    exact absurd rfl this
  | some a =>
    rw [Option.getD_some]
    have h2 := Array.find?_some (p := fun x => tauAct O D bi x f == f) hc
    exact ⟨Array.mem_of_find?_eq_some hc, beq_iff_eq.1 h2⟩

theorem ncWit_spec {O : WOrbit} {D bi : Table} {C : Array Nat} {f : Nat}
    (h : ∃ x ∈ C, tauAct O D bi x f ≠ f) :
    ncWit O D bi C f ∈ C ∧ tauAct O D bi (ncWit O D bi C f) f ≠ f := by
  unfold ncWit
  cases hc : C.find? (fun x => tauAct O D bi x f != f) with
  | none =>
    obtain ⟨x, hx, e⟩ := h
    have := Array.find?_eq_none.1 hc x hx
    rw [bne_iff_ne] at this
    exact absurd e this
  | some a =>
    rw [Option.getD_some]
    have h2 := Array.find?_some (p := fun x => tauAct O D bi x f != f) hc
    exact ⟨Array.mem_of_find?_eq_some hc, bne_iff_ne.1 h2⟩

theorem find_range_spec {n : Nat} {p : Nat → Bool} (h : ∃ m < n, p m = true) :
    ((List.range n).find? p).getD 0 < n ∧ p (((List.range n).find? p).getD 0) = true := by
  cases hc : (List.range n).find? p with
  | none =>
    obtain ⟨m, hm, e⟩ := h
    have := List.find?_eq_none.1 hc m (List.mem_range.2 hm)
    exact absurd e this
  | some a =>
    rw [Option.getD_some]
    exact ⟨List.mem_range.1 (List.mem_of_find?_eq_some hc), List.find?_some hc⟩

abbrev CSt := Array Nat × Array Nat × PBits

@[expose] def cStep (O : WOrbit) (D bi : Table) (x h y : Nat) (s : CSt) : CSt :=
  if (!pBit s.2.2 y && tauAct O D bi x y == y) = true then (s.1.push y, s.2.1.push h, pSet s.2.2 y)
  else s

@[expose] def cBody (O : WOrbit) (D bi : Table) (S : Array Nat) (h : Nat) (s : CSt) :
    Id (ForInStep CSt) :=
  if h < s.1.size then
    let x := s.1[h]!
    pure (.yield (S.toList.foldl (fun t y => cStep O D bi x h y t) s))
  else pure (.done s)

theorem commTreeP_eq (O : WOrbit) (D bi : Table) (z : PBits) (S : Array Nat) :
    commTreeP O D bi z S = (fun s : CSt => (s.1, s.2.1))
      (forIn (m := Id) [0:S.size] ((#[S[0]!], #[0], pSet z S[0]!) : CSt) (cBody O D bi S)) := by
  unfold commTreeP
  simp only [Id.run]
  refine (congrArg (fun F => (forIn (m := Id) [0:S.size] ((#[S[0]!], #[0], pSet z S[0]!) : CSt) F >>=
    fun (s : CSt) => (pure (s.1, s.2.1) : Id (Array Nat × Array Nat)))) (funext fun h => funext fun s => ?_)).trans rfl
  unfold cBody
  by_cases hh : h < s.1.size
  · simp only [hh, if_true]
    rw [← Array.forIn_toList, forIn_yield _ (fun y t => cStep O D bi s.1[h]! h y t) (fun y t => by
      unfold cStep
      split <;> rfl)]
    rfl
  · simp only [hh, if_false]

structure CInvT (O : WOrbit) (D bi : Table) (S : Array Nat) (Dn : Nat → Nat → Prop) (s : CSt) :
    Prop where
  pos : 0 < s.1.size
  root : s.1[0]! = S[0]!
  par_size : s.2.1.size = s.1.size
  seen_size : s.2.2.size = 3959
  mem : ∀ k < s.1.size, s.1[k]! ∈ S
  seen : ∀ y, pBit s.2.2 y = true ↔ ∃ k < s.1.size, s.1[k]! = y
  inj : ∀ i < s.1.size, ∀ j < s.1.size, s.1[i]! = s.1[j]! → i = j
  par : ∀ k, 0 < k → k < s.1.size → s.2.1[k]! < k ∧ tauAct O D bi s.1[s.2.1[k]!]! s.1[k]! = s.1[k]!
  clos : ∀ k < s.1.size, ∀ y ∈ S, Dn k y → tauAct O D bi s.1[k]! y = y →
    ∃ j < s.1.size, s.1[j]! = y

theorem CInvT.mono {O : WOrbit} {D bi : Table} {S : Array Nat} {Dn Dn' : Nat → Nat → Prop} {s : CSt}
    (H : CInvT O D bi S Dn s) (h : ∀ k y, y ∈ S → Dn' k y → Dn k y) : CInvT O D bi S Dn' s :=
  { H with clos := fun k hk y hy hd => H.clos k hk y hy (h k y hy hd) }

theorem cStep_inv {O : WOrbit} {D bi : Table} {S : Array Nat} {Dn : Nat → Nat → Prop} {s : CSt}
    (hS : ∀ y ∈ S, y < 31671) (H : CInvT O D bi S Dn s) {h y : Nat} (hh : h < s.1.size)
    (hy : y ∈ S) (hD : ∀ k y', Dn k y' → k < s.1.size) :
    CInvT O D bi S (fun k y' => Dn k y' ∨ (k = h ∧ y' = y)) (cStep O D bi s.1[h]! h y s) ∧
      s.1.size ≤ (cStep O D bi s.1[h]! h y s).1.size ∧
      ∀ k < s.1.size, (cStep O D bi s.1[h]! h y s).1[k]! = s.1[k]! := by
  obtain ⟨ord, par, seen⟩ := s
  dsimp only at hh hD ⊢
  have Hc := H
  obtain ⟨Hpos, Hroot, Hps, Hss, Hmem, Hseen, Hinj, Hpar, Hclos⟩ := Hc
  dsimp only at Hpos Hroot Hps Hss Hmem Hseen Hinj Hpar Hclos
  have hy31 := hS y hy
  unfold cStep
  dsimp only
  by_cases hc : (!pBit seen y && tauAct O D bi ord[h]! y == y) = true
  · rw [if_pos hc]
    dsimp only
    rw [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    obtain ⟨hns, hcomm⟩ := hc
    have hnew : ∀ k < ord.size, ord[k]! ≠ y := by
      intro k hk e
      have := (Hseen y).2 ⟨k, hk, e⟩
      rw [hns] at this
      exact absurd this (by simp)
    have hpush : ∀ k < ord.size + 1, (ord.push y)[k]! = if k < ord.size then ord[k]! else y := by
      intro k hk
      by_cases hk' : k < ord.size
      · rw [if_pos hk', get!_push_lt _ _ hk']
      · rw [if_neg hk', get!_push_of (by omega)]
    have hss : seen.size = 3959 := Hss
    refine ⟨⟨by simp, by rw [get!_push_lt _ _ Hpos]; exact Hroot, by simp [Hps],
      by rw [size_pSet]; exact hss, fun k hk => ?_, fun y' => ?_, fun i hi j hj e => ?_,
      fun k hk0 hk => ?_, fun k hk y' hy' hd he => ?_⟩, by simp, fun k hk => get!_push_lt _ _ hk⟩
    · dsimp only at *
      rw [Array.size_push] at hk
      rw [hpush k hk]
      split
      · exact Hmem k (by assumption)
      · exact hy
    · dsimp only at *
      rw [pBit_pSet (by rw [hss]; omega), Bool.or_eq_true, Hseen y', beq_iff_eq, Array.size_push]
      constructor
      · rintro (⟨k, hk, e⟩ | e)
        · exact ⟨k, by omega, by rw [get!_push_lt _ _ hk]; exact e⟩
        · exact ⟨ord.size, by omega, by rw [get!_push_eq, e]⟩
      · rintro ⟨k, hk, e⟩
        rw [hpush k hk] at e
        split at e
        · exact Or.inl ⟨k, by assumption, e⟩
        · exact Or.inr e.symm
    · dsimp only at *
      rw [Array.size_push] at hi hj
      rw [hpush i hi, hpush j hj] at e
      by_cases hi' : i < ord.size <;> by_cases hj' : j < ord.size
      · rw [if_pos hi', if_pos hj'] at e
        exact Hinj i hi' j hj' e
      · rw [if_pos hi', if_neg hj'] at e
        exact absurd e (hnew i hi')
      · rw [if_neg hi', if_pos hj'] at e
        exact absurd e.symm (hnew j hj')
      · omega
    · dsimp only at *
      rw [Array.size_push] at hk
      have hps : par.size = ord.size := Hps
      rcases Nat.lt_or_ge k ord.size with hk' | hk'
      · rw [get!_push_lt _ _ (by omega), get!_push_lt _ _ hk']
        obtain ⟨p1, p2⟩ := Hpar k hk0 hk'
        rw [get!_push_lt _ _ (by omega)]
        exact ⟨p1, p2⟩
      · have ek : k = ord.size := by omega
        subst ek
        rw [get!_push_of hps, get!_push_eq, get!_push_lt _ _ hh]
        exact ⟨hh, hcomm⟩
    · dsimp only at *
      rw [Array.size_push] at hk
      rcases hd with hd | ⟨hk1, hy1⟩
      · have hk' := hD k y' hd
        rw [get!_push_lt _ _ hk'] at he
        obtain ⟨j, hj, e⟩ := Hclos k hk' y' hy' hd he
        exact ⟨j, by rw [Array.size_push]; omega, by rw [get!_push_lt _ _ hj]; exact e⟩
      · subst hy1
        exact ⟨ord.size, by simp, get!_push_eq _ _⟩
  · rw [if_neg hc]
    refine ⟨{ H with clos := fun k hk y' hy' hd he => ?_ }, Nat.le_refl _, fun _ _ => rfl⟩
    rcases hd with hd | ⟨hk1, hy1⟩
    · exact Hclos k hk y' hy' hd he
    · subst hk1 hy1
      rw [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
      by_cases hs : pBit seen y' = true
      · obtain ⟨j, hj, e⟩ := (Hseen y').1 hs
        exact ⟨j, hj, e⟩
      · exact absurd ⟨by simpa using hs, he⟩ hc

theorem cFold_inv {O : WOrbit} {D bi : Table} {S : Array Nat} (hS : ∀ y ∈ S, y < 31671) {h : Nat}
    {s : CSt} (hh : h < s.1.size) :
    ∀ (l pre : List Nat) (t : CSt), (∀ y ∈ l, y ∈ S) →
      CInvT O D bi S (fun k y => k < h ∨ (k = h ∧ y ∈ pre)) t → s.1.size ≤ t.1.size →
      (∀ k < s.1.size, t.1[k]! = s.1[k]!) →
      CInvT O D bi S (fun k y => k < h ∨ (k = h ∧ y ∈ pre ++ l))
          (l.foldl (fun t y => cStep O D bi s.1[h]! h y t) t) ∧
        s.1.size ≤ (l.foldl (fun t y => cStep O D bi s.1[h]! h y t) t).1.size ∧
        ∀ k < s.1.size, (l.foldl (fun t y => cStep O D bi s.1[h]! h y t) t).1[k]! = s.1[k]!
  | [], pre, t, _, H, h1, h2 => by
    rw [List.append_nil]
    exact ⟨H, h1, h2⟩
  | y :: l, pre, t, hl, H, h1, h2 => by
    rw [List.foldl_cons]
    have ex : s.1[h]! = t.1[h]! := (h2 h hh).symm
    obtain ⟨H', g1, g2⟩ := cStep_inv hS H (h := h) (by omega) (hl y List.mem_cons_self)
      (fun k y' hd => by rcases hd with hd | ⟨hd, -⟩ <;> omega)
    rw [← ex] at H' g1 g2
    have := cFold_inv hS hh l (pre ++ [y]) _ (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (H'.mono fun k y' _ hd => by
        rcases hd with hd | ⟨hd1, hd2⟩
        · exact Or.inl (Or.inl hd)
        · rcases List.mem_append.1 hd2 with h3 | h3
          · exact Or.inl (Or.inr ⟨hd1, h3⟩)
          · exact Or.inr ⟨hd1, by simpa using h3⟩)
      (by omega) (fun k hk => by rw [g2 k (by omega), h2 k hk])
    rw [List.append_assoc, List.singleton_append] at this
    exact this

theorem le_of_inj' {m n : Nat} {f : Nat → Nat} (hf : ∀ k < m, f k < n)
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) : m ≤ n := by
  have h := Finset.card_le_card_of_injOn f (s := Finset.range m) (t := Finset.range n)
    (by
      intro a ha
      have ha' : a < m := by simpa using ha
      simpa using hf a ha')
    (by
      intro a ha b hb e
      exact hinj a (by simpa using ha) b (by simpa using hb) e)
  simpa using h

theorem size_le_of_mem {S ord : Array Nat} (hmem : ∀ k < ord.size, ord[k]! ∈ S)
    (hinj : ∀ i < ord.size, ∀ j < ord.size, ord[i]! = ord[j]! → i = j) : ord.size ≤ S.size := by
  refine le_of_inj' (f := fun k => S.toList.idxOf ord[k]!) (fun k hk => ?_) (fun i hi j hj e => ?_)
  · have := List.idxOf_lt_length_of_mem (Array.mem_toList_iff.2 (hmem k hk))
    simpa using this
  · apply hinj i hi j hj
    have hi' := List.idxOf_lt_length_of_mem (Array.mem_toList_iff.2 (hmem i hi))
    have hj' := List.idxOf_lt_length_of_mem (Array.mem_toList_iff.2 (hmem j hj))
    rw [← List.getElem_idxOf hi', ← List.getElem_idxOf hj']
    simp only [e]

theorem commTreeP_spec (O : WOrbit) (D bi : Table) {z : PBits} (hz : z.size = 3959)
    (hz0 : ∀ y, pBit z y = false) {S : Array Nat} (hS0 : 0 < S.size) (hS : ∀ y ∈ S, y < 31671) :
    let ct := commTreeP O D bi z S
    ct.2.size = ct.1.size ∧ 0 < ct.1.size ∧ ct.1[0]! = S[0]! ∧ (∀ k < ct.1.size, ct.1[k]! ∈ S) ∧
      (∀ i < ct.1.size, ∀ j < ct.1.size, ct.1[i]! = ct.1[j]! → i = j) ∧
      (∀ k, 0 < k → k < ct.1.size →
        ct.2[k]! < k ∧ tauAct O D bi ct.1[ct.2[k]!]! ct.1[k]! = ct.1[k]!) ∧
      ∀ k < ct.1.size, ∀ y ∈ S, tauAct O D bi ct.1[k]! y = y → ∃ j < ct.1.size, ct.1[j]! = y := by
  rw [commTreeP_eq]
  intro ct
  suffices H : CInvT O D bi S (fun k _ => k < (forIn (m := Id) [0:S.size]
      ((#[S[0]!], #[0], pSet z S[0]!) : CSt) (cBody O D bi S)).1.size)
      (forIn (m := Id) [0:S.size] ((#[S[0]!], #[0], pSet z S[0]!) : CSt) (cBody O D bi S)) by
    exact ⟨H.par_size, H.pos, H.root, H.mem, H.inj, H.par,
      fun k hk y hy he => H.clos k hk y hy hk he⟩
  have hS0' : S[0]! ∈ S := by
    rw [getElem!_pos S 0 hS0]
    exact Array.getElem_mem hS0
  refine range_loop (fun q (s : CSt) => CInvT O D bi S (fun k _ => k < q) s ∧ q ≤ s.1.size)
    (fun s => CInvT O D bi S (fun k _ => k < s.1.size) s) _ S.size _ ?_ ?_ ?_
  · rintro q s hq ⟨H, hqs⟩
    unfold cBody
    by_cases hlt : q < s.1.size
    · rw [if_pos hlt]
      have := cFold_inv (O := O) (D := D) (bi := bi) hS hlt S.toList [] s
        (fun y hy => Array.mem_toList_iff.1 hy)
        (H.mono fun k y _ hd => by
          rcases hd with hd | ⟨_, hd⟩
          · exact hd
          · exact absurd hd List.not_mem_nil)
        (Nat.le_refl _) (fun _ _ => rfl)
      obtain ⟨H1, H2, -⟩ := this
      refine ⟨H1.mono fun k y hy hd => ?_, by omega⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | hd
      · exact Or.inl hd
      · exact Or.inr ⟨hd, by simpa using hy⟩
    · rw [if_neg hlt]
      have e : q = s.1.size := by omega
      exact e ▸ H
  · rintro s ⟨H, hs⟩
    have := size_le_of_mem H.mem H.inj
    have e : s.1.size = S.size := by omega
    rw [e]
    exact H
  · have hss : (pSet z S[0]!).size = 3959 := by rw [size_pSet, hz]
    have hlt := hS _ hS0'
    refine ⟨⟨by simp, rfl, rfl, hss, fun k hk => ?_, fun y => ?_, fun i hi j hj _ => ?_,
      fun k hk0 hk => ?_, fun k hk _ _ hd _ => absurd hd (Nat.not_lt_zero _)⟩, Nat.zero_le _⟩
    · have hk' : k < 1 := hk
      have e : k = 0 := by omega
      subst e
      exact hS0'
    · dsimp only
      rw [pBit_pSet (by rw [hz]; omega), hz0, Bool.false_or, beq_iff_eq]
      constructor
      · intro e
        exact ⟨0, by simp, by rw [e]; rfl⟩
      · rintro ⟨k, hk, e⟩
        have hk' : k < 1 := hk
        have e0 : k = 0 := by omega
        subst e0
        exact e.symm
    · have hi' : i < 1 := hi
      have hj' : j < 1 := hj
      omega
    · have hk' : k < 1 := hk
      omega

end CFSG.KS.Fi23Tr
