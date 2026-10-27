
module

public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public import CFSG.Certificates.Kernel.MonsterB.BfsReplaySound
public import CFSG.Certificates.Kernel.Co2InvS.BfsS

public section

namespace CFSG.KS.LeftEnum

open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.KC.Bfs

@[expose] def actL (gens : Array (Array ℕ)) (k : ℕ) (x : Array ℕ) : Array ℕ :=
  compA 2300 gens[k]! x

abbrev ISt := Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ

abbrev OSt := Array (Array ℕ) × Array ℕ × Array ℕ × Array (Array ℕ) × Std.HashMap ℕ ℕ

@[expose] def lInner (gens : Array (Array ℕ)) (x : Array ℕ) (h : ℕ) (s : ISt) (j : ℕ) : ISt :=
  match s.2.2.2.1.get? (keyA (compA 2300 gens[j]! x)) with
  | some i => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.push i)
  | none => (s.1.push (compA 2300 gens[j]! x), s.2.1.push h, s.2.2.1.push j,
      s.2.2.2.1.insert (keyA (compA 2300 gens[j]! x)) s.1.size, s.2.2.2.2.push s.1.size)

@[expose] def lOuter (gens : Array (Array ℕ)) (s : OSt) (h : ℕ) : OSt :=
  if h < s.1.size then
    (fun t : ISt => (t.1, t.2.1, t.2.2.1, s.2.2.2.1.push t.2.2.2.2, t.2.2.2.1))
      ((List.range gens.size).foldl (lInner gens s.1[h]! h) (s.1, s.2.1, s.2.2.1, s.2.2.2.2, #[]))
  else s

@[expose] def lInit : OSt :=
  (#[idA 2300], #[0], #[0], #[], (∅ : Std.HashMap ℕ ℕ).insert (keyA (idA 2300)) 0)

theorem leftEnum_eq (gens : Array (Array ℕ)) (cap : ℕ) :
    leftEnum gens cap = (fun s : OSt => (⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2⟩ : LeftEnum))
      ((List.range cap).foldl (lOuter gens) lInit) := by
  unfold leftEnum
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  rw [CFSG.KC.Co2InvS.forIn_id_eq_foldl (g := lOuter gens)]
  · rfl
  · intro h s
    unfold lOuter
    split
    · rw [CFSG.KC.Co2InvS.forIn_id_eq_foldl (g := lInner gens s.1[h]! h)]
      · rfl
      · intro j t
        unfold lInner
        split <;> (rename_i heq; simp only [heq]; rfl)
    · rfl

theorem lInner_eq {gens : Array (Array ℕ)} {x : Array ℕ} {h : ℕ} {s : ISt} (hs : h < s.1.size)
    (hx : s.1[h]! = x) (j : ℕ) : lInner gens x h s j = gF (actL gens) keyA h s j := by
  obtain ⟨p, q, l, d, r⟩ := s
  dsimp only at hs hx
  subst hx
  unfold lInner gF actL
  dsimp only
  cases d.get? (keyA (compA 2300 gens[j]! p[h]!)) <;> simp only

theorem gF_keep {gens : Array (Array ℕ)} {h : ℕ} {s : ISt} (hs : h < s.1.size) (j : ℕ) :
    h < (gF (actL gens) keyA h s j).1.size ∧ (gF (actL gens) keyA h s j).1[h]! = s.1[h]! := by
  obtain ⟨p, q, l, d, r⟩ := s
  dsimp only at hs
  unfold gF
  dsimp only
  split
  · exact ⟨hs, rfl⟩
  · exact ⟨by rw [Array.size_push]; omega, push_get_lt _ _ hs⟩

theorem lFold_eq {gens : Array (Array ℕ)} {x : Array ℕ} {h : ℕ} (l : List ℕ) :
    ∀ (s : ISt), h < s.1.size → s.1[h]! = x →
      l.foldl (lInner gens x h) s = l.foldl (gF (actL gens) keyA h) s := by
  induction l with
  | nil => intro _ _ _; rw [List.foldl_nil, List.foldl_nil]
  | cons j l ih =>
    intro s hs hx
    rw [List.foldl_cons, List.foldl_cons, lInner_eq hs hx]
    obtain ⟨h1, h2⟩ := gF_keep (gens := gens) hs j
    exact ih _ h1 (by rw [h2, hx])

theorem lOuter_eq {gens : Array (Array ℕ)} {el : Array (Array ℕ)} {par lab : Array ℕ}
    {tbl : Array (Array ℕ)} {pos : Std.HashMap ℕ ℕ} {h : ℕ} (hs : h < el.size) :
    lOuter gens (el, par, lab, tbl, pos) h =
      (fun t : ISt => (t.1, t.2.1, t.2.2.1, tbl.push t.2.2.2.2, t.2.2.2.1))
        (gStep (actL gens) gens.size keyA h (el, par, lab, pos)) := by
  unfold lOuter gStep
  simp only [hs, ↓reduceIte]
  rw [lFold_eq (List.range gens.size) (el, par, lab, pos, #[]) hs rfl]

theorem lOuter_stop {gens : Array (Array ℕ)} {s : OSt} {h : ℕ} (hs : s.1.size ≤ h) :
    lOuter gens s h = s := by
  unfold lOuter
  have hn : ¬ h < s.1.size := by omega
  simp only [hn, ↓reduceIte]

theorem lFold_stop {gens : Array (Array ℕ)} :
    ∀ (l : List ℕ) (s : OSt), (∀ h ∈ l, s.1.size ≤ h) → l.foldl (lOuter gens) s = s
  | [], _, _ => rfl
  | h :: l, s, hl => by
    rw [List.foldl_cons, lOuter_stop (hl h List.mem_cons_self)]
    exact lFold_stop l s fun h' hh => hl h' (List.mem_cons_of_mem _ hh)

section Replay

variable {gens : Array (Array ℕ)} {N : ℕ} {L : Array (Array ℕ)} {E : ℕ → ℕ → ℕ}

structure LInv (gens : Array (Array ℕ)) (L : Array (Array ℕ)) (T : Finset (Array ℕ)) (m n : ℕ)
    (s : OSt) : Prop where
  core : Core (actL gens) gens.size keyA T (idA 2300) s.1 s.2.1 s.2.2.1 s.2.2.2.2
  size : s.1.size = m
  pre : Pre s.1 L
  tsize : s.2.2.2.1.size = n
  rows : ∀ j < n, RowOK (actL gens) s.1 j s.2.2.2.1[j]! gens.size

theorem lInv_step {T : Finset (Array ℕ)} (hT : ∀ x ∈ T, ∀ k < gens.size, actL gens k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, keyA x = keyA y → x = y)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, keyA L[a]! = keyA L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < gens.size, E i k < L.size ∧ L[E i k]! = actL gens k L[i]!)
    {s : OSt} {m m' n : ℕ} (hI : LInv gens L T m n s) (hn : n < m)
    (hr : rRow E gens.size n m = some m') : LInv gens L T m' (n + 1) (lOuter gens s n) := by
  obtain ⟨el, par, lab, tbl, pos⟩ := s
  obtain ⟨hc, hsz, hp, hts, hrows⟩ := hI
  dsimp only at hc hsz hp hts hrows
  subst hsz
  rw [lOuter_eq hn]
  dsimp only
  obtain ⟨hc', hx, hrow⟩ := gStep_spec hT hkey hc hn
  obtain ⟨hs', hp'⟩ := gFold_replay hT hkey hkeyL hE hc hp hn gens.size le_rfl m' hr
  have hs'' : (gStep (actL gens) gens.size keyA n (el, par, lab, pos)).1.size = m' := hs'
  have hp'' : Pre (gStep (actL gens) gens.size keyA n (el, par, lab, pos)).1 L := hp'
  generalize gStep (actL gens) gens.size keyA n (el, par, lab, pos) = t at hc' hx hrow hs'' hp''
  obtain ⟨p, q, l, d, r⟩ := t
  dsimp only at hc' hx hrow hs'' hp'' ⊢
  refine ⟨hc', hs'', hp'', by rw [Array.size_push, hts], fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [push_get_lt _ _ (by rw [hts]; exact hj)]
    exact (hrows j hj).ext hx (by omega)
  · rw [← hts, push_get_size, hts]
    exact hrow

theorem leftEnum_replay (hN : L.size = N) (hL : 0 < N) (h0 : L[0]! = idA 2300)
    (hkeyL : ∀ a < N, ∀ b < N, keyA L[a]! = keyA L[b]! → a = b)
    (hE : ∀ i < N, ∀ k < gens.size, E i k < N ∧ L[E i k]! = compA 2300 gens[k]! L[i]!)
    {M : ℕ → ℕ} (hM0 : M 0 = 1) (hMN : M N = N)
    (hM : ∀ k < N, k < M k ∧ rRow E gens.size k (M k) = some (M (k + 1)))
    {cap : ℕ} (hcap : N ≤ cap) :
    (leftEnum gens cap).elems = L ∧ (leftEnum gens cap).mult.size = N ∧
      (∀ j < N, RowOK (actL gens) L j (leftEnum gens cap).mult[j]! gens.size) ∧
      (∀ j, 0 < j → j < N → (leftEnum gens cap).par[j]! < j ∧
        (leftEnum gens cap).lab[j]! < gens.size ∧
        L[j]! = compA 2300 gens[(leftEnum gens cap).lab[j]!]! L[(leftEnum gens cap).par[j]!]!) ∧
      (∀ j < N, (leftEnum gens cap).pos[keyA L[j]!]? = some j) := by
  subst hN
  have memL : ∀ x, x ∈ L.toList.toFinset ↔ ∃ a < L.size, L[a]! = x := by
    intro x
    rw [List.mem_toFinset, Array.mem_toList_iff, Array.mem_iff_getElem]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, getElem!_pos L a ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (getElem!_pos L a ha).symm⟩
  have hroot : idA 2300 ∈ L.toList.toFinset := (memL _).2 ⟨0, hL, h0⟩
  have hT : ∀ x ∈ L.toList.toFinset, ∀ k < gens.size, actL gens k x ∈ L.toList.toFinset := by
    intro x hx k hk
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    exact (memL _).2 ⟨_, (hE a ha k hk).1, (hE a ha k hk).2⟩
  have hkey : ∀ x ∈ L.toList.toFinset, ∀ y ∈ L.toList.toFinset, keyA x = keyA y → x = y := by
    intro x hx y hy e
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    obtain ⟨b, hb, rfl⟩ := (memL y).1 hy
    rw [hkeyL a ha b hb e]
  have hE' : ∀ i < L.size, ∀ k < gens.size, E i k < L.size ∧ L[E i k]! = actL gens k L[i]! :=
    hE
  have inv : ∀ n ≤ L.size, LInv gens L L.toList.toFinset (M n) n
      ((List.range n).foldl (lOuter gens) lInit) := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [hM0, List.range_zero, List.foldl_nil]
      have e1 : lInit.1.size = 1 := rfl
      have e0 : ∀ y : Array ℕ, (#[y] : Array (Array ℕ))[0]! = y := fun y => rfl
      refine ⟨core_init hroot, e1, ⟨by rw [e1]; omega, fun j hj => ?_⟩, rfl,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      rw [e1] at hj
      have : j = 0 := by omega
      subst this
      rw [h0]
      exact e0 _
    | succ n ih =>
      intro hn
      have hI := ih (by omega)
      obtain ⟨hkM, hr⟩ := hM n (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact lInv_step hT hkey hkeyL hE' hI hkM hr
  obtain ⟨hc, hsz, hp, hts, hrows⟩ := inv L.size le_rfl
  rw [hMN] at hsz
  have hcapE : List.range cap =
      List.range L.size ++ (List.range (cap - L.size)).map (L.size + ·) := by
    rw [← List.range_add, Nat.add_sub_cancel' hcap]
  have hfin : (List.range cap).foldl (lOuter gens) lInit =
      (List.range L.size).foldl (lOuter gens) lInit := by
    rw [hcapE, List.foldl_append]
    exact lFold_stop _ _ fun h hh => by
      rw [hsz]
      obtain ⟨t, -, rfl⟩ := List.mem_map.1 hh
      omega
  have hel : ((List.range L.size).foldl (lOuter gens) lInit).1 = L := by
    refine Array.ext (by rw [hsz]) fun j h1 h2 => ?_
    rw [← getElem!_pos _ j h1, ← getElem!_pos L j h2]
    exact hp.2 j h1
  rw [leftEnum_eq, hfin]
  dsimp only
  rw [hel] at hc hrows
  refine ⟨hel, hts, hrows, fun j h0' hj => ?_, fun j hj => ?_⟩
  · exact hc.tree j h0' hj
  · exact hc.idx_get j hj

theorem eqA_refl (t : Array ℕ) : eqA 2300 t t = true := by
  rw [eqA, CFSG.Monster.B.Co2.allLt_iff]
  intro i _
  exact beq_self_eq_true _

theorem enumOK_of_replay (hN : L.size = N) (hL : 0 < N) (h0 : L[0]! = idA 2300)
    (hkeyL : ∀ a < N, ∀ b < N, keyA L[a]! = keyA L[b]! → a = b)
    (hE : ∀ i < N, ∀ k < gens.size, E i k < N ∧ L[E i k]! = compA 2300 gens[k]! L[i]!)
    {M : ℕ → ℕ} (hM0 : M 0 = 1) (hMN : M N = N)
    (hM : ∀ k < N, k < M k ∧ rRow E gens.size k (M k) = some (M (k + 1)))
    (hinv : ∀ k < N, isInvA 2300 L[k]! (invCand 2300 L[k]!) = true) {cap : ℕ} (hcap : N ≤ cap) :
    enumOK gens N (leftEnum gens cap) = true := by
  obtain ⟨he, hms, hrow, htree, hpos⟩ := leftEnum_replay hN hL h0 hkeyL hE hM0 hMN hM hcap
  unfold enumOK
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true,
    decide_eq_true_eq, he, hN]
  have hid : eqA 2300 L[0]! (idA 2300) = true := by
    rw [h0]
    exact eqA_refl _
  refine ⟨⟨⟨⟨⟨trivial, hid⟩, hinv⟩, fun k hk => ?_⟩, fun k hk j hj => ?_⟩, fun k hk => ?_⟩
  · rcases Nat.eq_zero_or_pos k with e | e
    · exact Or.inl e
    · obtain ⟨a, b, c⟩ := htree k e hk
      refine Or.inr ⟨⟨a, b⟩, ?_⟩
      rw [← c]
      exact eqA_refl _
  · obtain ⟨h1, h2⟩ := (hrow k hk).2 j hj
    refine ⟨by rw [← hN]; exact h1, ?_⟩
    rw [h2]
    exact eqA_refl _
  · rw [Std.HashMap.getD_eq_getD_getElem?, hpos k hk]
    rfl

end Replay

end CFSG.KS.LeftEnum

end
