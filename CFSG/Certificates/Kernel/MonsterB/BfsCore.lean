module

public import Mathlib.Data.Finset.Card
public import Std.Data.HashMap.Lemmas

public section

namespace CFSG.KC.Bfs

variable {α : Type} [Inhabited α]

@[expose] def gF (act : ℕ → α → α) (key : α → ℕ) (i : ℕ)
    (acc : Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ) (k : ℕ) :
    Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  let (pts, par, lab, idx, row) := acc
  let y := act k pts[i]!
  let ky := key y
  match idx.get? ky with
  | some j => (pts, par, lab, idx, row.push j)
  | none => (pts.push y, par.push i, lab.push k, idx.insert ky pts.size, row.push pts.size)

@[expose] def gStep (act : ℕ → α → α) (ngen : ℕ) (key : α → ℕ) (i : ℕ)
    (st : Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ) :
    Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  (List.range ngen).foldl (gF act key i) (st.1, st.2.1, st.2.2.1, st.2.2.2, #[])

@[expose] def gLoop (act : ℕ → α → α) (ngen : ℕ) (key : α → ℕ) :
    ℕ → ℕ → Array α → Array (Array ℕ) → Array ℕ → Array ℕ → Std.HashMap ℕ ℕ →
      Array α × Array (Array ℕ) × Array ℕ × Array ℕ
  | 0, _, pts, edges, par, lab, _ => (pts, edges, par, lab)
  | fuel + 1, i, pts, edges, par, lab, idx =>
    if i < pts.size then
      let (pts', par', lab', idx', row) := gStep act ngen key i (pts, par, lab, idx)
      gLoop act ngen key fuel (i + 1) pts' (edges.push row) par' lab' idx'
    else (pts, edges, par, lab)

@[expose] def gBfs (act : ℕ → α → α) (ngen : ℕ) (key : α → ℕ) (root : α) (fuel : ℕ) :
    Array α × Array (Array ℕ) × Array ℕ × Array ℕ :=
  gLoop act ngen key fuel 0 #[root] #[] #[0] #[0] ((∅ : Std.HashMap ℕ ℕ).insert (key root) 0)

inductive Reach (act : ℕ → α → α) (ngen : ℕ) (root : α) : α → Prop
  | root : Reach act ngen root root
  | step {x : α} (k : ℕ) : k < ngen → Reach act ngen root x → Reach act ngen root (act k x)

theorem push_get_lt (a : Array α) (x : α) {j : ℕ} (h : j < a.size) : (a.push x)[j]! = a[j]! := by
  rw [getElem!_pos (a.push x) j (by rw [Array.size_push]; omega), getElem!_pos a j h,
    Array.getElem_push_lt h]

theorem push_get_size (a : Array α) (x : α) : (a.push x)[a.size]! = x := by
  rw [getElem!_pos (a.push x) a.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem push_get_of_eq (a : Array α) (x : α) {n : ℕ} (h : a.size = n) : (a.push x)[n]! = x := by
  subst h
  exact push_get_size a x

structure Core (act : ℕ → α → α) (ngen : ℕ) (key : α → ℕ) (T : Finset α) (root : α)
    (pts : Array α) (par lab : Array ℕ) (idx : Std.HashMap ℕ ℕ) : Prop where
  pos : 0 < pts.size
  root : pts[0]! = root
  par_size : par.size = pts.size
  lab_size : lab.size = pts.size
  mem : ∀ j < pts.size, pts[j]! ∈ T
  idx_get : ∀ j < pts.size, idx[key pts[j]!]? = some j
  idx_some : ∀ m j, idx[m]? = some j → j < pts.size ∧ key pts[j]! = m
  tree : ∀ j, 0 < j → j < pts.size →
    par[j]! < j ∧ lab[j]! < ngen ∧ pts[j]! = act lab[j]! pts[par[j]!]!

@[expose] def RowOK (act : ℕ → α → α) (pts : Array α) (j : ℕ) (row : Array ℕ) (n : ℕ) : Prop :=
  row.size = n ∧ ∀ k < n, row[k]! < pts.size ∧ pts[row[k]!]! = act k pts[j]!

@[expose] def Ext (pts pts' : Array α) : Prop :=
  pts.size ≤ pts'.size ∧ ∀ j < pts.size, pts'[j]! = pts[j]!

theorem RowOK.ext {act : ℕ → α → α} {pts pts' : Array α} {j : ℕ} {row : Array ℕ} {n : ℕ}
    (h : RowOK act pts j row n) (he : Ext pts pts') (hj : j < pts.size) :
    RowOK act pts' j row n := by
  refine ⟨h.1, fun k hk => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 k hk
  exact ⟨lt_of_lt_of_le h1 he.1, by rw [he.2 _ h1, he.2 _ hj, h2]⟩

theorem Core.inj {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}
    {pts : Array α} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) {a b : ℕ} (ha : a < pts.size)
    (hb : b < pts.size) (h : key pts[a]! = key pts[b]!) : a = b := by
  have h1 := hc.idx_get a ha
  rw [h, hc.idx_get b hb] at h1
  exact (Option.some.inj h1).symm

section Step

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}

theorem gF_spec (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    {i k : ℕ} {pts : Array α} {par lab row : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hi : i < pts.size)
    (hr : RowOK act pts i row k) (hk : k < ngen) :
    Core act ngen key T root (gF act key i (pts, par, lab, idx, row) k).1
        (gF act key i (pts, par, lab, idx, row) k).2.1
        (gF act key i (pts, par, lab, idx, row) k).2.2.1
        (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 ∧
      Ext pts (gF act key i (pts, par, lab, idx, row) k).1 ∧
      RowOK act (gF act key i (pts, par, lab, idx, row) k).1 i
        (gF act key i (pts, par, lab, idx, row) k).2.2.2.2 (k + 1) := by
  have hy : act k pts[i]! ∈ T := hT _ (hc.mem i hi) k hk
  simp only [gF]
  split
  · next j heq =>
    dsimp only
    rw [Std.HashMap.get?_eq_getElem?] at heq
    obtain ⟨hj, hkj⟩ := hc.idx_some _ _ heq
    have hpj : pts[j]! = act k pts[i]! := hkey _ (hc.mem j hj) _ hy hkj
    refine ⟨hc, ⟨le_rfl, fun _ _ => rfl⟩, ?_, fun k' hk' => ?_⟩
    · rw [Array.size_push, hr.1]
    · obtain hk' | hk' := Nat.lt_succ_iff_lt_or_eq.1 hk'
      · rw [push_get_lt _ _ (by rw [hr.1]; exact hk')]
        exact hr.2 k' hk'
      · subst hk'
        rw [push_get_of_eq _ _ hr.1]
        exact ⟨hj, hpj⟩
  · next heq =>
    dsimp only
    rw [Std.HashMap.get?_eq_getElem?] at heq
    have hne : ∀ j < pts.size, key (act k pts[i]!) ≠ key pts[j]! := by
      intro j hj e
      rw [e, hc.idx_get j hj] at heq
      nomatch heq
    have hget : ∀ j < pts.size, (pts.push (act k pts[i]!))[j]! = pts[j]! :=
      fun j hj => push_get_lt _ _ hj
    have hlast : (pts.push (act k pts[i]!))[pts.size]! = act k pts[i]! := push_get_size _ _
    have hsz : (pts.push (act k pts[i]!)).size = pts.size + 1 := Array.size_push _
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨by omega, hget⟩, ?_, fun k' hk' => ?_⟩
    · omega
    · rw [hget 0 hc.pos, hc.root]
    · rw [Array.size_push, Array.size_push, hc.par_size]
    · rw [Array.size_push, Array.size_push, hc.lab_size]
    · intro j hj
      rw [hsz] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hget j hj]
        exact hc.mem j hj
      · rw [hlast]
        exact hy
    · intro j hj
      rw [hsz] at hj
      rw [Std.HashMap.getElem?_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [hget j hj]
        simp only [beq_iff_eq, hne j hj, ↓reduceIte]
        exact hc.idx_get j hj
      · simp only [hlast, beq_self_eq_true, ↓reduceIte]
    · intro m j h
      rw [Std.HashMap.getElem?_insert] at h
      split at h
      · next e =>
        rw [beq_iff_eq] at e
        cases h
        exact ⟨by omega, by rw [hlast, e]⟩
      · obtain ⟨hj, e⟩ := hc.idx_some m j h
        exact ⟨by omega, by rw [hget j hj, e]⟩
    · intro j h0 hj
      rw [hsz] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨hp, hl, e⟩ := hc.tree j h0 hj
        rw [hget j hj, push_get_lt _ _ (by rw [hc.par_size]; exact hj),
          push_get_lt _ _ (by rw [hc.lab_size]; exact hj), hget _ (by omega)]
        exact ⟨hp, hl, e⟩
      · rw [← hc.par_size, push_get_size, hc.par_size, ← hc.lab_size, push_get_size,
          hc.lab_size, hlast, hget i hi]
        exact ⟨hi, hk, rfl⟩
    · rw [Array.size_push, hr.1]
    · obtain hk' | hk' := Nat.lt_succ_iff_lt_or_eq.1 hk'
      · rw [push_get_lt _ _ (by rw [hr.1]; exact hk')]
        obtain ⟨h1, h2⟩ := hr.2 k' hk'
        exact ⟨by omega, by rw [hget _ h1, hget i hi, h2]⟩
      · subst hk'
        rw [push_get_of_eq _ _ hr.1, hlast, hget i hi]
        exact ⟨by omega, rfl⟩

theorem gFold_spec (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    {i : ℕ} {pts : Array α} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hi : i < pts.size) :
    ∀ n ≤ ngen, ∀ s : Array α × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ,
      s = (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) →
      Core act ngen key T root s.1 s.2.1 s.2.2.1 s.2.2.2.1 ∧ Ext pts s.1 ∧
        RowOK act s.1 i s.2.2.2.2 n := by
  intro n
  induction n with
  | zero =>
    rintro - s rfl
    exact ⟨hc, ⟨le_rfl, fun _ _ => rfl⟩, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ n ih =>
    rintro hn s rfl
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hc', he, hr⟩ := ih (by omega) _ rfl
    generalize (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) = s at hc' he hr
    obtain ⟨p, q, l, d, r⟩ := s
    obtain ⟨hc'', he', hr'⟩ := gF_spec hT hkey hc' (lt_of_lt_of_le hi he.1) hr (by omega)
    refine ⟨hc'', ⟨le_trans he.1 he'.1, fun j hj => ?_⟩, hr'⟩
    rw [he'.2 j (lt_of_lt_of_le hj he.1), he.2 j hj]

theorem gStep_spec (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    {i : ℕ} {pts : Array α} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hi : i < pts.size) :
    Core act ngen key T root (gStep act ngen key i (pts, par, lab, idx)).1
        (gStep act ngen key i (pts, par, lab, idx)).2.1
        (gStep act ngen key i (pts, par, lab, idx)).2.2.1
        (gStep act ngen key i (pts, par, lab, idx)).2.2.2.1 ∧
      Ext pts (gStep act ngen key i (pts, par, lab, idx)).1 ∧
      RowOK act (gStep act ngen key i (pts, par, lab, idx)).1 i
        (gStep act ngen key i (pts, par, lab, idx)).2.2.2.2 ngen :=
  gFold_spec hT hkey hc hi ngen le_rfl _ rfl

end Step

section Step

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}

theorem core_init (hroot : root ∈ T) :
    Core act ngen key T root #[root] #[0] #[0] ((∅ : Std.HashMap ℕ ℕ).insert (key root) 0) := by
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp
  · intro j hj
    have : j = 0 := by simpa using hj
    subst this
    exact hroot
  · intro j hj
    have : j = 0 := by simpa using hj
    subst this
    change ((∅ : Std.HashMap ℕ ℕ).insert (key root) 0)[key root]? = some 0
    simp
  · intro m j h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · next e =>
      rw [beq_iff_eq] at e
      cases h
      exact ⟨by simp, e⟩
    · rw [Std.HashMap.getElem?_empty] at h
      exact absurd h (by simp)
  · intro j h0 hj
    have : j < 1 := hj
    omega

end Step

section Loop

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}

@[expose] def Out (act : ℕ → α → α) (ngen : ℕ) (key : α → ℕ) (T : Finset α) (root : α)
    (r : Array α × Array (Array ℕ) × Array ℕ × Array ℕ) : Prop :=
  (∃ idx, Core act ngen key T root r.1 r.2.2.1 r.2.2.2 idx) ∧ r.2.1.size = r.1.size ∧
    ∀ j < r.1.size, RowOK act r.1 j r.2.1[j]! ngen

theorem Core.size_le {pts : Array α} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) : pts.size ≤ T.card := by
  have := Finset.card_le_card_of_injOn (s := Finset.range pts.size) (t := T)
    (fun j => pts[j]!) (fun j hj => hc.mem j (Finset.mem_range.1 hj))
    (fun a ha b hb e => hc.inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb)
      (congrArg key e))
  rwa [Finset.card_range] at this

theorem gLoop_spec (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y) :
    ∀ (f i : ℕ) (pts : Array α) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), Core act ngen key T root pts par lab idx → i ≤ pts.size →
      edges.size = i → (∀ j < i, RowOK act pts j edges[j]! ngen) → T.card ≤ i + f →
      Out act ngen key T root (gLoop act ngen key f i pts edges par lab idx) := by
  intro f
  induction f with
  | zero =>
    intro i pts edges par lab idx hc hi he hr hf
    have : i = pts.size := le_antisymm hi (by have := hc.size_le; omega)
    subst this
    exact ⟨⟨idx, hc⟩, he, hr⟩
  | succ f ih =>
    intro i pts edges par lab idx hc hi he hr hf
    rw [gLoop]
    split
    · next hlt =>
      obtain ⟨hc', hx, hrow⟩ := gStep_spec hT hkey hc hlt
      generalize gStep act ngen key i (pts, par, lab, idx) = s at hc' hx hrow
      obtain ⟨p, q, l, d, r⟩ := s
      refine ih _ _ _ _ _ _ hc' (by have := hx.1; dsimp only at this ⊢; omega)
        (by rw [Array.size_push, he]) (fun j hj => ?_) (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rw [push_get_lt _ _ (by rw [he]; exact hj)]
        exact (hr j hj).ext hx (by omega)
      · rw [← he, push_get_size, he]
        exact hrow
    · next hge =>
      have : i = pts.size := by omega
      subst this
      exact ⟨⟨idx, hc⟩, he, hr⟩

theorem gBfs_out (hroot : root ∈ T) (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y) {fuel : ℕ} (hfuel : T.card ≤ fuel) :
    Out act ngen key T root (gBfs act ngen key root fuel) := by
  exact gLoop_spec hT hkey fuel 0 _ _ _ _ _ (core_init hroot) (Nat.zero_le _)
    rfl (fun j hj => absurd hj (Nat.not_lt_zero _)) (by omega)

end Loop

section Spec

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α} {fuel : ℕ}

theorem gBfs_spec (hroot : root ∈ T) (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y) (hfuel : T.card ≤ fuel) :
    0 < (gBfs act ngen key root fuel).1.size ∧ (gBfs act ngen key root fuel).1[0]! = root ∧
      (∀ j < (gBfs act ngen key root fuel).1.size, (gBfs act ngen key root fuel).1[j]! ∈ T) ∧
      (∀ a < (gBfs act ngen key root fuel).1.size, ∀ b < (gBfs act ngen key root fuel).1.size,
        key (gBfs act ngen key root fuel).1[a]! = key (gBfs act ngen key root fuel).1[b]! →
          a = b) ∧
      (gBfs act ngen key root fuel).2.1.size = (gBfs act ngen key root fuel).1.size ∧
      (∀ j < (gBfs act ngen key root fuel).1.size,
        ((gBfs act ngen key root fuel).2.1[j]!).size = ngen ∧
        ∀ k < ngen, (gBfs act ngen key root fuel).2.1[j]![k]! <
            (gBfs act ngen key root fuel).1.size ∧
          (gBfs act ngen key root fuel).1[(gBfs act ngen key root fuel).2.1[j]![k]!]! =
            act k (gBfs act ngen key root fuel).1[j]!) ∧
      ∀ j, 0 < j → j < (gBfs act ngen key root fuel).1.size →
        (gBfs act ngen key root fuel).2.2.1[j]! < j ∧
        (gBfs act ngen key root fuel).2.2.2[j]! < ngen ∧
        (gBfs act ngen key root fuel).1[j]! =
          act (gBfs act ngen key root fuel).2.2.2[j]!
            (gBfs act ngen key root fuel).1[(gBfs act ngen key root fuel).2.2.1[j]!]! := by
  obtain ⟨⟨idx, hc⟩, he, hr⟩ := gBfs_out (fuel := fuel) hroot hT hkey hfuel
  exact ⟨hc.pos, hc.root, hc.mem, fun a ha b hb e => hc.inj ha hb e, he, hr, hc.tree⟩

theorem gBfs_reach (hroot : root ∈ T) (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y) (hfuel : T.card ≤ fuel) :
    ∀ j < (gBfs act ngen key root fuel).1.size,
      Reach act ngen root (gBfs act ngen key root fuel).1[j]! := by
  obtain ⟨-, h0, -, -, -, -, htree⟩ := gBfs_spec (fuel := fuel) hroot hT hkey hfuel
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | h0'
    · rw [h0]
      exact Reach.root
    · obtain ⟨hp, hl, e⟩ := htree j h0' hj
      rw [e]
      exact Reach.step _ hl (ih _ hp (by omega))

theorem gBfs_complete (hroot : root ∈ T) (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y) (hfuel : T.card ≤ fuel) {x : α}
    (hx : Reach act ngen root x) :
    ∃ j < (gBfs act ngen key root fuel).1.size, (gBfs act ngen key root fuel).1[j]! = x := by
  obtain ⟨hpos, h0, -, -, -, hr, -⟩ := gBfs_spec (fuel := fuel) hroot hT hkey hfuel
  induction hx with
  | root => exact ⟨0, hpos, h0⟩
  | step k hk _ ih =>
    obtain ⟨j, hj, rfl⟩ := ih
    exact ⟨_, (hr j hj).2 k hk |>.1, (hr j hj).2 k hk |>.2⟩

theorem nodup_map_of_inj {β : Type} [Inhabited β] {xs : Array β} (f : β → ℕ)
    (h : ∀ a < xs.size, ∀ b < xs.size, f xs[a]! = f xs[b]! → a = b) :
    (xs.toList.map f).Nodup := by
  rw [List.nodup_iff_injective_get]
  rintro ⟨a, ha⟩ ⟨b, hb⟩ e
  simp only [List.length_map, Array.length_toList] at ha hb
  simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList] at e
  rw [← getElem!_pos xs a ha, ← getElem!_pos xs b hb] at e
  exact Fin.ext (h a ha b hb e)

theorem gBfs_listing [DecidableEq α] (S : Finset α) (hS : ∀ x, Reach act ngen root x ↔ x ∈ S)
    (hkey : ∀ x ∈ S, ∀ y ∈ S, key x = key y → x = y) (hfuel : S.card ≤ fuel) :
    (∀ x, x ∈ (gBfs act ngen key root fuel).1 ↔ x ∈ S) ∧
      (gBfs act ngen key root fuel).1.size = S.card ∧
      ((gBfs act ngen key root fuel).1.toList.map key).Nodup := by
  have hroot : root ∈ S := (hS root).1 Reach.root
  have hT : ∀ x ∈ S, ∀ k < ngen, act k x ∈ S := fun x hx k hk =>
    (hS _).1 (Reach.step k hk ((hS x).2 hx))
  obtain ⟨-, -, hmem, hinj, -⟩ := gBfs_spec (fuel := fuel) hroot hT hkey hfuel
  have hnd := nodup_map_of_inj key hinj
  have hiff : ∀ x, x ∈ (gBfs act ngen key root fuel).1 ↔ x ∈ S := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
      rw [← getElem!_pos _ j hj]
      exact hmem j hj
    · intro hx
      obtain ⟨j, hj, rfl⟩ := gBfs_complete hroot hT hkey hfuel ((hS x).2 hx)
      rw [getElem!_pos _ j hj]
      exact Array.getElem_mem hj
  refine ⟨hiff, ?_, hnd⟩
  have hnd' : (gBfs act ngen key root fuel).1.toList.Nodup := List.Nodup.of_map key hnd
  have e : (gBfs act ngen key root fuel).1.toList.toFinset = S := by
    ext x
    rw [List.mem_toFinset, Array.mem_toList_iff, hiff]
  rw [← e, List.toFinset_card_of_nodup hnd', Array.length_toList]

end Spec

theorem pairwise_lt_mergeSort {l : List ℕ} (h : l.Nodup) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· < ·) := by
  have hs := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
    (fun a b c hab hbc => decide_eq_true (le_trans (of_decide_eq_true hab)
      (of_decide_eq_true hbc)))
    (fun a b => by rcases le_total a b with h | h <;> simp [h]) l
  have hn : (l.mergeSort (fun a b => decide (a ≤ b))).Nodup :=
    (List.mergeSort_perm l _).nodup_iff.2 h
  exact (hs.and hn).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne (of_decide_eq_true h1) h2

omit [Inhabited α] in
theorem reach_iff_of_closed {act : ℕ → α → α} {ngen : ℕ} {root : α} {S : Finset α}
    (hroot : root ∈ S) (hS : ∀ x ∈ S, ∀ k < ngen, act k x ∈ S)
    (hR : ∀ x ∈ S, Reach act ngen root x) (x : α) : Reach act ngen root x ↔ x ∈ S := by
  refine ⟨fun h => ?_, hR x⟩
  induction h with
  | root => exact hroot
  | step k hk _ ih => exact hS _ ih k hk

end CFSG.KC.Bfs
