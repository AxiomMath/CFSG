module

public import CFSG.Certificates.Kernel.MonsterB.BfsReplaySound

public section

namespace CFSG.KC.Bfs

variable {α : Type} [Inhabited α]

section Trunc

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}
  {L : Array α} {E : ℕ → ℕ → ℕ}

theorem gF_core {i k : ℕ} {pts : Array α} {par lab row : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hi : i < pts.size) (hk : k < ngen)
    (hy : act k pts[i]! ∈ T) :
    Core act ngen key T root (gF act key i (pts, par, lab, idx, row) k).1
      (gF act key i (pts, par, lab, idx, row) k).2.1
      (gF act key i (pts, par, lab, idx, row) k).2.2.1
      (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 := by
  simp only [gF]
  split
  · exact hc
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

theorem rStep_le {i k m m' : ℕ} (h : rStep E i (some m) k = some m') : m ≤ m' := by
  simp only [rStep] at h
  split at h
  · cases h
    exact le_rfl
  · split at h
    · cases h
      omega
    · nomatch h

theorem gF_trunc (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hT : ∀ j < L.size, L[j]! ∈ T) {i k m' : ℕ} {pts : Array α} {par lab row : Array ℕ}
    {idx : Std.HashMap ℕ ℕ} (hc : Core act ngen key T root pts par lab idx) (hp : Pre pts L)
    (hi : i < pts.size) (hk : k < ngen) (hEk : E i k < L.size ∧ L[E i k]! = act k L[i]!)
    (h : rStep E i (some pts.size) k = some m') :
    Core act ngen key T root (gF act key i (pts, par, lab, idx, row) k).1
        (gF act key i (pts, par, lab, idx, row) k).2.1
        (gF act key i (pts, par, lab, idx, row) k).2.2.1
        (gF act key i (pts, par, lab, idx, row) k).2.2.2.1 ∧
      (gF act key i (pts, par, lab, idx, row) k).1.size = m' ∧
      Pre (gF act key i (pts, par, lab, idx, row) k).1 L := by
  obtain ⟨hEL, hEe⟩ := hEk
  have hy : act k pts[i]! = L[E i k]! := by rw [hp.2 i hi, hEe]
  refine ⟨gF_core hc hi hk (by rw [hy]; exact hT _ hEL), ?_⟩
  simp only [rStep] at h
  simp only [gF]
  split
  · next j heq =>
    dsimp only
    rw [Std.HashMap.get?_eq_getElem?] at heq
    obtain ⟨hj, hkj⟩ := hc.idx_some _ _ heq
    split at h
    · cases h
      exact ⟨rfl, hp⟩
    · split at h
      · next _ he =>
        rw [hy, hp.2 j hj, he] at hkj
        have := hkeyL j (lt_of_lt_of_le hj hp.1) _ (he ▸ hEL) hkj
        omega
      · nomatch h
  · next heq =>
    dsimp only
    rw [Std.HashMap.get?_eq_getElem?] at heq
    split at h
    · next hlt =>
      have h1 := hc.idx_get _ hlt
      rw [hp.2 _ hlt, ← hy, heq] at h1
      nomatch h1
    · split at h
      · next _ he =>
        cases h
        refine ⟨Array.size_push _, by rw [Array.size_push]; omega, fun j hj => ?_⟩
        rw [Array.size_push] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [push_get_lt _ _ hj, hp.2 j hj]
        · rw [push_get_size, hy, he]
      · nomatch h

theorem gFold_trunc (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hT : ∀ j < L.size, L[j]! ∈ T) {i : ℕ}
    (hEi : ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!) {pts : Array α}
    {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ} (hc : Core act ngen key T root pts par lab idx)
    (hp : Pre pts L) (hi : i < pts.size) :
    ∀ n ≤ ngen, ∀ m', (List.range n).foldl (rStep E i) (some pts.size) = some m' →
      Core act ngen key T root ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).1
          ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).2.1
          ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).2.2.1
          ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).2.2.2.1 ∧
        ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).1.size = m' ∧
        pts.size ≤ m' ∧
        Pre ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).1 L := by
  intro n
  induction n with
  | zero =>
    intro _ m' h
    cases h
    exact ⟨hc, rfl, le_rfl, hp⟩
  | succ n ih =>
    intro hn m' h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    cases ho : (List.range n).foldl (rStep E i) (some pts.size) with
    | none =>
      rw [ho] at h
      nomatch h
    | some m'' =>
      rw [ho] at h
      obtain ⟨hc', hs, hle, hp'⟩ := ih (by omega) m'' ho
      generalize (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) = s at hc' hs hp'
      obtain ⟨p, q, l, d, r⟩ := s
      dsimp only at hs hp' hc'
      subst hs
      obtain ⟨h1, h2, h3⟩ := gF_trunc hkeyL hT hc' hp' (by omega) (by omega) (hEi n (by omega)) h
      exact ⟨h1, h2, le_trans hle (rStep_le h), h3⟩

theorem gLoop_trunc (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hT : ∀ j < L.size, L[j]! ∈ T) :
    ∀ (c i : ℕ) (pts : Array α) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), Core act ngen key T root pts par lab idx → Pre pts L →
      (∀ i', i ≤ i' → i' < i + c → ∀ k < ngen, E i' k < L.size ∧ L[E i' k]! = act k L[i']!) →
      replayLoop E ngen c i pts.size = some L.size →
      (gLoop act ngen key c i pts edges par lab idx).1 = L ∧
        ∃ idx', Core act ngen key T root (gLoop act ngen key c i pts edges par lab idx).1
          (gLoop act ngen key c i pts edges par lab idx).2.2.1
          (gLoop act ngen key c i pts edges par lab idx).2.2.2 idx' := by
  intro c
  induction c with
  | zero =>
    intro i pts edges par lab idx hc hp _ hr
    simp only [replayLoop, Option.some.injEq] at hr
    refine ⟨Array.ext hr fun j h1 h2 => ?_, idx, hc⟩
    rw [← getElem!_pos _ j h1, ← getElem!_pos L j h2]
    exact hp.2 j h1
  | succ c ih =>
    intro i pts edges par lab idx hc hp hE hr
    simp only [replayLoop] at hr
    split at hr
    · next hlt =>
      cases hrow : rRow E ngen i pts.size with
      | none =>
        rw [hrow] at hr
        nomatch hr
      | some m' =>
        rw [hrow] at hr
        obtain ⟨hc', hs, hle, hp'⟩ := gFold_trunc hkeyL hT
          (hE i le_rfl (by omega)) hc hp hlt ngen le_rfl m' hrow
        rw [gLoop, if_pos hlt]
        have e : gStep act ngen key i (pts, par, lab, idx) =
            (List.range ngen).foldl (gF act key i) (pts, par, lab, idx, #[]) := rfl
        rw [e]
        generalize (List.range ngen).foldl (gF act key i) (pts, par, lab, idx, #[]) = s
          at hc' hs hp'
        obtain ⟨p, q, l, d, r⟩ := s
        dsimp only at hs hp' hc' ⊢
        subst hs
        exact ih (i + 1) p (edges.push r) q l d hc' hp'
          (fun i' h1 h2 k hk => hE i' (by omega) (by omega) k hk) hr
    · nomatch hr

theorem gBfs_trunc [DecidableEq α] (hL : 0 < L.size) (h0 : L[0]! = root)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b) {f : ℕ}
    (hE : ∀ i < f, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    (hrep : replayLoop E ngen f 0 1 = some L.size) :
    (gBfs act ngen key root f).1 = L ∧
      ∀ j, 0 < j → j < L.size → (gBfs act ngen key root f).2.2.1[j]! < j ∧
        (gBfs act ngen key root f).2.2.2[j]! < ngen ∧
        L[j]! = act (gBfs act ngen key root f).2.2.2[j]! L[(gBfs act ngen key root f).2.2.1[j]!]! := by
  have hT : ∀ j < L.size, L[j]! ∈ L.toList.toFinset := by
    intro j hj
    rw [List.mem_toFinset, Array.mem_toList_iff, getElem!_pos L j hj]
    exact Array.getElem_mem hj
  unfold gBfs
  obtain ⟨hs, idx', hc⟩ := gLoop_trunc (act := act) (ngen := ngen) (key := key) (root := root)
    (E := E) hkeyL hT f 0 _ #[] _ _ _ (core_init (by rw [← h0]; exact hT 0 hL))
    ⟨Nat.succ_le_of_lt hL, fun j hj => by
      have : j = 0 := by simpa using hj
      subst this
      exact h0.symm⟩ (fun i' _ h2 k hk => hE i' (by omega) k hk) hrep
  refine ⟨hs, fun j h0' hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hc.tree j h0' (by rw [hs]; exact hj)
  rw [hs] at h3
  exact ⟨h1, h2, h3⟩

end Trunc

end CFSG.KC.Bfs
