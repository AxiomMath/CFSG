module

public import CFSG.Certificates.Kernel.MonsterB.NatBfsSound
public import CFSG.Monster.B.CTIB.Cert

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.CTIB

@[expose] def stepVal {β : Type} : ForInStep β → β
  | .done b => b
  | .yield b => b

theorem forIn_id_eq_foldl {β : Type} (l : List ℕ) (init : β) (f : ℕ → β → Id (ForInStep β))
    (h : ∀ a b, ∃ c, f a b = ForInStep.yield c) :
    forIn l init f = (pure (l.foldl (fun b a => stepVal (f a b)) init) : Id β) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨c, hc⟩ := h a init
    rw [List.forIn_cons, List.foldl_cons, hc]
    exact ih c

theorem range_size (n : ℕ) : [:n].size = n := by
  simp [Std.Legacy.Range.size]

@[expose] def cInner (act : ℕ → ℕ → ℕ) (p i : ℕ)
    (s : Std.HashMap ℕ ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ) (k : ℕ) :
    Std.HashMap ℕ ℕ × Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  match s.1.get? (act k p) with
  | some j => (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.push j)
  | none => (s.1.insert (act k p) s.2.1.size, s.2.1.push (act k p), s.2.2.1.push i,
      s.2.2.2.1.push k, s.2.2.2.2.push s.2.1.size)

@[expose] def cOuter (act : ℕ → ℕ → ℕ) (ngen : ℕ)
    (s : Std.HashMap ℕ ℕ × Array ℕ × Array ℕ × Array ℕ × Array (Array ℕ)) (i : ℕ) :
    Std.HashMap ℕ ℕ × Array ℕ × Array ℕ × Array ℕ × Array (Array ℕ) :=
  if i < s.2.1.size then
    let r := (List.range' 0 ngen).foldl (cInner act s.2.1[i]! i)
      (s.1, s.2.1, s.2.2.1, s.2.2.2.1, #[])
    (r.1, r.2.1, r.2.2.1, r.2.2.2.1, s.2.2.2.2.push r.2.2.2.2)
  else s

theorem native_natBfs_fold (act : ℕ → ℕ → ℕ) (ngen root fuel : ℕ) :
    Native.natBfs act ngen root fuel =
      (((List.range' 0 fuel).foldl (cOuter act ngen)
          ((∅ : Std.HashMap ℕ ℕ).insert root 0, #[root], #[0], #[0], #[])).2.1,
        ((List.range' 0 fuel).foldl (cOuter act ngen)
          ((∅ : Std.HashMap ℕ ℕ).insert root 0, #[root], #[0], #[0], #[])).2.2.2.2,
        ((List.range' 0 fuel).foldl (cOuter act ngen)
          ((∅ : Std.HashMap ℕ ℕ).insert root 0, #[root], #[0], #[0], #[])).2.2.1,
        ((List.range' 0 fuel).foldl (cOuter act ngen)
          ((∅ : Std.HashMap ℕ ℕ).insert root 0, #[root], #[0], #[0], #[])).2.2.2.1) := by
  unfold Native.natBfs
  dsimp only
  rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_id_eq_foldl, range_size]
  · rw [List.foldl_ext _ (cOuter act ngen) _ fun s i _ => ?_]
    · rfl
    obtain ⟨idx, pts, par, lab, edges⟩ := s
    unfold cOuter
    dsimp only
    by_cases hi : i < pts.size
    · simp only [hi, ↓reduceIte]
      rw [Std.Legacy.Range.forIn_eq_forIn_range', forIn_id_eq_foldl, range_size]
      · rw [List.foldl_ext _ (cInner act pts[i]! i) _ fun s k _ => ?_]
        · rfl
        obtain ⟨idx', pts', par', lab', row'⟩ := s
        unfold cInner
        dsimp only
        rcases idx'.get? (act k pts[i]!) with _ | j <;> rfl
      · intro k s
        obtain ⟨idx', pts', par', lab', row'⟩ := s
        dsimp only
        split
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
    · simp only [hi, ↓reduceIte]
      rfl
  · intro i s
    obtain ⟨idx, pts, par, lab, edges⟩ := s
    dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

theorem gF_ext' (act : ℕ → ℕ → ℕ) (i k : ℕ) (pts : Array ℕ) (par lab row : Array ℕ)
    (idx : Std.HashMap ℕ ℕ) : Ext pts (gF act id i (pts, par, lab, idx, row) k).1 := by
  simp only [gF]
  split
  · exact ⟨le_rfl, fun _ _ => rfl⟩
  · refine ⟨by rw [Array.size_push]; omega, fun j hj => push_get_lt _ _ hj⟩

theorem cInner_fold (act : ℕ → ℕ → ℕ) {i : ℕ} {pts : Array ℕ} (hi : i < pts.size)
    (par lab : Array ℕ) (idx : Std.HashMap ℕ ℕ) :
    ∀ n, (List.range n).foldl (cInner act pts[i]! i) (idx, pts, par, lab, #[]) =
      (((List.range n).foldl (gF act id i) (pts, par, lab, idx, #[])).2.2.2.1,
        ((List.range n).foldl (gF act id i) (pts, par, lab, idx, #[])).1,
        ((List.range n).foldl (gF act id i) (pts, par, lab, idx, #[])).2.1,
        ((List.range n).foldl (gF act id i) (pts, par, lab, idx, #[])).2.2.1,
        ((List.range n).foldl (gF act id i) (pts, par, lab, idx, #[])).2.2.2.2) ∧
      Ext pts ((List.range n).foldl (gF act id i) (pts, par, lab, idx, #[])).1 := by
  intro n
  induction n with
  | zero => exact ⟨rfl, le_rfl, fun _ _ => rfl⟩
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, ih.1]
    obtain ⟨-, he⟩ := ih
    generalize (List.range n).foldl (gF act id i) (pts, par, lab, idx, #[]) = s at he
    obtain ⟨p, q, l, d, r⟩ := s
    dsimp only at he ⊢
    have hp : p[i]! = pts[i]! := he.2 i hi
    have he' := gF_ext' act i n p q l r d
    refine ⟨?_, le_trans he.1 he'.1, fun j hj => by rw [he'.2 j (lt_of_lt_of_le hj he.1), he.2 j hj]⟩
    unfold cInner gF
    dsimp only [id]
    rw [hp]
    rcases d.get? (act n pts[i]!) with _ | j <;> rfl

theorem cOuter_idle (act : ℕ → ℕ → ℕ) (ngen : ℕ) :
    ∀ (f i : ℕ) (s : Std.HashMap ℕ ℕ × Array ℕ × Array ℕ × Array ℕ × Array (Array ℕ)),
      s.2.1.size ≤ i → (List.range' i f).foldl (cOuter act ngen) s = s := by
  intro f
  induction f with
  | zero => intro i s _; rfl
  | succ f ih =>
    intro i s h
    rw [List.range'_succ, List.foldl_cons]
    have : cOuter act ngen s i = s := by
      have hn : ¬ i < s.2.1.size := by omega
      unfold cOuter
      simp only [hn, ↓reduceIte]
    rw [this]
    exact ih (i + 1) s (by omega)

theorem cOuter_loop (act : ℕ → ℕ → ℕ) (ngen : ℕ) :
    ∀ (f i : ℕ) (pts : Array ℕ) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ),
      (((List.range' i f).foldl (cOuter act ngen) (idx, pts, par, lab, edges)).2.1,
        ((List.range' i f).foldl (cOuter act ngen) (idx, pts, par, lab, edges)).2.2.2.2,
        ((List.range' i f).foldl (cOuter act ngen) (idx, pts, par, lab, edges)).2.2.1,
        ((List.range' i f).foldl (cOuter act ngen) (idx, pts, par, lab, edges)).2.2.2.1) =
      gLoop act ngen id f i pts edges par lab idx := by
  intro f
  induction f with
  | zero => intro i pts edges par lab idx; rfl
  | succ f ih =>
    intro i pts edges par lab idx
    rw [List.range'_succ, List.foldl_cons, gLoop]
    by_cases hi : i < pts.size
    · have hc : cOuter act ngen (idx, pts, par, lab, edges) i =
          ((gStep act ngen id i (pts, par, lab, idx)).2.2.2.1,
            (gStep act ngen id i (pts, par, lab, idx)).1,
            (gStep act ngen id i (pts, par, lab, idx)).2.1,
            (gStep act ngen id i (pts, par, lab, idx)).2.2.1,
            edges.push (gStep act ngen id i (pts, par, lab, idx)).2.2.2.2) := by
        unfold cOuter gStep
        dsimp only
        simp only [hi, ↓reduceIte]
        rw [← List.range_eq_range', (cInner_fold act hi par lab idx ngen).1]
      rw [hc]
      simp only [hi, ↓reduceIte]
      generalize gStep act ngen id i (pts, par, lab, idx) = s
      obtain ⟨p, q, l, d, r⟩ := s
      exact ih (i + 1) p (edges.push r) q l d
    · have hc : cOuter act ngen (idx, pts, par, lab, edges) i = (idx, pts, par, lab, edges) := by
        unfold cOuter
        simp only [hi, ↓reduceIte]
      rw [hc]
      simp only [hi, ↓reduceIte]
      rw [cOuter_idle act ngen f (i + 1) _ (by dsimp only; omega)]

theorem native_natBfs_eq (act : ℕ → ℕ → ℕ) (ngen root fuel : ℕ) :
    Native.natBfs act ngen root fuel = gBfs act ngen id root fuel := by
  rw [native_natBfs_fold]
  exact cOuter_loop act ngen fuel 0 _ _ _ _ _

theorem orbitOK_of_reach {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root size : ℕ}
    (S : Finset ℕ) (hS : ∀ x, Reach act ngen root x ↔ x ∈ S) (hv : ∀ x ∈ S, valid x = true)
    (hsize : S.card = size) (hmin : ∀ x ∈ S, root ≤ x) :
    Native.orbitOK act ngen valid root size = true := by
  have hfuel : S.card ≤ size + 1 := by omega
  obtain ⟨hc, hmem, hsz, -⟩ := natBfs_spec (valid := valid) S hS hv hfuel
  rw [natBfs_eq] at hc hmem hsz
  simp only [Native.orbitOK, native_natBfs_eq, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨?_, hsz.trans hsize⟩, fun i hi => hmin _ ((hmem _).1 (Array.getElem_mem hi))⟩
  simp only [natCertOK, Bool.and_eq_true] at hc
  simp only [Native.natCertOK, Bool.and_eq_true]
  exact ⟨⟨hc.1.1, hc.1.2⟩, (chainLt_iff _).2 (of_decide_eq_true hc.2)⟩

end CFSG.KC.Bfs
