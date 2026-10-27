module

public import CFSG.Monster.B.Fischer.ArrCert
public import Std.Data.HashMap.Lemmas

public section

namespace CFSG.KS.ArrBfsSim

open CFSG.Monster.B.Fischer

@[expose] def pos (n : ℕ) (PA LA : ℕ → ℕ) (j : ℕ) : ℕ := n * PA j + LA j

structure Tables (n N : ℕ) (act : ℕ → Array ℕ → Array ℕ) (key : Array ℕ → ℕ) (Pt : ℕ → Array ℕ)
    (E : ℕ → ℕ → ℕ) (PA LA : ℕ → ℕ) : Prop where
  N2 : 2 ≤ N
  act : ∀ i < N, ∀ k < n, E i k < N ∧ act k (Pt i) = Pt (E i k)
  key : ∀ a < N, ∀ b < N, key (Pt a) = key (Pt b) → a = b
  pa0 : PA 0 = 0
  la0 : LA 0 = 0
  tree : ∀ j, 1 ≤ j → j < N → PA j < j ∧ LA j < n ∧ E (PA j) (LA j) = j
  mono : ∀ j, 1 ≤ j → j + 1 < N → pos n PA LA j < pos n PA LA (j + 1)
  first : ∀ i < N, ∀ k < n, E i k = 0 ∨ pos n PA LA (E i k) ≤ n * i + k

structure Inv (n N : ℕ) (key : Array ℕ → ℕ) (Pt : ℕ → Array ℕ) (PA LA : ℕ → ℕ) (s m : ℕ)
    (pts : Array (Array ℕ)) (par lab : Array ℕ) (idx : Std.HashMap ℕ ℕ) : Prop where
  pts_eq : pts = ((List.range m).map Pt).toArray
  par_eq : par = ((List.range m).map PA).toArray
  lab_eq : lab = ((List.range m).map LA).toArray
  m_pos : 1 ≤ m
  m_le : m ≤ N
  disc : ∀ y, 1 ≤ y → y < N → (y < m ↔ pos n PA LA y < s)
  hit : ∀ y < m, idx[key (Pt y)]? = some y
  miss : ∀ K, (∀ y < m, key (Pt y) ≠ K) → idx[K]? = none

@[expose] def stepA (act : ℕ → Array ℕ → Array ℕ) (key : Array ℕ → ℕ) (i : ℕ)
    (acc : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ) (k : ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  let (pts, par, lab, idx, row) := acc
  let y := act k pts[i]!
  let ky := key y
  match idx.get? ky with
  | some j => (pts, par, lab, idx, row.push j)
  | none => (pts.push y, par.push i, lab.push k, idx.insert ky pts.size, row.push pts.size)

theorem arrBfsStep_eq (act : ℕ → Array ℕ → Array ℕ) (ngen : ℕ) (key : Array ℕ → ℕ) (i : ℕ)
    (st : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ) :
    arrBfsStep act ngen key i st =
      (List.range ngen).foldl (stepA act key i) (st.1, st.2.1, st.2.2.1, st.2.2.2, #[]) := rfl

variable {n N : ℕ} {act : ℕ → Array ℕ → Array ℕ} {key : Array ℕ → ℕ} {Pt : ℕ → Array ℕ}
  {E : ℕ → ℕ → ℕ} {PA LA : ℕ → ℕ}

theorem toArray_get {α : Type} [Inhabited α] {p : ℕ → α} {m y : ℕ} (hy : y < m) :
    ((List.range m).map p).toArray[y]! = p y := by
  rw [getElem!_pos _ y (by simpa using hy)]
  simp

theorem toArray_size {α : Type} (p : ℕ → α) (m : ℕ) : ((List.range m).map p).toArray.size = m := by
  simp

theorem push_range {α : Type} (p : ℕ → α) (m : ℕ) :
    (((List.range m).map p).toArray).push (p m) = ((List.range (m + 1)).map p).toArray := by
  rw [List.range_succ, List.map_append]
  simp

theorem pos_mono (T : Tables n N act key Pt E PA LA) :
    ∀ y z, 1 ≤ y → y < z → z < N → pos n PA LA y < pos n PA LA z := by
  intro y z hy hyz hz
  induction z with
  | zero => omega
  | succ z ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hyz with h1 | h1
    · exact (ih h1 (by omega)).trans (T.mono z (by omega) hz)
    · subst h1
      exact T.mono y hy hz

theorem pos_lt (T : Tables n N act key Pt E PA LA) {y : ℕ} (hy : 1 ≤ y) (hyN : y < N) :
    pos n PA LA y < n * y := by
  obtain ⟨h1, h2, -⟩ := T.tree y hy hyN
  unfold pos
  have : n * (PA y + 1) ≤ n * y := Nat.mul_le_mul_left n h1
  rw [Nat.mul_succ] at this
  omega

theorem pos_inj {y i k : ℕ} (hn : 0 < n) (hLA : LA y < n) (hk : k < n)
    (h : pos n PA LA y = n * i + k) : PA y = i ∧ LA y = k := by
  unfold pos at h
  have h1 : (n * PA y + LA y) / n = PA y := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hLA, Nat.add_zero]
  have h2 : (n * i + k) / n = i := by
    rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hk, Nat.add_zero]
  have e1 : PA y = i := by rw [← h1, h, h2]
  refine ⟨e1, ?_⟩
  rw [e1] at h
  omega

theorem step_inv (T : Tables n N act key Pt E PA LA) {i k s m : ℕ} {pts : Array (Array ℕ)}
    {par lab row : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (H : Inv n N key Pt PA LA s m pts par lab idx) (hs : s = n * i + k) (hk : k < n)
    (hi : i < m) :
    ∃ m', m ≤ m' ∧ Inv n N key Pt PA LA (s + 1) m' (stepA act key i (pts, par, lab, idx, row) k).1
        (stepA act key i (pts, par, lab, idx, row) k).2.1
        (stepA act key i (pts, par, lab, idx, row) k).2.2.1
        (stepA act key i (pts, par, lab, idx, row) k).2.2.2.1 ∧
      (stepA act key i (pts, par, lab, idx, row) k).2.2.2.2 = row.push (E i k) := by
  have hn : 0 < n := by omega
  have hiN : i < N := Nat.lt_of_lt_of_le hi H.m_le
  have hsz : pts.size = m := by rw [H.pts_eq, toArray_size]
  have hpi : pts[i]! = Pt i := by rw [H.pts_eq, toArray_get hi]
  obtain ⟨hxN, hy⟩ := T.act i hiN k hk
  have hnew : ∀ y, 1 ≤ y → y < N → pos n PA LA y = s → y = E i k := by
    intro y hy1 hyN e
    obtain ⟨-, hLA, hE⟩ := T.tree y hy1 hyN
    obtain ⟨e1, e2⟩ := pos_inj hn hLA hk (hs ▸ e)
    rw [← hE, e1, e2]
  have hmono := pos_mono T
  unfold stepA
  simp only [hpi, hy, Std.HashMap.get?_eq_getElem?]
  by_cases hc : E i k < m
  · rw [H.hit _ hc]
    dsimp only
    refine ⟨m, le_refl m, ⟨H.pts_eq, H.par_eq, H.lab_eq, H.m_pos, H.m_le, fun y hy1 hyN => ?_,
      H.hit, H.miss⟩, rfl⟩
    rw [H.disc y hy1 hyN]
    constructor
    · intro h
      omega
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
      · exact h1
      · have := hnew y hy1 hyN h1
        subst this
        exact absurd ((H.disc _ hy1 hyN).1 hc) (by omega)
  · have hx0 : E i k ≠ 0 := by have := H.m_pos; omega
    have hfx : pos n PA LA (E i k) = s := by
      rcases T.first i hiN k hk with h | h
      · exact absurd h hx0
      · have := (H.disc (E i k) (by omega) hxN).not.1 hc
        omega
    have hxm : E i k = m := by
      by_contra hne
      have hmx : m < E i k := by omega
      have h1 := hmono m (E i k) H.m_pos hmx hxN
      have h2 := (H.disc m H.m_pos (by omega)).not.1 (Nat.lt_irrefl m)
      omega
    have hmiss : idx[key (Pt (E i k))]? = none :=
      H.miss _ fun y hy e => by
        have := T.key y (by have := H.m_le; omega) (E i k) hxN e
        omega
    rw [hmiss]
    dsimp only
    obtain ⟨-, hLA, -⟩ := T.tree (E i k) (by omega) hxN
    obtain ⟨hPAm, hLAm⟩ := pos_inj hn hLA hk (hs ▸ hfx)
    have hPAm' : PA m = i := hxm ▸ hPAm
    have hLAm' : LA m = k := hxm ▸ hLAm
    have hfx' : pos n PA LA m = s := hxm ▸ hfx
    have hmN : m < N := hxm ▸ hxN
    rw [hxm, hsz]
    refine ⟨m + 1, by omega, ⟨?_, ?_, ?_, by omega, by omega, fun y hy1 hyN => ?_, fun y hy => ?_,
      fun K hK => ?_⟩, rfl⟩
    · rw [H.pts_eq, push_range]
    · rw [H.par_eq, ← hPAm', push_range]
    · rw [H.lab_eq, ← hLAm', push_range]
    · constructor
      · intro h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
        · have := (H.disc y hy1 hyN).1 h1
          omega
        · rw [h1, hfx']
          omega
      · intro h
        by_contra hge
        have := hmono m y (by omega) (by omega) hyN
        omega
    · rw [Std.HashMap.getElem?_insert]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hy with h1 | h1
      · have hne : (key (Pt m) == key (Pt y)) = false := by
          rw [beq_eq_false_iff_ne]
          intro e
          have := T.key m hmN y (by have := H.m_le; omega) e
          omega
        rw [hne]
        exact H.hit y h1
      · subst h1
        rw [beq_self_eq_true]
        rfl
    · rw [Std.HashMap.getElem?_insert]
      have hne : (key (Pt m) == K) = false := by
        rw [beq_eq_false_iff_ne]
        exact hK m (Nat.lt_succ_self m)
      rw [hne]
      exact H.miss K fun y hy => hK y (by omega)

theorem fold_inv (T : Tables n N act key Pt E PA LA) {i : ℕ} :
    ∀ k ≤ n, ∀ {m : ℕ} {pts : Array (Array ℕ)} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ},
    Inv n N key Pt PA LA (n * i) m pts par lab idx → i < m →
    ∃ m', i < m' ∧
      Inv n N key Pt PA LA (n * i + k) m' ((List.range k).foldl (stepA act key i)
          (pts, par, lab, idx, #[])).1
        ((List.range k).foldl (stepA act key i) (pts, par, lab, idx, #[])).2.1
        ((List.range k).foldl (stepA act key i) (pts, par, lab, idx, #[])).2.2.1
        ((List.range k).foldl (stepA act key i) (pts, par, lab, idx, #[])).2.2.2.1 ∧
      ((List.range k).foldl (stepA act key i) (pts, par, lab, idx, #[])).2.2.2.2 =
        ((List.range k).map (E i)).toArray
  | 0, _, m, pts, par, lab, idx, H, hi => ⟨m, hi, by simpa using H, rfl⟩
  | k + 1, hk, m, pts, par, lab, idx, H, hi => by
    obtain ⟨m1, hi1, H1, hrow⟩ := fold_inv T k (by omega) H hi
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hacc : (List.range k).foldl (stepA act key i) (pts, par, lab, idx, #[]) = acc at H1 hrow
    obtain ⟨a1, a2, a3, a4, a5⟩ := acc
    obtain ⟨m2, hm12, H2, hrow2⟩ := step_inv (row := a5) T H1 rfl (by omega) hi1
    refine ⟨m2, Nat.lt_of_lt_of_le hi1 hm12, by simpa [Nat.add_assoc] using H2, ?_⟩
    rw [hrow2]
    simp only at hrow
    rw [hrow, List.map_append]
    simp

theorem m_full (T : Tables n N act key Pt E PA LA) {m : ℕ} {pts : Array (Array ℕ)}
    {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (H : Inv n N key Pt PA LA (n * N) m pts par lab idx) : m = N := by
  have hN := T.N2
  have hy := pos_lt T (y := N - 1) (by omega) (by omega)
  have hle : n * (N - 1) ≤ n * N := Nat.mul_le_mul_left n (by omega)
  have h := (H.disc (N - 1) (by omega) (by omega)).2 (by omega)
  have := H.m_le
  omega

@[expose] def cert (n N : ℕ) (Pt : ℕ → Array ℕ) (E : ℕ → ℕ → ℕ) (PA LA : ℕ → ℕ) : ArrCert :=
  ⟨((List.range N).map Pt).toArray,
    ((List.range N).map fun h => ((List.range n).map (E h)).toArray).toArray,
    ((List.range N).map PA).toArray, ((List.range N).map LA).toArray⟩

theorem loop_eq (T : Tables n N act key Pt E PA LA) :
    ∀ fuel i {m : ℕ} {pts edges : Array (Array ℕ)} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ},
    Inv n N key Pt PA LA (n * i) m pts par lab idx → i ≤ N → N - i ≤ fuel →
    edges = ((List.range i).map fun h => ((List.range n).map (E h)).toArray).toArray →
    arrBfsLoop act n key fuel i pts edges par lab idx = cert n N Pt E PA LA
  | 0, i, m, pts, edges, par, lab, idx, H, hiN, hf, he => by
    have hi : i = N := by omega
    subst hi
    have hm := m_full T H
    subst hm
    unfold arrBfsLoop
    rw [H.pts_eq, H.par_eq, H.lab_eq, he]
    rfl
  | fuel + 1, i, m, pts, edges, par, lab, idx, H, hiN, hf, he => by
    have hsz : pts.size = m := by rw [H.pts_eq, toArray_size]
    unfold arrBfsLoop
    by_cases hi : i < m
    · rw [if_pos (by rw [hsz]; exact hi), arrBfsStep_eq]
      obtain ⟨m', hi', H', hrow⟩ := fold_inv (act := act) T n le_rfl H hi
      dsimp only at H' hrow ⊢
      generalize (List.range n).foldl (stepA act key i) (pts, par, lab, idx, #[]) = acc at H' hrow ⊢
      obtain ⟨a1, a2, a3, a4, a5⟩ := acc
      dsimp only at H' hrow ⊢
      refine loop_eq T fuel (i + 1) (by rw [Nat.mul_succ]; exact H') (by
        have := H.m_le
        omega) (by omega) ?_
      rw [he, hrow, List.range_succ, List.map_append]
      simp
    · rw [if_neg (by rw [hsz]; exact hi)]
      have hiN' : i = N := by
        by_contra hne
        apply hi
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · rw [h0]
          exact H.m_pos
        · exact (H.disc i h0 (by omega)).2 (pos_lt T h0 (by omega))
      subst hiN'
      have hm := m_full T H
      subst hm
      rw [H.pts_eq, H.par_eq, H.lab_eq, he]
      rfl

theorem arrBfs_eq (T : Tables n N act key Pt E PA LA) {fuel : ℕ} (hfuel : N ≤ fuel) :
    arrBfs act n key (Pt 0) fuel = cert n N Pt E PA LA := by
  unfold arrBfs
  have hN := T.N2
  refine loop_eq T fuel 0 ⟨by simp, by simp [T.pa0], by simp [T.la0], le_refl 1, by omega,
    fun y hy1 _ => by simp only [Nat.mul_zero]; omega, fun y hy => ?_, fun K hK => ?_⟩
    (by omega) (by omega) (by simp)
  · have : y = 0 := by omega
    subst this
    exact Std.HashMap.getElem?_insert_self
  · rw [Std.HashMap.getElem?_insert]
    have hne : (key (Pt 0) == K) = false := by
      rw [beq_eq_false_iff_ne]
      exact hK 0 (by omega)
    rw [hne]
    exact Std.HashMap.getElem?_empty

end CFSG.KS.ArrBfsSim

end
