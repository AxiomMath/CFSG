module

public import Certificates.Data.Kernel.MonsterB.NatBfsL

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

@[expose] def IdxRel (idx : Std.HashMap ℕ ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ y, idx.get? y = L.lookup y

theorem idxRel_insert {idx : Std.HashMap ℕ ℕ} {L : List (ℕ × ℕ)} (h : IdxRel idx L) (y v : ℕ) :
    IdxRel (idx.insert y v) ((y, v) :: L) := by
  intro z
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  by_cases hz : y = z
  · subst hz
    simp [List.lookup]
  · have h1 : (y == z) = false := by simp [hz]
    have h2 : (z == y) = false := by simp [Ne.symm hz]
    rw [h1, if_neg (by simp), ← Std.HashMap.get?_eq_getElem?, h z]
    simp [List.lookup, h2]

theorem idxRel_init (root : ℕ) :
    IdxRel ((∅ : Std.HashMap ℕ ℕ).insert root 0) [(root, 0)] :=
  idxRel_insert (fun y => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty]; rfl)
    root 0

@[expose] def natBfsFH (act : ℕ → ℕ → ℕ) (i : ℕ)
    (acc : Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ) (k : ℕ) :
    Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ :=
  let (pts, par, lab, idx, row) := acc
  let y := act k pts[i]!
  match idx.get? y with
  | some j => (pts, par, lab, idx, row.push j)
  | none => (pts.push y, par.push i, lab.push k, idx.insert y pts.size, row.push pts.size)

theorem natBfsStep_eq_fold (act : ℕ → ℕ → ℕ) (ngen i : ℕ)
    (st : Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ) :
    natBfsStep act ngen i st =
      (List.range ngen).foldl (natBfsFH act i) (st.1, st.2.1, st.2.2.1, st.2.2.2, #[]) :=
  rfl

@[expose] def AccRel (a : Array ℕ × Array ℕ × Array ℕ × Std.HashMap ℕ ℕ × Array ℕ)
    (b : Array ℕ × Array ℕ × Array ℕ × List (ℕ × ℕ) × Array ℕ) : Prop :=
  a.1 = b.1 ∧ a.2.1 = b.2.1 ∧ a.2.2.1 = b.2.2.1 ∧ IdxRel a.2.2.2.1 b.2.2.2.1 ∧
    a.2.2.2.2 = b.2.2.2.2

theorem accRel_step (act : ℕ → ℕ → ℕ) (i k : ℕ) :
    ∀ a b, AccRel a b → AccRel (natBfsFH act i a k) (natBfsFL act i b k) := by
  rintro ⟨pts, par, lab, idx, row⟩ ⟨pts', par', lab', L, row'⟩ ⟨e1, e2, e3, h, e5⟩
  dsimp only at e1 e2 e3 h e5
  subst e1 e2 e3 e5
  have hy := h (act k pts[i]!)
  unfold natBfsFH natBfsFL
  dsimp only
  rw [← hy]
  cases idx.get? (act k pts[i]!) with
  | some j => exact ⟨rfl, rfl, rfl, h, rfl⟩
  | none => exact ⟨rfl, rfl, rfl, idxRel_insert h _ _, rfl⟩

theorem accRel_fold (act : ℕ → ℕ → ℕ) (i : ℕ) :
    ∀ (ks : List ℕ) a b, AccRel a b →
      AccRel (ks.foldl (natBfsFH act i) a) (ks.foldl (natBfsFL act i) b)
  | [], _, _, h => h
  | k :: ks, a, b, h => accRel_fold act i ks _ _ (accRel_step act i k a b h)

theorem natBfsLoop_eq_L (act : ℕ → ℕ → ℕ) (ngen : ℕ) :
    ∀ (fuel i : ℕ) (pts : Array ℕ) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ) (L : List (ℕ × ℕ)), IdxRel idx L →
      natBfsLoop act ngen fuel i pts edges par lab idx =
        natBfsLoopL act ngen fuel i pts edges par lab L
  | 0, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, i, pts, edges, par, lab, idx, L, h => by
    rw [natBfsLoop, natBfsLoopL]
    split
    · have hr := accRel_fold act i (List.range ngen) (pts, par, lab, idx, #[])
        (pts, par, lab, L, #[]) ⟨rfl, rfl, rfl, h, rfl⟩
      rw [natBfsStep_eq_fold]
      unfold natBfsStepL
      dsimp only at hr ⊢
      generalize (List.range ngen).foldl (natBfsFH act i) (pts, par, lab, idx, #[]) = s at hr ⊢
      generalize (List.range ngen).foldl (natBfsFL act i) (pts, par, lab, L, #[]) = t at hr ⊢
      obtain ⟨a1, a2, a3, a4, a5⟩ := s
      obtain ⟨b1, b2, b3, b4, b5⟩ := t
      obtain ⟨e1, e2, e3, h4, e5⟩ := hr
      dsimp only at e1 e2 e3 h4 e5 ⊢
      subst e1 e2 e3 e5
      exact natBfsLoop_eq_L act ngen fuel _ _ _ _ _ _ _ h4
    · rfl

theorem natBfs_eq_natBfsL (act : ℕ → ℕ → ℕ) (ngen root fuel : ℕ) :
    natBfs act ngen root fuel = natBfsL act ngen root fuel :=
  natBfsLoop_eq_L act ngen fuel 0 _ _ _ _ _ _ (idxRel_init root)

theorem natBfs_eq_natBfsL_fun : @natBfs = @natBfsL :=
  funext fun act => funext fun ngen => funext fun root => funext fun fuel =>
    natBfs_eq_natBfsL act ngen root fuel
end CFSG.KC.Bfs
