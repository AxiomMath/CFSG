module

public import CFSG.Certificates.Kernel.MonsterB.BfsReplaySound
public import Certificates.Data.Kernel.MonsterB.BfsReplayT

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

section Weak

variable {E : ℕ → ℕ → ℕ} {P Lb : ℕ → ℕ}

theorem rStepT_rStep {i k m' : ℕ} {o : Option ℕ} (h : rStepT E P Lb i o k = some m') :
    rStep E i o k = some m' := by
  cases o with
  | none => exact absurd h (by simp [rStepT])
  | some m =>
    simp only [rStepT] at h
    simp only [rStep]
    by_cases h1 : E i k < m
    · rw [ite_eq_left h1] at h ⊢
      exact h
    · rw [ite_eq_right h1] at h ⊢
      by_cases h2 : E i k = m ∧ P m = i ∧ Lb m = k
      · rw [ite_eq_left h2] at h
        rw [ite_eq_left h2.1]
        exact h
      · rw [ite_eq_right h2] at h
        exact absurd h (by simp)

theorem foldl_rStepT_none (i : ℕ) : ∀ l : List ℕ, l.foldl (rStepT E P Lb i) none = none
  | [] => rfl
  | _ :: l => foldl_rStepT_none i l

theorem foldl_rStepT {i m' : ℕ} : ∀ (l : List ℕ) (o : Option ℕ),
    l.foldl (rStepT E P Lb i) o = some m' → l.foldl (rStep E i) o = some m'
  | [], _, h => h
  | k :: l, o, h => by
    simp only [List.foldl_cons] at h ⊢
    cases hk : rStepT E P Lb i o k with
    | none =>
      rw [hk, foldl_rStepT_none] at h
      exact absurd h (by simp)
    | some y =>
      rw [hk] at h
      rw [rStepT_rStep hk]
      exact foldl_rStepT l _ h

theorem replayLoopT_replayLoop {ngen r : ℕ} : ∀ (c i m : ℕ),
    replayLoopT E P Lb ngen c i m = some r → replayLoop E ngen c i m = some r
  | 0, _, _, h => h
  | c + 1, i, m, h => by
    simp only [replayLoopT] at h
    simp only [replayLoop]
    by_cases hi : i < m
    · rw [ite_eq_left hi] at h ⊢
      cases hr : rRowT E P Lb ngen i m with
      | none =>
        rw [hr] at h
        exact absurd h (by simp)
      | some m' =>
        rw [hr] at h
        rw [rRow, foldl_rStepT _ _ hr]
        exact replayLoopT_replayLoop c (i + 1) m' h
    · rw [ite_eq_right hi] at h
      exact absurd h (by simp)

theorem replayTOK_replayOK {ngen n : ℕ} (h : replayTOK E P Lb ngen n = true) :
    replayOK E ngen n = true := by
  simp only [replayTOK, beq_iff_eq] at h
  simp only [replayOK, beq_iff_eq]
  exact replayLoopT_replayLoop n 0 1 h

end Weak

variable {α : Type} [Inhabited α]

def PreT (par lab : Array ℕ) (P Lb : ℕ → ℕ) : Prop :=
  ∀ j, 0 < j → j < par.size → j < lab.size → par[j]! = P j ∧ lab[j]! = Lb j

section Replay

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}
  {L : Array α} {E : ℕ → ℕ → ℕ} {P Lb : ℕ → ℕ}

theorem gF_replayT (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    {i k m' : ℕ} {pts : Array α} {par lab row : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hp : Pre pts L) (hpp : PreT par lab P Lb)
    (hi : i < pts.size) (hk : k < ngen) (h : rStepT E P Lb i (some pts.size) k = some m') :
    PreT (gF act key i (pts, par, lab, idx, row) k).2.1 (gF act key i (pts, par, lab, idx, row) k).2.2.1
      P Lb := by
  have hiL : i < L.size := lt_of_lt_of_le hi hp.1
  obtain ⟨hEL, hEe⟩ := hE i hiL k hk
  have hy : act k pts[i]! = L[E i k]! := by rw [hp.2 i hi, hEe]
  simp only [rStepT] at h
  simp only [gF]
  split
  · exact hpp
  · next heq =>
    dsimp only
    rw [Std.HashMap.get?_eq_getElem?] at heq
    by_cases hlt : E i k < pts.size
    · have h1 := hc.idx_get _ hlt
      rw [hp.2 _ hlt, ← hy, heq] at h1
      nomatch h1
    · rw [ite_eq_right hlt] at h
      by_cases hc' : E i k = pts.size ∧ P pts.size = i ∧ Lb pts.size = k
      · intro j hj0 hj1 hj2
        rw [Array.size_push] at hj1 hj2
        have hps : par.size = pts.size := hc.par_size
        have hls : lab.size = pts.size := hc.lab_size
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj1 with hj | rfl
        · rw [push_get_lt _ _ hj, push_get_lt _ _ (by omega)]
          exact hpp j hj0 hj (by omega)
        · rw [push_get_size, push_get_of_eq _ _ (by omega), hps]
          exact ⟨hc'.2.1.symm, hc'.2.2.symm⟩
      · rw [ite_eq_right hc'] at h
        nomatch h

theorem foldl_some_of {i m' : ℕ} {n : ℕ} {o : Option ℕ}
    (h : (List.range n).foldl (rStepT E P Lb i) o = some m') :
    (List.range n).foldl (rStep E i) o = some m' := foldl_rStepT _ _ h

theorem gFold_replayT (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    {i : ℕ} {pts : Array α} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hp : Pre pts L) (hpp : PreT par lab P Lb)
    (hi : i < pts.size) :
    ∀ n ≤ ngen, ∀ m', (List.range n).foldl (rStepT E P Lb i) (some pts.size) = some m' →
      PreT ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).2.1
        ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).2.2.1 P Lb := by
  intro n
  induction n with
  | zero => intro _ _ _; exact hpp
  | succ n ih =>
    intro hn m' h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    obtain ⟨hc', he, -⟩ := gFold_spec hT hkey hc hi n (by omega) _ rfl
    cases ho : (List.range n).foldl (rStepT E P Lb i) (some pts.size) with
    | none =>
      rw [ho] at h
      nomatch h
    | some m'' =>
      rw [ho] at h
      have hpp' := ih (by omega) m'' ho
      obtain ⟨hs, hp'⟩ := gFold_replay hT hkey hkeyL hE hc hp hi n (by omega) m'' (foldl_some_of ho)
      generalize (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) = s at hc' he hs hp' hpp'
      obtain ⟨p, q, l, d, r⟩ := s
      dsimp only at hs hp' hc' he hpp'
      subst hs
      exact gF_replayT hE hc' hp' hpp' (lt_of_lt_of_le hi he.1) (by omega) h

theorem gLoop_replayT (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!) :
    ∀ (f i c : ℕ) (pts : Array α) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), Core act ngen key T root pts par lab idx → i ≤ pts.size →
      Pre pts L → PreT par lab P Lb → i + c = L.size →
      replayLoopT E P Lb ngen c i pts.size = some L.size → T.card ≤ i + f →
      PreT (gLoop act ngen key f i pts edges par lab idx).2.2.1
        (gLoop act ngen key f i pts edges par lab idx).2.2.2 P Lb := by
  intro f
  induction f with
  | zero =>
    intro i c pts edges par lab idx _ _ _ hpp _ _ _
    exact hpp
  | succ f ih =>
    intro i c pts edges par lab idx hc hi hp hpp hic hr hf
    rw [gLoop]
    split
    · next hlt =>
      cases c with
      | zero =>
        have := hp.1
        omega
      | succ c =>
        simp only [replayLoopT, hlt, ↓reduceIte] at hr
        cases hrow : rRowT E P Lb ngen i pts.size with
        | none =>
          rw [hrow] at hr
          nomatch hr
        | some m' =>
          rw [hrow] at hr
          obtain ⟨hs, hp'⟩ := gFold_replay hT hkey hkeyL hE hc hp hlt ngen le_rfl m'
            (foldl_some_of hrow)
          have hpp' := gFold_replayT hT hkey hkeyL hE hc hp hpp hlt ngen le_rfl m' hrow
          obtain ⟨hc', hx, -⟩ := gStep_spec hT hkey hc hlt
          have hs' : (gStep act ngen key i (pts, par, lab, idx)).1.size = m' := hs
          have hp'' : Pre (gStep act ngen key i (pts, par, lab, idx)).1 L := hp'
          have hpp'' : PreT (gStep act ngen key i (pts, par, lab, idx)).2.1
              (gStep act ngen key i (pts, par, lab, idx)).2.2.1 P Lb := hpp'
          generalize gStep act ngen key i (pts, par, lab, idx) = s at hc' hx hs' hp'' hpp''
          obtain ⟨p, q, l, d, r⟩ := s
          dsimp only at hs' hp'' hc' hx hpp''
          subst hs'
          exact ih _ c _ _ _ _ _ hc' (by have := hx.1; omega) hp'' hpp'' (by omega) hr (by omega)
    · exact hpp

theorem gBfs_tree_of_replayT [DecidableEq α] (hL : 0 < L.size) (h0 : L[0]! = root)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    (hrep : replayTOK E P Lb ngen L.size = true) {fuel : ℕ} (hfuel : L.size ≤ fuel) :
    ∀ j, 0 < j → j < L.size → (gBfs act ngen key root fuel).2.2.1[j]! = P j ∧
      (gBfs act ngen key root fuel).2.2.2[j]! = Lb j := by
  have memL : ∀ x, x ∈ L.toList.toFinset ↔ ∃ a < L.size, L[a]! = x := by
    intro x
    rw [List.mem_toFinset, Array.mem_toList_iff, Array.mem_iff_getElem]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, getElem!_pos L a ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (getElem!_pos L a ha).symm⟩
  have hroot : root ∈ L.toList.toFinset := (memL _).2 ⟨0, hL, h0⟩
  have hT : ∀ x ∈ L.toList.toFinset, ∀ k < ngen, act k x ∈ L.toList.toFinset := by
    intro x hx k hk
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    exact (memL _).2 ⟨_, (hE a ha k hk).1, (hE a ha k hk).2⟩
  have hkey : ∀ x ∈ L.toList.toFinset, ∀ y ∈ L.toList.toFinset, key x = key y → x = y := by
    intro x hx y hy e
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    obtain ⟨b, hb, rfl⟩ := (memL y).1 hy
    rw [hkeyL a ha b hb e]
  have hcard : L.toList.toFinset.card ≤ fuel :=
    le_trans (List.toFinset_card_le _) (by rw [Array.length_toList]; exact hfuel)
  have hr : replayLoopT E P Lb ngen L.size 0 1 = some L.size := by
    simpa [replayTOK] using hrep
  have hpp := gLoop_replayT (P := P) (Lb := Lb) hT hkey hkeyL hE fuel 0 L.size _ #[] _ _ _
    (core_init hroot) (Nat.zero_le _) ⟨hL, fun j hj => by
      have : j = 0 := by simpa using hj
      subst this
      exact h0.symm⟩ (fun j hj0 hj1 _ => by simp at hj1; omega) (by omega) hr (by omega)
  have hpts := gBfs_eq_of_replay (act := act) (key := key) hL h0 hkeyL hE (replayTOK_replayOK hrep)
    hfuel
  obtain ⟨⟨idx, hc⟩, -, -⟩ := gBfs_out (act := act) (key := key) (fuel := fuel) hroot hT hkey hcard
  intro j hj0 hj
  have hs : (gBfs act ngen key root fuel).1.size = L.size := by rw [hpts]
  have h1 : j < (gBfs act ngen key root fuel).2.2.1.size := by rw [hc.par_size, hs]; exact hj
  have h2 : j < (gBfs act ngen key root fuel).2.2.2.size := by rw [hc.lab_size, hs]; exact hj
  exact hpp j hj0 h1 h2

end Replay

theorem natBfs_tree_of_replayT {act : ℕ → ℕ → ℕ} {ngen root fuel : ℕ} {L : Array ℕ}
    {E : ℕ → ℕ → ℕ} {P Lb : ℕ → ℕ} (hL : 0 < L.size) (h0 : L[0]! = root)
    (hinj : ∀ a < L.size, ∀ b < L.size, L[a]! = L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    (hrep : replayTOK E P Lb ngen L.size = true) (hfuel : L.size ≤ fuel) :
    ∀ j, 0 < j → j < L.size → (natBfs act ngen root fuel).par[j]! = P j ∧
      (natBfs act ngen root fuel).lab[j]! = Lb j := by
  rw [natBfs_eq]
  exact gBfs_tree_of_replayT (key := id) hL h0 hinj hE hrep hfuel

end CFSG.KC.Bfs

end
