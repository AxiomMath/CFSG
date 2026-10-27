module

public import CFSG.Certificates.Kernel.MonsterB.NatBfsSound
public import Certificates.Data.Kernel.MonsterB.BfsReplay

public section

namespace CFSG.KC.Bfs

open CFSG.Monster.B.TwoA.Census

variable {α : Type} [Inhabited α]

@[expose] def Pre (pts L : Array α) : Prop :=
  pts.size ≤ L.size ∧ ∀ j < pts.size, pts[j]! = L[j]!

section Replay

variable {act : ℕ → α → α} {ngen : ℕ} {key : α → ℕ} {T : Finset α} {root : α}
  {L : Array α} {E : ℕ → ℕ → ℕ}

theorem gF_replay (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    {i k m' : ℕ} {pts : Array α} {par lab row : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hp : Pre pts L) (hi : i < pts.size)
    (hk : k < ngen) (h : rStep E i (some pts.size) k = some m') :
    (gF act key i (pts, par, lab, idx, row) k).1.size = m' ∧
      Pre (gF act key i (pts, par, lab, idx, row) k).1 L := by
  have hiL : i < L.size := lt_of_lt_of_le hi hp.1
  obtain ⟨hEL, hEe⟩ := hE i hiL k hk
  have hy : act k pts[i]! = L[E i k]! := by rw [hp.2 i hi, hEe]
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

theorem gFold_replay (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    {i : ℕ} {pts : Array α} {par lab : Array ℕ} {idx : Std.HashMap ℕ ℕ}
    (hc : Core act ngen key T root pts par lab idx) (hp : Pre pts L) (hi : i < pts.size) :
    ∀ n ≤ ngen, ∀ m', (List.range n).foldl (rStep E i) (some pts.size) = some m' →
      ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).1.size = m' ∧
        Pre ((List.range n).foldl (gF act key i) (pts, par, lab, idx, #[])).1 L := by
  intro n
  induction n with
  | zero =>
    intro _ m' h
    cases h
    exact ⟨rfl, hp⟩
  | succ n ih =>
    intro hn m' h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at h ⊢
    obtain ⟨hc', he, -⟩ := gFold_spec hT hkey hc hi n (by omega) _ rfl
    cases ho : (List.range n).foldl (rStep E i) (some pts.size) with
    | none =>
      rw [ho] at h
      nomatch h
    | some m'' =>
      rw [ho] at h
      obtain ⟨hs, hp'⟩ := ih (by omega) m'' ho
      generalize (List.range n).foldl (gF act key i) (pts, par, lab, idx, #[]) = s at hc' he hs hp'
      obtain ⟨p, q, l, d, r⟩ := s
      dsimp only at hs hp' hc' he
      subst hs
      exact gF_replay hkeyL hE hc' hp' (lt_of_lt_of_le hi he.1) (by omega) h

theorem gLoop_replay (hT : ∀ x ∈ T, ∀ k < ngen, act k x ∈ T)
    (hkey : ∀ x ∈ T, ∀ y ∈ T, key x = key y → x = y)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!) :
    ∀ (f i c : ℕ) (pts : Array α) (edges : Array (Array ℕ)) (par lab : Array ℕ)
      (idx : Std.HashMap ℕ ℕ), Core act ngen key T root pts par lab idx → i ≤ pts.size →
      Pre pts L → i + c = L.size → replayLoop E ngen c i pts.size = some L.size →
      T.card ≤ i + f →
      (gLoop act ngen key f i pts edges par lab idx).1.size = L.size ∧
        Pre (gLoop act ngen key f i pts edges par lab idx).1 L := by
  have stop : ∀ (i c : ℕ), replayLoop E ngen c i i = some L.size → i = L.size := by
    intro i c h
    cases c with
    | zero =>
      simp only [replayLoop, Option.some.injEq] at h
      exact h
    | succ c =>
      simp only [replayLoop, Nat.lt_irrefl, ↓reduceIte] at h
      nomatch h
  intro f
  induction f with
  | zero =>
    intro i c pts edges par lab idx hc hi hp hic hr hf
    have : i = pts.size := le_antisymm hi (by have := hc.size_le; omega)
    subst this
    exact ⟨stop _ c hr, hp⟩
  | succ f ih =>
    intro i c pts edges par lab idx hc hi hp hic hr hf
    rw [gLoop]
    split
    · next hlt =>
      cases c with
      | zero =>
        have := hp.1
        omega
      | succ c =>
        simp only [replayLoop, hlt, ↓reduceIte] at hr
        cases hrow : rRow E ngen i pts.size with
        | none =>
          rw [hrow] at hr
          nomatch hr
        | some m' =>
          rw [hrow] at hr
          obtain ⟨hs, hp'⟩ := gFold_replay hT hkey hkeyL hE hc hp hlt ngen le_rfl m' hrow
          obtain ⟨hc', hx, -⟩ := gStep_spec hT hkey hc hlt
          have hs' : (gStep act ngen key i (pts, par, lab, idx)).1.size = m' := hs
          have hp'' : Pre (gStep act ngen key i (pts, par, lab, idx)).1 L := hp'
          generalize gStep act ngen key i (pts, par, lab, idx) = s at hc' hx hs' hp''
          obtain ⟨p, q, l, d, r⟩ := s
          dsimp only at hs' hp'' hc' hx
          subst hs'
          exact ih _ c _ _ _ _ _ hc' (by have := hx.1; omega) hp'' (by omega) hr (by omega)
    · next hge =>
      have : i = pts.size := by omega
      subst this
      exact ⟨stop _ c hr, hp⟩

theorem gBfs_eq_of_replay [DecidableEq α] (hL : 0 < L.size) (h0 : L[0]! = root)
    (hkeyL : ∀ a < L.size, ∀ b < L.size, key L[a]! = key L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    (hrep : replayOK E ngen L.size = true) {fuel : ℕ} (hfuel : L.size ≤ fuel) :
    (gBfs act ngen key root fuel).1 = L := by
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
  have hr : replayLoop E ngen L.size 0 1 = some L.size := by
    simpa [replayOK] using hrep
  obtain ⟨hs, hp⟩ := gLoop_replay hT hkey hkeyL hE fuel 0 L.size _ #[] _ _ _
    (core_init hroot) (Nat.zero_le _) ⟨hL, fun j hj => by
      have : j = 0 := by simpa using hj
      subst this
      exact h0.symm⟩ (by omega) hr (by omega)
  refine Array.ext hs fun j h1 h2 => ?_
  rw [← getElem!_pos _ j h1, ← getElem!_pos L j h2]
  exact hp.2 j h1

end Replay

theorem natBfs_of_replay {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root fuel : ℕ}
    {L : Array ℕ} {E : ℕ → ℕ → ℕ} (hL : 0 < L.size) (h0 : L[0]! = root)
    (hinj : ∀ a < L.size, ∀ b < L.size, L[a]! = L[b]! → a = b)
    (hE : ∀ i < L.size, ∀ k < ngen, E i k < L.size ∧ L[E i k]! = act k L[i]!)
    (hrep : replayOK E ngen L.size = true) (hv : ∀ j < L.size, valid L[j]! = true)
    (hfuel : L.size ≤ fuel) :
    (natBfs act ngen root fuel).pts = L ∧
      natCertOK act ngen valid root (natBfs act ngen root fuel) = true := by
  have memL : ∀ x, x ∈ L.toList.toFinset ↔ ∃ a < L.size, L[a]! = x := by
    intro x
    rw [List.mem_toFinset, Array.mem_toList_iff, Array.mem_iff_getElem]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, getElem!_pos L a ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, (getElem!_pos L a ha).symm⟩
  refine ⟨?_, natCertOK_gBfs (T := L.toList.toFinset) ((memL _).2 ⟨0, hL, h0⟩) ?_ ?_
    (le_trans (List.toFinset_card_le _) (by rw [Array.length_toList]; exact hfuel))⟩
  · rw [natBfs_eq]
    exact gBfs_eq_of_replay (key := id) hL h0 hinj hE hrep hfuel
  · intro x hx k hk
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    exact (memL _).2 ⟨_, (hE a ha k hk).1, (hE a ha k hk).2⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := (memL x).1 hx
    exact hv a ha

end CFSG.KC.Bfs
