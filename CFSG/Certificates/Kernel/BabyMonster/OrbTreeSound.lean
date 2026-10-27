module

public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbTree
public import CFSG.Certificates.Kernel.MonsterB.BfsCore

public section

namespace CFSG.KC.BM.OrbT

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.Bfs

@[expose] noncomputable def ptsF (n S : ℕ) : Finset ℕ := ((List.range n).map (fld32 S)).toFinset

theorem mem_ptsF {n S x : ℕ} : x ∈ ptsF n S ↔ ∃ i < n, fld32 S i = x := by
  simp [ptsF]

theorem andB_eq_true {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem allLt_eq_true {n : ℕ} {f : ℕ → Bool} : allLt n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change andB (allLt n f) (f n) = true ↔ _
    rw [andB_eq_true, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem blt_iff {a b : ℕ} : Nat.blt a b = true ↔ a < b := Iff.of_eq Nat.blt_eq

theorem beq_iff {a b : ℕ} : Nat.beq a b = true ↔ a = b := Iff.of_eq Nat.beq_eq

theorem incPt_spec {n bound S i : ℕ} (h : incPt n bound S i = true) :
    fld32 S i < bound ∧ (i + 1 < n → fld32 S i < fld32 S (i + 1)) := by
  unfold incPt at h
  rw [andB_eq_true, blt_iff] at h
  refine ⟨h.1, fun hi => ?_⟩
  have h2 := h.2
  have hb : Nat.blt (Nat.succ i) n = true := blt_iff.2 hi
  rw [hb] at h2
  exact blt_iff.1 h2

theorem incPt_mono {n bound S : ℕ} (h : ∀ i < n, incPt n bound S i = true) :
    ∀ j < n, ∀ i < j, fld32 S i < fld32 S j := by
  intro j
  induction j with
  | zero => exact fun _ i hi => absurd hi (Nat.not_lt_zero i)
  | succ j ih =>
    intro hj i hi
    have hs := (incPt_spec (h j (by omega))).2 hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact lt_trans (ih (by omega) i hi) hs
    · exact hs

theorem closPt_spec {act : ℕ → ℕ → ℕ} {ngen n S E i : ℕ} (h : closPt act ngen n S E i = true)
    {k : ℕ} (hk : k < ngen) : ∃ j < n, act k (fld32 S i) = fld32 S j := by
  unfold closPt at h
  have h' := allLt_eq_true.1 h k hk
  unfold imgOK at h'
  rw [andB_eq_true, blt_iff, beq_iff] at h'
  exact ⟨_, h'.1, h'.2⟩

theorem treePt_spec {act : ℕ → ℕ → ℕ} {ngen n r S T i : ℕ} (h : treePt act ngen n r S T i = true) :
    (tDep (fld32 T i) = 0 → i = r) ∧
      (tDep (fld32 T i) ≠ 0 → tPar (fld32 T i) < n ∧ tLab (fld32 T i) < ngen ∧
        tDep (fld32 T (tPar (fld32 T i))) + 1 = tDep (fld32 T i) ∧
        act (tLab (fld32 T i)) (fld32 S (tPar (fld32 T i))) = fld32 S i) := by
  unfold treePt at h
  by_cases h0 : tDep (fld32 T i) = 0
  · have hb : Nat.beq (tDep (fld32 T i)) 0 = true := beq_iff.2 h0
    rw [hb] at h
    exact ⟨fun _ => beq_iff.1 h, fun h' => absurd h0 h'⟩
  · have hb : Nat.beq (tDep (fld32 T i)) 0 = false :=
      Bool.eq_false_iff.2 fun e => h0 (beq_iff.1 e)
    rw [hb] at h
    unfold edgeOK at h
    simp only [andB_eq_true, blt_iff, beq_iff] at h
    exact ⟨fun e => absurd e h0, fun _ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

theorem orbT_reach {act act' : ℕ → ℕ → ℕ} {ngen n root r bound S E T : ℕ}
    (hact : ∀ k < ngen, ∀ x, act k x = act' k x)
    (hinc : ∀ i < n, incPt n bound S i = true)
    (hclos : ∀ i < n, closPt act' ngen n S E i = true)
    (htree : ∀ i < n, treePt act' ngen n r S T i = true)
    (hr : r < n) (hroot : fld32 S r = root) :
    (∀ x, Reach act ngen root x ↔ x ∈ ptsF n S) ∧ (ptsF n S).card = n ∧
      ∀ x ∈ ptsF n S, x < bound := by
  have hreach : ∀ d, ∀ i < n, tDep (fld32 T i) = d → Reach act ngen root (fld32 S i) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      rw [(treePt_spec (htree i hi)).1 hd, hroot]
      exact Reach.root
    | succ d ih =>
      intro i hi hd
      obtain ⟨hp, hl, hdp, he⟩ := (treePt_spec (htree i hi)).2 (by omega)
      rw [← he, ← hact _ hl]
      exact Reach.step _ hl (ih _ hp (by omega))
  refine ⟨reach_iff_of_closed (mem_ptsF.2 ⟨r, hr, hroot⟩) (fun x hx k hk => ?_) (fun x hx => ?_),
    ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := mem_ptsF.1 hx
    obtain ⟨j, hj, e⟩ := closPt_spec (hclos i hi) hk
    rw [hact k hk, e]
    exact mem_ptsF.2 ⟨j, hj, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := mem_ptsF.1 hx
    exact hreach _ i hi rfl
  · unfold ptsF
    rw [List.toFinset_card_of_nodup, List.length_map, List.length_range]
    refine List.Nodup.map_on (fun i hi j hj e => ?_) List.nodup_range
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd e (Nat.ne_of_lt (incPt_mono hinc j (List.mem_range.1 hj) i h))
    · exact h
    · exact absurd e.symm (Nat.ne_of_lt (incPt_mono hinc i (List.mem_range.1 hi) j h))
  · obtain ⟨i, hi, rfl⟩ := mem_ptsF.1 hx
    exact (incPt_spec (hinc i hi)).1

end CFSG.KC.BM.OrbT

end
