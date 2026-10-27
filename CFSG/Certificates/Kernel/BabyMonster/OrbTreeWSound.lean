module

public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbTreeW
public import CFSG.Certificates.Kernel.BabyMonster.OrbTreeSound

public section

namespace CFSG.KC.BM.OrbW

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbT CFSG.KC.Bfs

@[expose] noncomputable def ptsB (B n : ℕ) (SB : List ℕ) : Finset ℕ :=
  ((List.range n).map (ptB B SB)).toFinset

theorem mem_ptsB {B n : ℕ} {SB : List ℕ} {x : ℕ} : x ∈ ptsB B n SB ↔ ∃ i < n, ptB B SB i = x := by
  simp [ptsB]

theorem incB_spec {B n bound : ℕ} {SB : List ℕ} {i : ℕ} (h : incB B n bound SB i = true) :
    ptB B SB i < bound ∧ (i + 1 < n → ptB B SB i < ptB B SB (i + 1)) := by
  unfold incB at h
  rw [andB_eq_true, blt_iff] at h
  refine ⟨h.1, fun hi => ?_⟩
  have h2 := h.2
  have hb : Nat.blt (Nat.succ i) n = true := blt_iff.2 hi
  rw [hb] at h2
  exact blt_iff.1 h2

theorem incB_mono {B n bound : ℕ} {SB : List ℕ} (h : ∀ i < n, incB B n bound SB i = true) :
    ∀ j < n, ∀ i < j, ptB B SB i < ptB B SB j := by
  intro j
  induction j with
  | zero => exact fun _ i hi => absurd hi (Nat.not_lt_zero i)
  | succ j ih =>
    intro hj i hi
    have hs := (incB_spec (h j (by omega))).2 hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact lt_trans (ih (by omega) i hi) hs
    · exact hs

theorem ptsB_card {B n bound : ℕ} {SB : List ℕ} (h : ∀ i < n, incB B n bound SB i = true) :
    (ptsB B n SB).card = n ∧ ∀ x ∈ ptsB B n SB, x < bound := by
  refine ⟨?_, fun x hx => ?_⟩
  · unfold ptsB
    rw [List.toFinset_card_of_nodup, List.length_map, List.length_range]
    refine List.Nodup.map_on (fun i hi j hj e => ?_) List.nodup_range
    rcases Nat.lt_trichotomy i j with hl | hl | hl
    · exact absurd e (Nat.ne_of_lt (incB_mono h j (List.mem_range.1 hj) i hl))
    · exact hl
    · exact absurd e.symm (Nat.ne_of_lt (incB_mono h i (List.mem_range.1 hi) j hl))
  · obtain ⟨i, hi, rfl⟩ := mem_ptsB.1 hx
    exact (incB_spec (h i hi)).1

theorem closB_spec {act : ℕ → ℕ → ℕ} {ngen B n : ℕ} {SB EB : List ℕ} {i : ℕ}
    (h : closB act ngen B n SB EB i = true) {k : ℕ} (hk : k < ngen) :
    ∃ j < n, act k (ptB B SB i) = ptB B SB j := by
  unfold closB at h
  have h' := allLt_eq_true.1 h k hk
  rw [andB_eq_true, blt_iff, beq_iff] at h'
  exact ⟨_, h'.1, h'.2⟩

theorem treeB_spec {act : ℕ → ℕ → ℕ} {ngen B n r : ℕ} {SB TB : List ℕ} {i : ℕ}
    (h : treeB act ngen B n r SB TB i = true) :
    (tDep (ptB B TB i) = 0 → i = r) ∧
      (tDep (ptB B TB i) ≠ 0 → tPar (ptB B TB i) < n ∧ tLab (ptB B TB i) < ngen ∧
        tDep (ptB B TB (tPar (ptB B TB i))) + 1 = tDep (ptB B TB i) ∧
        act (tLab (ptB B TB i)) (ptB B SB (tPar (ptB B TB i))) = ptB B SB i) := by
  unfold treeB at h
  by_cases hr : i = r
  · have hb : Nat.beq i r = true := beq_iff.2 hr
    rw [hb] at h
    exact ⟨fun _ => hr, fun h' => absurd (beq_iff.1 h) h'⟩
  · have hb : Nat.beq i r = false := Bool.eq_false_iff.2 fun e => hr (beq_iff.1 e)
    rw [hb] at h
    unfold edgeB at h
    simp only [andB_eq_true, blt_iff, beq_iff] at h
    refine ⟨fun e => ?_, fun _ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
    have := h.2.2.1
    omega

theorem treeB_reach {act act' : ℕ → ℕ → ℕ} {ngen B n root r : ℕ} {SB TB : List ℕ}
    (hact : ∀ k < ngen, ∀ x, act k x = act' k x)
    (htree : ∀ i < n, treeB act' ngen B n r SB TB i = true) (hroot : ptB B SB r = root) :
    ∀ i < n, Reach act ngen root (ptB B SB i) := by
  have hreach : ∀ d, ∀ i < n, tDep (ptB B TB i) = d → Reach act ngen root (ptB B SB i) := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      rw [(treeB_spec (htree i hi)).1 hd, hroot]
      exact Reach.root
    | succ d ih =>
      intro i hi hd
      obtain ⟨hp, hl, hdp, he⟩ := (treeB_spec (htree i hi)).2 (by omega)
      rw [← he, ← hact _ hl]
      exact Reach.step _ hl (ih _ hp (by omega))
  exact fun i hi => hreach _ i hi rfl

theorem orbB_reach {act act' : ℕ → ℕ → ℕ} {ngen B n root r bound : ℕ} {SB EB TB : List ℕ}
    (hact : ∀ k < ngen, ∀ x, act k x = act' k x)
    (hinc : ∀ i < n, incB B n bound SB i = true)
    (hclos : ∀ i < n, closB act' ngen B n SB EB i = true)
    (htree : ∀ i < n, treeB act' ngen B n r SB TB i = true)
    (hr : r < n) (hroot : ptB B SB r = root) :
    (∀ x, Reach act ngen root x ↔ x ∈ ptsB B n SB) ∧ (ptsB B n SB).card = n ∧
      ∀ x ∈ ptsB B n SB, x < bound := by
  refine ⟨reach_iff_of_closed (mem_ptsB.2 ⟨r, hr, hroot⟩) (fun x hx k hk => ?_) (fun x hx => ?_),
    ptsB_card hinc⟩
  · obtain ⟨i, hi, rfl⟩ := mem_ptsB.1 hx
    obtain ⟨j, hj, e⟩ := closB_spec (hclos i hi) hk
    rw [hact k hk, e]
    exact mem_ptsB.2 ⟨j, hj, rfl⟩
  · obtain ⟨i, hi, rfl⟩ := mem_ptsB.1 hx
    exact treeB_reach hact htree hroot i hi

end CFSG.KC.BM.OrbW

end
