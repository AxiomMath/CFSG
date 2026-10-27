module

public import Certificates.Data.Kernel.SporLatDcLin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CFSG.Certificates.Kernel.SporLatDcLists

public section

namespace CFSG.KC.SLDc

theorem cntB_cons' {α : Type} (f : α → Bool) (a : α) (l : List α) :
    cntB f (a :: l) = (if f a then 1 else 0) + cntB f l := by
  cases h : f a <;> simp [cntB, h, Nat.succ_eq_add_one, Nat.add_comm]

theorem sumN_eq_sum (l : List ℕ) : sumN l = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [sumN, ih]

theorem sum_map_range (f : ℕ → ℕ) (m : ℕ) :
    ((List.range m).map f).sum = ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem pairwise_of_ascN : ∀ {l : List ℕ}, ascN l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    simp only [ascN, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := pairwise_of_ascN h.2
    refine List.Pairwise.cons (fun x hx => ?_) ih
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem sum_ite_one {c m : ℕ} (h : c < m) :
    ∑ j ∈ Finset.range m, (if c = j then 1 else 0) = 1 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.lt_or_ge c m with hc | hc
    · rw [ih hc, if_neg (by omega)]
    · have hc' : c = m := by omega
      rw [Finset.sum_eq_zero fun j hj => if_neg (by rw [Finset.mem_range] at hj; omega),
        if_pos hc']

theorem sum_cntB (f : ℕ → ℕ) (m : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, f x < m) →
      ∑ j ∈ Finset.range m, cntB (fun q => Nat.beq (f q) j) l = l.length
  | [], _ => by simp [cntB]
  | a :: l, h => by
    simp only [cntB_cons', Finset.sum_add_distrib]
    rw [sum_cntB f m l (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp only [Nat.beq_eq]
    rw [sum_ite_one (h a List.mem_cons_self), List.length_cons]
    omega

theorem length_le_cntB (f : ℕ → ℕ) (j n : ℕ) {P : List ℕ} (hP : P.Nodup)
    (h : ∀ p ∈ P, p < n ∧ f p = j) :
    P.length ≤ cntB (fun q => Nat.beq (f q) j) (List.range n) := by
  rw [cntB_eq_length_filter]
  refine (List.subperm_of_subset hP fun p hp => ?_).length_le
  rw [List.mem_filter, List.mem_range]
  exact ⟨(h p hp).1, by simpa using (h p hp).2⟩

variable {C : DcCtx} {D : DcData} {P : List (List Nat)}

theorem oid_lt_of_pts (hg : globalOK C D = true)
    (hp : (List.range D.npc).all (ptChunk C D) = true) {p : ℕ} (hpn : p < C.n) :
    oid D p < D.obase.length := by
  have hnp : C.n ≤ D.npc * D.pcz := by
    unfold globalOK at hg
    simp only [Bool.and_eq_true, Nat.ble_eq] at hg
    exact hg.1.1.2
  have hz : 0 < D.pcz := by
    rcases Nat.eq_zero_or_pos D.pcz with h | h
    · rw [h, Nat.mul_zero] at hnp; omega
    · exact h
  have hi : p / D.pcz < D.npc := by
    rw [Nat.div_lt_iff_lt_mul hz]; omega
  have hc := List.all_eq_true.1 hp _ (List.mem_range.2 hi)
  unfold ptChunk at hc
  have hm : p ∈ List.range' (Nat.mul (p / D.pcz) D.pcz) D.pcz := by
    rw [List.mem_range']
    refine ⟨p - p / D.pcz * D.pcz, ?_, ?_⟩
    · have := Nat.mod_lt p hz
      rw [Nat.mod_eq_sub_mul_div] at this
      rw [Nat.mul_comm] at this
      omega
    · have := Nat.div_mul_le_self p D.pcz
      simp only [Nat.mul_eq]
      omega
  have e := List.all_eq_true.1 hc p hm
  rw [Bool.or_eq_true] at e
  rcases e with e | e
  · have hb : Nat.blt p C.n = true := Nat.blt_eq ▸ hpn
    rw [hb] at e
    exact absurd e (by decide)
  · unfold ptOK at e
    simp only [Bool.and_eq_true, Nat.blt_eq] at e
    exact e.1.1

theorem dcCheck_of_dcCheckL (h : dcCheckL C D P = true) : dcCheck C D = true := by
  unfold dcCheckL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hg, hp⟩, ho⟩, hs⟩, hc⟩ := h
  have ho' : ∀ j < D.obase.length, orbOKL C D P j = true :=
    fun j hj => List.all_eq_true.1 ho j (List.mem_range.2 hj)
  set m := D.obase.length
  let cnt : ℕ → ℕ := fun j => cntB (fun q => Nat.beq (oid D q) j) (List.range C.n)
  have hsum : ∑ j ∈ Finset.range m, cnt j = C.n := by
    have := sum_cntB (oid D) m (List.range C.n)
      (fun x hx => oid_lt_of_pts hg hp (List.mem_range.1 hx))
    rwa [List.length_range] at this
  have hosz : ∑ j ∈ Finset.range m, D.osz.getD j 0 = C.n := by
    unfold oszOK at hs
    rw [← sum_map_range, ← sumN_eq_sum]
    exact Nat.eq_of_beq_eq_true hs
  have hle : ∀ j ∈ Finset.range m, D.osz.getD j 0 ≤ cnt j := by
    intro j hj
    have e := ho' j (Finset.mem_range.1 hj)
    unfold orbOKL orbPts at e
    simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Nat.beq_eq] at e
    rw [← e.2.2]
    exact length_le_cntB (oid D) j C.n ((pairwise_of_ascN e.2.1.1).imp ne_of_lt) e.2.1.2
  have heq := (Finset.sum_eq_sum_iff_of_le hle).1 (by rw [hosz, hsum])
  unfold dcCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hg, hp⟩, List.all_eq_true.2 fun j hj => ?_⟩, hc⟩
  have hj' := List.mem_range.1 hj
  have e := ho' j hj'
  unfold orbOKL at e
  rw [Bool.and_eq_true] at e
  unfold orbOK
  rw [Bool.and_eq_true]
  refine ⟨e.1, ?_⟩
  rw [Nat.beq_eq]
  exact (heq j (Finset.mem_range.2 hj')).symm

end CFSG.KC.SLDc

end
