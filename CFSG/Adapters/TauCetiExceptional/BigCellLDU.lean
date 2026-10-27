module

public import Mathlib.LinearAlgebra.Matrix.Block

public noncomputable section

namespace CFSG.TauCetiBridge.BigCell

open Matrix

variable {A : Type*} [CommRing A] {n : ℕ}

@[expose] def leadMinor (M : Matrix (Fin n) (Fin n) A) (k : ℕ) : A :=
  (M.toBlock (fun i => i.val < k) (fun i => i.val < k)).det

@[expose] def bigCellDet (M : Matrix (Fin n) (Fin n) A) : A :=
  ∏ i : Fin n, leadMinor M (i.val + 1)

theorem map_leadMinor {B : Type*} [CommRing B] (f : A →+* B) (M : Matrix (Fin n) (Fin n) A)
    (k : ℕ) : f (leadMinor M k) = leadMinor (f.mapMatrix M) k := by
  rw [leadMinor, leadMinor, RingHom.map_det]
  rfl

theorem map_bigCellDet {B : Type*} [CommRing B] (f : A →+* B) (M : Matrix (Fin n) (Fin n) A) :
    f (bigCellDet M) = bigCellDet (f.mapMatrix M) := by
  rw [bigCellDet, bigCellDet, map_prod]
  exact Finset.prod_congr rfl fun i _ => map_leadMinor f M _

theorem det_mem {m : Type*} [Fintype m] [DecidableEq m] (S : Subring A) (M : Matrix m m A)
    (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  have h := RingHom.map_det S.subtype (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S))
  have h' : S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) = M := by
    ext i j
    rfl
  rw [h'] at h
  rw [← h]
  exact Subtype.prop _

theorem leadMinor_mem (S : Subring A) (M : Matrix (Fin n) (Fin n) A) (hM : ∀ i j, M i j ∈ S)
    (k : ℕ) : leadMinor M k ∈ S :=
  det_mem S _ fun i j => hM i j

structure IsLDU (l d u : Matrix (Fin n) (Fin n) A) : Prop where
  l_one : ∀ i, l i i = 1
  l_zero : ∀ i j, i < j → l i j = 0
  d_zero : ∀ i j, i ≠ j → d i j = 0
  u_one : ∀ i, u i i = 1
  u_zero : ∀ i j, j < i → u i j = 0

variable {l d u : Matrix (Fin n) (Fin n) A}

theorem IsLDU.mul_apply (h : IsLDU l d u) (i j : Fin n) :
    (l * d * u) i j = ∑ m, l i m * d m m * u m j := by
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_eq_single m (fun k _ hk => by rw [h.d_zero k m hk, mul_zero])
    (fun hm => absurd (Finset.mem_univ m) hm)]

theorem IsLDU.leadMinor_eq (h : IsLDU l d u) (k : ℕ) :
    leadMinor (l * d * u) k = ∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), d i i := by
  set p : Fin n → Prop := fun i => i.val < k with hp
  have hl : l.toBlock p (fun i => ¬p i) = 0 := by
    ext i j
    have hi := i.2
    have hj := j.2
    simp only [hp] at hi hj
    exact h.l_zero _ _ (Fin.lt_def.2 (by omega))
  have hd : d.toBlock p (fun i => ¬p i) = 0 := by
    ext i j
    refine h.d_zero _ _ fun hij => ?_
    have hi := i.2
    have hj := j.2
    rw [hij] at hi
    exact hj hi
  have hu : u.toBlock (fun i => ¬p i) p = 0 := by
    ext i j
    have hi := i.2
    have hj := j.2
    simp only [hp] at hi hj
    exact h.u_zero _ _ (Fin.lt_def.2 (by omega))
  have hblock : (l * d * u).toBlock p p = l.toBlock p p * d.toBlock p p * u.toBlock p p := by
    rw [Matrix.toBlock_mul_eq_add p p p, hu, Matrix.mul_zero, add_zero,
      Matrix.toBlock_mul_eq_add p p p, hl, Matrix.zero_mul, add_zero]
  have hdetl : (l.toBlock p p).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular (l.toBlock p p) fun i j hij =>
      h.l_zero i.1 j.1 (OrderDual.toDual_lt_toDual.1 hij)]
    exact Finset.prod_eq_one fun i _ => h.l_one _
  have hdetu : (u.toBlock p p).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (M := u.toBlock p p) fun i j hij =>
      h.u_zero i.1 j.1 hij]
    exact Finset.prod_eq_one fun i _ => h.u_one _
  have hdetd : (d.toBlock p p).det = ∏ i : {i // p i}, d i i :=
    Matrix.det_of_isUpperTriangular fun i j hij => h.d_zero _ _ fun e =>
      (ne_of_gt hij) (Subtype.ext e)
  rw [leadMinor, hblock, Matrix.det_mul, Matrix.det_mul, hdetl, hdetu, hdetd, one_mul, mul_one]
  exact (Finset.prod_subtype _ (fun i => by simp [hp]) fun i => d i i).symm

theorem IsLDU.leadMinor_succ (h : IsLDU l d u) (m : Fin n) :
    leadMinor (l * d * u) (m.val + 1) = leadMinor (l * d * u) m.val * d m m := by
  rw [h.leadMinor_eq, h.leadMinor_eq]
  have he : Finset.univ.filter (fun i : Fin n => i.val < m.val + 1) =
      insert m (Finset.univ.filter fun i : Fin n => i.val < m.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | h'
      · exact .inr h'
      · exact .inl (Fin.ext h')
    · rintro (rfl | h')
      · omega
      · omega
  rw [he, Finset.prod_insert (by simp), mul_comm]

theorem IsLDU.mem (S : Subring A) (h : IsLDU l d u) (hg : ∀ i j, (l * d * u) i j ∈ S)
    (hinv : ∃ y ∈ S, y * bigCellDet (l * d * u) = 1) (m : Fin n) :
    (∃ y ∈ S, y * d m m = 1) ∧ d m m ∈ S ∧ (∀ i, l i m ∈ S) ∧ ∀ j, u m j ∈ S := by
  have hunit : ∀ m : Fin n, ∃ y ∈ S, y * d m m = 1 := by
    intro m
    obtain ⟨y, hy, hyD⟩ := hinv
    have hsplit := (Finset.mul_prod_erase Finset.univ
      (fun i : Fin n => leadMinor (l * d * u) (i.val + 1)) (Finset.mem_univ m))
    rw [← bigCellDet, h.leadMinor_succ] at hsplit
    refine ⟨y * (∏ i ∈ Finset.univ.erase m, leadMinor (l * d * u) (i.val + 1)) *
      leadMinor (l * d * u) m.val, S.mul_mem (S.mul_mem hy (S.prod_mem fun i _ =>
        leadMinor_mem S _ hg _)) (leadMinor_mem S _ hg _), ?_⟩
    rw [← hyD, ← hsplit]
    ring
  suffices H : ∀ k : ℕ, ∀ m : Fin n, m.val = k →
      d m m ∈ S ∧ (∀ i, l i m ∈ S) ∧ ∀ j, u m j ∈ S from ⟨hunit m, H m.val m rfl⟩
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro m hm
  have IH : ∀ m' : Fin n, m' < m → d m' m' ∈ S ∧ (∀ i, l i m' ∈ S) ∧ ∀ j, u m' j ∈ S :=
    fun m' hm' => ih m'.val (hm ▸ Fin.lt_def.1 hm') m' rfl
  set T : Fin n → Fin n → A := fun i j =>
    ∑ m' ∈ Finset.univ.erase m, l i m' * d m' m' * u m' j with hT
  have hsum : ∀ i j, (l * d * u) i j = l i m * d m m * u m j + T i j := fun i j => by
    rw [h.mul_apply]
    exact (Finset.add_sum_erase _ (fun m' => l i m' * d m' m' * u m' j)
      (Finset.mem_univ m)).symm
  have hmem : ∀ i j, (i = m ∨ j = m) → T i j ∈ S := by
    intro i j hij
    refine S.sum_mem fun m' hm' => ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hm') with hlt | hgt
    · obtain ⟨hd', hl', hu'⟩ := IH m' hlt
      exact S.mul_mem (S.mul_mem (hl' i) hd') (hu' j)
    · rcases hij with rfl | rfl
      · rw [h.l_zero _ _ hgt, zero_mul, zero_mul]
        exact S.zero_mem
      · rw [h.u_zero _ _ hgt, mul_zero]
        exact S.zero_mem
  obtain ⟨y, hy, hyd⟩ := hunit m
  have hdm : d m m ∈ S := by
    have e := hsum m m
    rw [h.l_one, h.u_one, one_mul, mul_one] at e
    rw [show d m m = (l * d * u) m m - T m m by rw [e]; ring]
    exact S.sub_mem (hg m m) (hmem m m (.inl rfl))
  refine ⟨hdm, fun i => ?_, fun j => ?_⟩
  · have e := hsum i m
    rw [h.u_one, mul_one] at e
    rw [show l i m = ((l * d * u) i m - T i m) * y by
      rw [e, add_sub_cancel_right, mul_assoc, mul_comm (d m m) y, hyd, mul_one]]
    exact S.mul_mem (S.sub_mem (hg i m) (hmem i m (.inr rfl))) hy
  · have e := hsum m j
    rw [h.l_one, one_mul] at e
    rw [show u m j = y * ((l * d * u) m j - T m j) by
      rw [e, add_sub_cancel_right, ← mul_assoc, hyd, one_mul]]
    exact S.mul_mem hy (S.sub_mem (hg m j) (hmem m j (.inl rfl)))

end CFSG.TauCetiBridge.BigCell
