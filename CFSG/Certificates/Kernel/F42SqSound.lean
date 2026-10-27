module

public import Certificates.Data.Kernel.F42Sq
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.PcGroup
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.F42

open CFSG.KC.Enum

@[expose] noncomputable def arrOf (P n : ℕ) : Array ℕ := Array.ofFn (n := n) fun i => fldW P 22 i

@[expose] noncomputable def dOf (L D n p : ℕ) : ℕ := fldW D 8 ((arrOf L n).toList.idxOf p)

theorem strictB_eq (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = if c then t else e := by
  cases c <;> rfl

theorem ofFn_eq_map_range (n : ℕ) (f : ℕ → ℕ) :
    List.ofFn (n := n) (fun i => f i) = (List.range n).map f :=
  List.ext_getElem (by simp) fun i h1 h2 => by simp

@[expose] noncomputable def cand (k A c : ℕ) : ℕ := fldW A 22 (c / 2) + c % 2 * 2 ^ k

theorem extend_toList (k A n : ℕ) :
    (CFSG.EvenSmallLie.FFourTwo.Pc.extend k (arrOf A n)).toList =
      (List.range (2 * n)).map (cand k A) := by
  rw [CFSG.EvenSmallLie.FFourTwo.Pc.extend, Array.toList_flatMap, arrOf, Array.toList_ofFn,
    ofFn_eq_map_range n (fun i => fldW A 22 i)]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      show 2 * (n + 1) = 2 * n + 1 + 1 by omega, List.range_succ, List.range_succ, List.map_append,
      List.map_append, List.append_assoc]
    congr 1
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.singleton_append, cand]
    refine congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_ rfl)
    · rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]
      simp
    · rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
      simp

theorem stepOK_spec {k A B Q S c : ℕ} {last : Bool} (h : stepOK k A B Q S last c = true) :
    (mulR (cand k A c) (cand k A c) % 2 ^ (k + 1) = 0 →
      fldW Q 17 (c + 1) = fldW Q 17 c + 1 ∧ fldW B 22 (fldW Q 17 c) = cand k A c ∧
        (last = true →
          mulR (cand k A c) (cand k A c) >>> 22 = fldW S 3 (fldW Q 17 c))) ∧
    (mulR (cand k A c) (cand k A c) % 2 ^ (k + 1) ≠ 0 → fldW Q 17 (c + 1) = fldW Q 17 c) := by
  have hq : Nat.add (fldW A 22 (Nat.shiftRight c 1)) (Nat.mul (Nat.land c 1) (Nat.pow 2 k)) =
      cand k A c := by
    rw [cand]
    change fldW A 22 (c >>> 1) + (c &&& 1) * 2 ^ k = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, pow_one]
  unfold stepOK at h
  simp only [strictB_eq, hq, bIf_eq] at h
  constructor
  · intro hp
    have hb : Nat.beq (Nat.mod (mulR (cand k A c) (cand k A c)) (Nat.pow 2 (Nat.succ k))) 0 = true :=
      Nat.beq_eq_true_eq _ _ ▸ hp
    simp only [hb, ↓reduceIte] at h
    split_ifs at h with h1 h2 h3
    · exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2,
        fun _ => (Nat.eq_of_beq_eq_true h).symm⟩
    · exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun hl => absurd hl h3⟩
  · intro hp
    have hb : Nat.beq (Nat.mod (mulR (cand k A c) (cand k A c)) (Nat.pow 2 (Nat.succ k))) 0 = false :=
      beq_false_of_ne hp
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    exact Nat.eq_of_beq_eq_true h

theorem level_sound {k A B Q S nA nB nC : ℕ} {last : Bool} (hC : nC = 2 * nA)
    (h0 : Nat.beq (fldW Q 17 0) 0 = true) (hn : Nat.beq (fldW Q 17 nC) nB = true)
    (hc : ∀ c < nC, stepOK k A B Q S last c = true) :
    (CFSG.EvenSmallLie.FFourTwo.Pc.extend k (arrOf A nA)).filter
        (fun q => mulR q q % 2 ^ (k + 1) == 0) = arrOf B nB ∧
      ∀ a < nB, mulR (fldW B 22 a) (fldW B 22 a) % 2 ^ (k + 1) = 0 ∧
        (last = true → mulR (fldW B 22 a) (fldW B 22 a) >>> 22 = fldW S 3 a) := by
  set P : ℕ → Bool := fun q => mulR q q % 2 ^ (k + 1) == 0 with hP
  have inv : ∀ c ≤ nC, ((List.range c).map (cand k A)).filter P =
      (List.range (fldW Q 17 c)).map (fldW B 22) ∧
      ∀ a < fldW Q 17 c, mulR (fldW B 22 a) (fldW B 22 a) % 2 ^ (k + 1) = 0 ∧
        (last = true → mulR (fldW B 22 a) (fldW B 22 a) >>> 22 = fldW S 3 a) := by
    intro c
    induction c with
    | zero =>
      intro _
      rw [Nat.eq_of_beq_eq_true h0]
      exact ⟨rfl, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
    | succ c ih =>
      intro hc1
      obtain ⟨e, hall⟩ := ih (by omega)
      obtain ⟨hpass, hfail⟩ := stepOK_spec (hc c (by omega))
      rw [List.range_succ, List.map_append, List.filter_append, e]
      by_cases hp : mulR (cand k A c) (cand k A c) % 2 ^ (k + 1) = 0
      · obtain ⟨q1, q2, q3⟩ := hpass hp
        have hPc : P (cand k A c) = true := by simp [hP, hp]
        rw [q1, List.range_succ, List.map_append]
        simp only [List.map_cons, List.map_nil, List.filter_cons, hPc, ↓reduceIte, List.filter_nil,
          q2]
        refine ⟨by simp, fun a ha => ?_⟩
        rcases Nat.lt_or_ge a (fldW Q 17 c) with ha' | ha'
        · exact hall a ha'
        · obtain rfl : a = fldW Q 17 c := by omega
          rw [q2]
          exact ⟨hp, q3⟩
      · have q1 := hfail hp
        have hPc : P (cand k A c) = false := by simp [hP, hp]
        rw [q1]
        simp only [List.map_cons, List.map_nil, List.filter_cons, hPc, Bool.false_eq_true,
          ↓reduceIte, List.filter_nil, List.append_nil]
        exact ⟨by simp, hall⟩
  obtain ⟨e, hall⟩ := inv nC le_rfl
  rw [Nat.eq_of_beq_eq_true hn] at e hall
  refine ⟨?_, hall⟩
  apply Array.ext'
  rw [Array.toList_filter, extend_toList, ← hC, e, arrOf, Array.toList_ofFn,
    ofFn_eq_map_range nB (fun i => fldW B 22 i)]

@[expose] noncomputable def cntL (S n c : ℕ) : ℕ :=
  ((List.range n).map fun i => fldW S 3 i).countP (· == c)

theorem countP_eq_cntL {B S n : ℕ}
    (h : ∀ a < n, mulR (fldW B 22 a) (fldW B 22 a) = fldW S 3 a * 2 ^ 22) (c : ℕ) :
    (arrOf B n).toList.countP (fun p => mulR p p == c * 2 ^ 22) = cntL S n c := by
  rw [arrOf, Array.toList_ofFn, cntL, ofFn_eq_map_range n (fun i => fldW B 22 i), List.countP_map,
    List.countP_map]
  refine List.countP_congr fun i hi => ?_
  simp only [Function.comp_apply, beq_iff_eq, h i (List.mem_range.1 hi)]
  exact Nat.mul_left_inj (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos 22))

theorem bfs_sound {L S D M Pt n : ℕ} (hnd : (arrOf L n).toList.Nodup)
    (hall : ∀ i < n, bfsChk L S D M Pt n i = true) :
    ∀ i < n, fldW S 3 i = 0 → fldW L 22 i ≠ 0 → isRep (fldW L 22 i) = true ∨
      ∃ m, rmOK m = true ∧ mvOKR m (fldW L 22 i) = true ∧
        mvR m (fldW L 22 i) % 2 ^ 22 ≠ 0 ∧
        dOf L D n (mvR m (fldW L 22 i) % 2 ^ 22) + 1 = dOf L D n (fldW L 22 i) := by
  have hnot : ∀ b : Bool, Bool.rec (motive := fun _ => Bool) true false b = true ↔ b = false := by
    intro b
    cases b <;> simp
  have hix : ∀ j < n, dOf L D n (fldW L 22 j) = fldW D 8 j := by
    intro j hj
    have hlen : j < (arrOf L n).toList.length := by simp [arrOf, hj]
    have hg : (arrOf L n).toList[j] = fldW L 22 j := by simp [arrOf]
    rw [dOf, ← hg, hnd.idxOf_getElem j hlen]
  intro i hi hS hp
  have h := hall i hi
  unfold bfsChk at h
  have hS' : Nat.beq (fldW S 3 i) 0 = true := by rw [hS]; rfl
  have hp' : Nat.beq (fldW L 22 i) 0 = false := beq_false_of_ne hp
  simp only [strictB_eq, hS', hp'] at h
  cases hr : isRep (fldW L 22 i)
  · right
    simp only [hr, CFSG.KS.bAnd_iff, hnot] at h
    obtain ⟨hrm, hok, hy, hj, hL, hD⟩ := h
    have e : mvR (fldW M 3 i) (fldW L 22 i) % 2 ^ 22 = fldW L 22 (fldW Pt 16 i) :=
      (Nat.eq_of_beq_eq_true hL).symm
    refine ⟨fldW M 3 i, hrm, hok, fun h0 => ?_, ?_⟩
    · have hy' : Nat.beq (mvR (fldW M 3 i) (fldW L 22 i) % 2 ^ 22) 0 = false := hy
      rw [h0] at hy'
      exact absurd hy' (by decide)
    · have hj' : fldW Pt 16 i < n := Nat.blt_eq ▸ hj
      rw [e, hix _ hj', hix i hi]
      exact Nat.eq_of_beq_eq_true hD
  · exact Or.inl rfl

end CFSG.KC.F42

end
