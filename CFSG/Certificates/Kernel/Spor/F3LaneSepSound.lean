module

public import Certificates.Data.Kernel.Spor.F3LaneSep
public import CFSG.Certificates.Kernel.Spor.F3LaneSound
public import Certificates.Data.CFSGNative.F3.Sep

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

theorem trBit_testBit (d x q i : Nat) :
    (trBit d x q).testBit i = (decide (i = q) && x.testBit (d * (q % d) + q / d)) := by
  unfold trBit
  cases h : Nat.testBit x (Nat.add (Nat.mul d (Nat.mod q d)) (Nat.div q d))
  · change Nat.testBit 0 i = _
    simp
  · change (1 <<< q).testBit i = _
    rw [testBit_one_shiftLeft, Bool.and_true]

theorem trStep_eq (d : Nat) (L : V) (q : Nat) (acc : V) :
    trStep d L q acc = ⟨Nat.lor acc.p (trBit d L.p q), Nat.lor acc.m (trBit d L.m q)⟩ := by
  unfold trStep
  rw [strictT_eq, strictT_eq]

theorem trLane_n (d : Nat) (L : V) : ∀ n i,
    (Nat.rec (motive := fun _ => V) ⟨0, 0⟩ (fun q acc => trStep d L q acc) n : V).p.testBit i =
        (decide (i < n) && L.p.testBit (d * (i % d) + i / d)) ∧
    (Nat.rec (motive := fun _ => V) ⟨0, 0⟩ (fun q acc => trStep d L q acc) n : V).m.testBit i =
        (decide (i < n) && L.m.testBit (d * (i % d) + i / d)) := by
  intro n
  induction n with
  | zero => intro i; simp
  | succ n ih =>
    intro i
    change (trStep d L n _).p.testBit i = _ ∧ (trStep d L n _).m.testBit i = _
    rw [trStep_eq]
    change (Nat.lor _ _).testBit i = _ ∧ (Nat.lor _ _).testBit i = _
    have hor : ∀ a c : Nat, (Nat.lor a c).testBit i = (a.testBit i || c.testBit i) :=
      fun a c => Nat.testBit_or a c i
    rw [hor, hor, (ih i).1, (ih i).2, trBit_testBit, trBit_testBit]
    by_cases h1 : i < n
    · have h2 : i ≠ n := by omega
      have h3 : i < n + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : i = n
      · subst h2
        simp
      · have h3 : ¬ i < n + 1 := by omega
        simp [h1, h2, h3]

theorem trLane_p (d : Nat) (L : V) (i : Nat) :
    (trLane d L).p.testBit i = (decide (i < d * d) && L.p.testBit (d * (i % d) + i / d)) :=
  (trLane_n d L (d * d) i).1

theorem trLane_m (d : Nat) (L : V) (i : Nat) :
    (trLane d L).m.testBit i = (decide (i < d * d) && L.m.testBit (d * (i % d) + i / d)) :=
  (trLane_n d L (d * d) i).2

theorem idx_lt {d i j : Nat} (hi : i < d) (hj : j < d) : d * j + i < d * d := by
  have : d * j + i < d * (j + 1) := by rw [Nat.mul_succ]; omega
  exact lt_of_lt_of_le this (Nat.mul_le_mul_left _ (by omega))

theorem transpose_unlane {d : Nat} {L : V} (hL : L.wf = true) :
    transpose d (unlane d L) = unlane d (trLane d L) := by
  apply Array.ext
  · unfold transpose
    rw [Array.size_ofFn, unlane_size]
  · intro j h1 h2
    have hj : j < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (transpose d (unlane d L)) j h1, ← getElem!_pos (unlane d (trLane d L)) j h2,
      unlane_get _ hj]
    unfold transpose
    rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn, ofFn_eq_fold]
    have hd : 0 < d := by omega
    apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
    · rw [(fold_ofFnStep_bits _ k d).1, blk_p]
      by_cases hk : k < d
      · rw [unlane_get L hk, trLane_p]
        have e1 : (d * j + k) % d = k := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk
        have e2 : (d * j + k) / d = j := by
          rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, Nat.add_zero]
        rw [e1, e2]
        unfold V.get
        rw [blk_p, blk_m]
        simp only [hk, hj, idx_lt hk hj, decide_true, Bool.true_and]
        cases L.p.testBit (d * k + j) <;> cases L.m.testBit (d * k + j) <;> simp
      · simp [hk]
    · rw [(fold_ofFnStep_bits _ k d).2, blk_m]
      by_cases hk : k < d
      · rw [unlane_get L hk, trLane_m]
        have e1 : (d * j + k) % d = k := by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hk
        have e2 : (d * j + k) / d = j := by
          rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hk, Nat.add_zero]
        rw [e1, e2]
        unfold V.get
        rw [blk_p, blk_m]
        simp only [hk, hj, idx_lt hk hj, decide_true, Bool.true_and]
        have hn := V.not_both hL (d * k + j)
        cases hp : L.p.testBit (d * k + j) <;> cases hm : L.m.testBit (d * k + j) <;>
          simp_all
      · simp [hk]

theorem blk_self {d : Nat} {u : V} (hp : u.p < 2 ^ d) (hm : u.m < 2 ^ d) : blk d u 0 = u := by
  apply V.ext' <;> apply Nat.eq_of_testBit_eq <;> intro k
  · rw [blk_p, Nat.mul_zero, Nat.zero_add]
    by_cases hk : k < d
    · simp [hk]
    · simp only [hk, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by norm_num)
        (by omega)))).symm
  · rw [blk_m, Nat.mul_zero, Nat.zero_add]
    by_cases hk : k < d
    · simp [hk]
    · simp only [hk, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
        (by omega)))).symm

theorem mulVec_unlane {d : Nat} (hd : 0 < d) {L u : V} (hL : L.wf = true) (hp : u.p < 2 ^ d)
    (hm : u.m < 2 ^ d) : mulVecM d (unlane d L) u = mulVecL d (trLane d L) u := by
  unfold mulVecM mulVecL
  rw [transpose_unlane hL, blk_rmK hd u (blk d (trLane d L))
    (fun j _ => ⟨blk_p_lt d _ j, blk_m_lt d _ j⟩) (by norm_num : 0 < 1) (unlane d (trLane d L))
    (fun j hj => unlane_get _ hj), blk_self hp hm]

theorem zeroM_unlane (d : Nat) : zeroM d = unlane d ⟨0, 0⟩ := by
  apply Array.ext
  · unfold zeroM
    rw [Array.size_replicate, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (zeroM d) i h1, ← getElem!_pos (unlane d ⟨0, 0⟩) i h2, unlane_get _ hi]
    unfold zeroM
    rw [getElem!_pos _ i (by rw [Array.size_replicate]; exact hi), Array.getElem_replicate]
    exact (blk_zero d i).symm

theorem addM_unlane (d : Nat) (X Y : V) : addM d (unlane d X) (unlane d Y) = unlane d (X.add Y) := by
  apply Array.ext
  · unfold addM
    rw [Array.size_ofFn, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (addM d (unlane d X) (unlane d Y)) i h1, ← getElem!_pos (unlane d (X.add Y)) i h2,
      unlane_get _ hi]
    unfold addM
    rw [getElem!_pos _ i (by rw [Array.size_ofFn]; exact hi), Array.getElem_ofFn, unlane_get _ hi,
      unlane_get _ hi, blk_add]

theorem negM_unlane (d : Nat) (X : V) : negM (unlane d X) = unlane d X.neg := by
  apply Array.ext
  · unfold negM
    rw [Array.size_map, unlane_size, unlane_size]
  · intro i h1 h2
    have hi : i < d := by rwa [unlane_size] at h2
    rw [← getElem!_pos (negM (unlane d X)) i h1, ← getElem!_pos (unlane d X.neg) i h2, unlane_get _ hi]
    unfold negM
    rw [getElem!_pos _ i (by rw [Array.size_map, unlane_size]; exact hi), Array.getElem_map,
      ← getElem!_pos (unlane d X) i (by rwa [unlane_size]), unlane_get _ hi]
    rfl

theorem mats_get {d : Nat} {Ls : List V} {x : Nat} (hx : x < Ls.length) :
    (Ls.map (unlane d)).toArray[x]! = unlane d (Ls.getD x ⟨0, 0⟩) := by
  rw [getElem!_pos _ x (by simpa using hx)]
  simp [List.getElem?_eq_getElem hx]

theorem prodM_unlane {d : Nat} (hd : 0 < d) {I : V} (hI : idM d = unlane d I) (Ls : List V)
    (word : List Nat) (hw : ∀ x ∈ word, x < Ls.length) :
    prodM d (Ls.map (unlane d)).toArray word = unlane d (prodL d (spreadE d d) I Ls word) := by
  unfold prodM prodL
  rw [hI]
  generalize I = M0
  induction word generalizing M0 with
  | nil => rfl
  | cons x w ih =>
    rw [List.foldl_cons, List.foldl_cons, mats_get (hw x List.mem_cons_self), mul_unlane hd]
    exact ih (fun y hy => hw y (List.mem_cons_of_mem x hy)) _

theorem combM_unlane {d : Nat} (hd : 0 < d) {I : V} (hI : idM d = unlane d I) (Ls : List V)
    (terms : List (Nat × List Nat)) (hw : ∀ t ∈ terms, ∀ x ∈ t.2, x < Ls.length) :
    combM d (Ls.map (unlane d)).toArray terms = unlane d (combL d (spreadE d d) I Ls terms) := by
  unfold combM combL
  rw [zeroM_unlane]
  generalize (⟨0, 0⟩ : V) = A0
  induction terms generalizing A0 with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons, List.foldl_cons]
    dsimp only
    rw [prodM_unlane hd hI Ls t.2 (hw t List.mem_cons_self)]
    have e : (t.1 == 2) = Nat.beq t.1 2 := rfl
    rw [e]
    cases Nat.beq t.1 2
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [addM_unlane]
      exact ih (fun s hs => hw s (List.mem_cons_of_mem t hs)) _
    · simp only [↓reduceIte]
      rw [negM_unlane, addM_unlane]
      exact ih (fun s hs => hw s (List.mem_cons_of_mem t hs)) _

theorem spinVecs_lane {d : Nat} (hd : 0 < d) {Ls : List V} (hLs : ∀ L ∈ Ls, L.wf = true) {v : V}
    (hvp : v.p < 2 ^ d) (hvm : v.m < 2 ^ d) (tree : List (Nat × Nat))
    (ht : ∀ t ∈ tree, t.2 < Ls.length) :
    spinVecs d (Ls.map (unlane d)).toArray v tree = spinL d (Ls.map (trLane d)) v tree := by
  unfold spinVecs spinL
  have h0 : ∀ i : Nat, V.p ((#[v] : Array V)[i]!) < 2 ^ d ∧ V.m ((#[v] : Array V)[i]!) < 2 ^ d := by
    intro i
    by_cases hi : i < 1
    · rw [getElem!_pos _ i (by simpa using hi)]
      have : i = 0 := by omega
      subst this
      exact ⟨hvp, hvm⟩
    · rw [getElem!_neg _ i (by simpa using hi)]
      exact ⟨Nat.two_pow_pos d, Nat.two_pow_pos d⟩
  generalize (#[v] : Array V) = S at h0
  induction tree generalizing S with
  | nil => rfl
  | cons t ts ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have hlt := ht t List.mem_cons_self
    have hL := hLs _ (List.getElem_mem hlt)
    rw [mats_get hlt, List.getD_eq_getElem _ _ hlt, mulVec_unlane hd hL (h0 t.1).1 (h0 t.1).2]
    have hget : (Ls.map (trLane d)).getD t.2 ⟨0, 0⟩ = trLane d Ls[t.2] := by
      rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map]
    rw [hget]
    apply ih (fun s hs => ht s (List.mem_cons_of_mem t hs))
    intro i
    by_cases hi : i < S.size
    · rw [getElem!_pos _ i (by simp; omega), Array.getElem_push_lt hi, ← getElem!_pos S i hi]
      exact h0 i
    · by_cases he : i = S.size
      · subst he
        rw [getElem!_pos _ _ (by simp), Array.getElem_push_eq]
        exact ⟨blk_p_lt d _ 0, blk_m_lt d _ 0⟩
      · rw [getElem!_neg _ i (by simp; omega)]
        exact ⟨Nat.two_pow_pos d, Nat.two_pow_pos d⟩

end CFSG.KS.F3L

end
