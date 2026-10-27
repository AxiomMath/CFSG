module

public import CFSG.Certificates.Kernel.AS35QTS.ListSound

public section

namespace CFSG.KC.AS35QTS

open CFSG.KC CFSG.KC.F4M3B CFSG.Fischer
open CFSG.LargeExtraspecial.AS35QTS (Cd mulC e0 tau0 I3 codes sl dl)

theorem cmp_testBit (p : Nat) : ∀ (L : List Nat) (j : Nat),
    (cmp L p).testBit j = (decide (j < L.length) && p.testBit (L.getD j 0))
  | [], j => by
    change Nat.testBit 0 j = _
    simp
  | c :: L, j => by
    change (Nat.add (bitN p c) (Nat.mul 2 (cmp L p))).testBit j = _
    have h2 := bitN_lt p c
    cases j with
    | zero =>
      change (bitN p c + 2 * cmp L p).testBit 0 = _
      rw [List.getD_cons_zero, ← bitN_testBit p c, Nat.testBit_zero, Nat.testBit_zero]
      simp only [List.length_cons, Nat.zero_lt_succ, decide_true, Bool.true_and]
      congr 1
      apply propext
      omega
    | succ j =>
      rw [List.getD_cons_succ, List.length_cons, Nat.testBit_succ]
      have e : (Nat.add (bitN p c) (Nat.mul 2 (cmp L p))) / 2 = cmp L p := by
        change (bitN p c + 2 * cmp L p) / 2 = _
        omega
      rw [e, cmp_testBit p L j]
      simp only [Nat.succ_lt_succ_iff]

theorem cmp_lt (p : Nat) : ∀ L : List Nat, cmp L p < 2 ^ L.length
  | [] => by change 0 < 1; norm_num
  | c :: L => by
    change Nat.add (bitN p c) (Nat.mul 2 (cmp L p)) < 2 ^ (L.length + 1)
    have := cmp_lt p L
    have := bitN_lt p c
    rw [pow_succ]
    change bitN p c + 2 * cmp L p < _
    omega

theorem lane_cmpP {L : List Nat} {j : Nat} (hj : j < L.length) (X : PL Nat) :
    laneOf j (cmpP X L) = laneOf (L.getD j 0) X := by
  simp only [laneOf, cmpP, mapP, cmp_testBit, hj, decide_true, Bool.true_and]

theorem ones_testBit (n c : Nat) : (ones n).testBit c = decide (c < n) := allOnes_testBit n c

theorem pairA_testBit {na nb : Nat} (hb : 0 < nb) (p : Nat) {i k : Nat} (hi : i < na)
    (hk : k < nb) : (pairA na nb p).testBit (i * nb + k) = p.testBit i := by
  have hf : ∀ i < na, Nat.mul (bitN p i) (ones nb) < 2 ^ nb := by
    intro i _
    have h1 : bitN p i ≤ 1 := by have := bitN_lt p i; omega
    change bitN p i * (2 ^ nb - 1) < 2 ^ nb
    calc bitN p i * (2 ^ nb - 1) ≤ 1 * (2 ^ nb - 1) := Nat.mul_le_mul_right _ h1
      _ < 2 ^ nb := by rw [one_mul]; exact Nat.sub_lt (Nat.two_pow_pos _) one_pos
  unfold pairA
  rw [blk_testBit hb hf]
  have hlt : i * nb + k < nb * na := by
    have : (i + 1) * nb ≤ na * nb := Nat.mul_le_mul_right _ hi
    rw [Nat.mul_comm nb na]
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hq : (i * nb + k) / nb = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hk, Nat.zero_add]
  have hr : (i * nb + k) % nb = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  rw [hq, hr, mulbit_tb, ones_testBit]
  simp [hlt, hk]

theorem pairB_testBit {na nb : Nat} (hb : 0 < nb) {p : Nat} (hp : p < 2 ^ nb) {i k : Nat}
    (hi : i < na) (hk : k < nb) : (pairB na nb p).testBit (i * nb + k) = p.testBit k := by
  unfold pairB
  rw [blk_testBit hb (fun _ _ => hp)]
  have hlt : i * nb + k < nb * na := by
    have : (i + 1) * nb ≤ na * nb := Nat.mul_le_mul_right _ hi
    rw [Nat.mul_comm nb na]
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hr : (i * nb + k) % nb = k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  rw [hr]
  simp [hlt]

theorem lane_pairA {L M : List Nat} (hM : 0 < M.length) {i k : Nat} (hi : i < L.length)
    (hk : k < M.length) (X : PL Nat) :
    laneOf (i * M.length + k) (mapP (fun p => pairA L.length M.length (cmp L p)) X) =
      laneOf (L.getD i 0) X := by
  simp only [laneOf, mapP, pairA_testBit hM _ hi hk, cmp_testBit, hi, decide_true, Bool.true_and]

theorem lane_pairB {L M : List Nat} (hM : 0 < M.length) {i k : Nat} (hi : i < L.length)
    (hk : k < M.length) (X : PL Nat) :
    laneOf (i * M.length + k) (mapP (fun p => pairB L.length M.length (cmp M p)) X) =
      laneOf (M.getD k 0) X := by
  simp only [laneOf, mapP, pairB_testBit hM (cmp_lt _ M) hi hk, cmp_testBit, hk, decide_true,
    Bool.true_and]

theorem allI_go (f : Nat → Nat → Bool) : ∀ (L : List Nat) (j0 : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih j => Bool.and' (f j x) (ih (Nat.succ j))) L j0 = true →
    ∀ j (h : j < L.length), f (j0 + j) L[j] = true
  | [], _, _, j, h => absurd h (Nat.not_lt_zero j)
  | x :: L, j0, h, j, hj => by
    change Bool.and' (f j0 x) (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih j => Bool.and' (f j x) (ih (Nat.succ j))) L (Nat.succ j0)) = true at h
    rw [and'_eq, Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j =>
      have := allI_go f L (Nat.succ j0) h.2 j (by simpa using hj)
      rw [Nat.succ_add] at this
      exact this

theorem allI_spec {f : Nat → Nat → Bool} {L : List Nat} (h : allI L f = true) :
    ∀ j (hj : j < L.length), f j L[j] = true := fun j hj => by
  have := allI_go f L 0 h j hj
  rwa [Nat.zero_add] at this

theorem allI_mem {f : Nat → Nat → Bool} {L : List Nat} (h : allI L f = true) :
    ∀ x ∈ L, ∃ j, f j x = true := fun x hx => by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact ⟨j, allI_spec h j hj⟩

theorem allI2_go (f : Nat → Nat → Nat → Bool) : ∀ (L M : List Nat) (j0 : Nat),
    List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
      (fun x _ ih M j => List.rec (motive := fun _ => Bool) false
        (fun y rest _ => Bool.and' (f j x y) (ih rest (Nat.succ j))) M) L M j0 = true →
    ∀ j (h : j < L.length), ∃ h' : j < M.length, f (j0 + j) L[j] M[j] = true
  | [], _, _, _, j, h => absurd h (Nat.not_lt_zero j)
  | x :: L, [], j0, h, _, _ => absurd h (by exact Bool.false_ne_true)
  | x :: L, y :: M, j0, h, j, hj => by
    change Bool.and' (f j0 x y) (List.rec (motive := fun _ => List Nat → Nat → Bool)
      (fun _ _ => true) (fun x _ ih M j => List.rec (motive := fun _ => Bool) false
        (fun y rest _ => Bool.and' (f j x y) (ih rest (Nat.succ j))) M) L M (Nat.succ j0)) =
      true at h
    rw [and'_eq, Bool.and_eq_true] at h
    cases j with
    | zero => exact ⟨by simp, h.1⟩
    | succ j =>
      obtain ⟨h', h2⟩ := allI2_go f L M (Nat.succ j0) h.2 j (by simpa using hj)
      rw [Nat.succ_add] at h2
      exact ⟨by simpa using h', h2⟩

theorem allI2_spec {f : Nat → Nat → Nat → Bool} {L M : List Nat} (h : allI2 L M f = true) :
    ∀ j (hj : j < L.length), ∃ h' : j < M.length, f j L[j] M[j] = true := fun j hj => by
  obtain ⟨h', h2⟩ := allI2_go f L M 0 h j hj
  rw [Nat.zero_add] at h2
  exact ⟨h', h2⟩

theorem beq_one_tb {P : Nat} (h : Nat.beq P 1 = true) : P.testBit 0 = true := by
  rw [Nat.eq_of_beq_eq_true h]
  rfl

theorem one_tb0 : (1 : Nat).testBit 0 = true := rfl

end CFSG.KC.AS35QTS

end
