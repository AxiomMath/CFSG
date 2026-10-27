module

public import Certificates.Data.Kernel.LocalQT.CoreS
public import CFSG.Certificates.Kernel.LocalQTTab2KSound
public import CFSG.Certificates.Kernel.LocalQTCoreCSnd.EltDef

public section

namespace CFSG.KC.LQT.Syl.CoreSnd

open Equiv CFSG.KC.LQT

variable {n : ℕ}

theorem testBit_sum_pow (S : Finset ℕ) (j : ℕ) :
    (∑ u ∈ S, 2 ^ u).testBit j = decide (j ∈ S) := by
  have key : j ∈ (∑ u ∈ S, 2 ^ u).bitIndices ↔ j ∈ S := by
    rw [← List.mem_toFinset, Finset.toFinset_bitIndices_sum_two_pow]
  rw [Nat.mem_bitIndices] at key
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact key

private theorem kpw_getK_codes (L : List (Perm (Fin n))) (j : ℕ) :
    Syl.getK (L.map P.code) j (P.one n) = P.code (L.getD j 1) := by
  induction L generalizing j with
  | nil =>
    change P.one n = P.code (([] : List (Perm (Fin n))).getD j 1)
    rw [List.getD_nil]
    exact P.code_one
  | cons x L ih =>
    cases j with
    | zero =>
      change P.code x = _
      rw [List.getD_cons_zero]
    | succ j =>
      change Syl.getK (L.map P.code) j (P.one n) = _
      rw [List.getD_cons_succ]
      exact ih j

private theorem kpw_eltK_loop (hn : n ≤ 32) (B : List (Perm (Fin n))) (m : ℕ) :
    ∀ (k : ℕ) (acc : Perm (Fin n)) (j : ℕ),
    (Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
      (fun _ ih acc d j => Syl.letN (Bool.rec (motive := fun _ => Nat) acc
        (P.mul n acc (Syl.getK (B.map P.code) j (P.one n))) (Nat.beq (Nat.mod d 2) 1))
        fun acc' => ih acc' (Nat.div d 2) (Nat.succ j)) k :
      Nat → Nat → Nat → Nat) (P.code acc) (m / 2 ^ j) j =
      P.code ((List.range' j k).foldl
        (fun acc i => if m.testBit i then acc * B.getD i 1 else acc) acc) := by
  intro k
  induction k with
  | zero => intro acc j; rfl
  | succ k ih =>
    intro acc j
    rw [List.range'_succ, List.foldl_cons]
    have hd : Nat.div (m / 2 ^ j) 2 = m / 2 ^ (j + 1) := by
      change m / 2 ^ j / 2 = _
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hl : ∀ (y : ℕ) (f : ℕ → ℕ), Syl.letN y f = f y := fun y f => by
      cases y <;> rfl
    change Syl.letN _ _ = _
    rw [hl, hd]
    by_cases hb : m.testBit j
    · have h1 : Nat.beq (Nat.mod (m / 2 ^ j) 2) 1 = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
        exact P.beq_iff.2 hb
      have hm : ∀ σ τ : Perm (Fin n), P.mul n (P.code σ) (P.code τ) = P.code (σ * τ) :=
        P.code_mul hn
      rw [if_pos hb, h1, kpw_getK_codes, hm]
      exact ih (acc * B.getD j 1) (j + 1)
    · have h1 : Nat.beq (Nat.mod (m / 2 ^ j) 2) 1 = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
        exact Bool.eq_false_iff.2 fun h => hb (P.beq_iff.1 h)
      rw [if_neg hb, h1]
      exact ih acc (j + 1)

theorem eltK_code (hn : n ≤ 32) (k m : ℕ) (B : List (Perm (Fin n))) :
    Syl.eltK n k (B.map P.code) m = P.code (elt k B m) := by
  have h := kpw_eltK_loop hn B m k 1 0
  rw [Nat.pow_zero, Nat.div_one, ← List.range_eq_range', ← P.code_one] at h
  exact h

theorem lstK_code (hn : n ≤ 32) (B : List (Perm (Fin n))) :
    Syl.lstK n 4 (B.map P.code) = (lst B).map P.code := by
  have h16 : Nat.pow 2 4 = 16 := rfl
  show List.map (Syl.eltK n 4 (B.map P.code)) (List.range (Nat.pow 2 4)) =
    List.map P.code (List.map (elt 4 B) (List.range 16))
  rw [h16, List.map_map]
  exact List.map_congr_left fun m _ => eltK_code hn 4 m B

private theorem kpw_eK_conj {l : List ℕ} (h : Syl.eK n l = true) :
    Nat.ble n 32 = true ∧ Nat.beq (S.lenL l) 4 = true ∧
      T2.distinctS (Syl.lstK n 4 l) = true ∧
      P.allL l (fun x => Nat.beq (P.mul n x x) (P.one n)) = true ∧
      P.allL l (fun x => P.allL l (fun y => P.comm n x y)) = true := by
  unfold Syl.eK at h
  simp only [S.allBs_cons, S.allBs_nil, P.andB_iff, and_true, eq_self_iff_true,
    true_and] at h
  obtain ⟨h1, h2, -, h4, h5, h6, -⟩ := h
  exact ⟨h1, h2, h4, h5, h6⟩

theorem eK_le {l : List ℕ} (h : Syl.eK n l = true) : n ≤ 32 :=
  Nat.le_of_ble_eq_true (kpw_eK_conj h).1

theorem eK_facts (B : List (Perm (Fin n))) (h : Syl.eK n (B.map P.code) = true) :
    n ≤ 32 ∧ EFacts B := by
  obtain ⟨h1, h2, h4, h5, h6⟩ := kpw_eK_conj h
  have hn : n ≤ 32 := Nat.le_of_ble_eq_true h1
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · have h2' : S.lenL (B.map P.code) = 4 := P.beq_iff.1 h2
    rw [S.lenL_eq, List.length_map] at h2'
    exact h2'
  · have h4' := T2.nodup_of_distinctS h4
    rw [lstK_code hn] at h4'
    exact List.Nodup.of_map P.code h4'
  · intro b hb
    have h7 : Nat.beq (P.mul n (P.code b) (P.code b)) (P.one n) = true :=
      (P.allL_map B _).1 h5 b hb
    rw [P.code_mul hn, P.code_one, P.beq_iff, P.code_eq_iff hn] at h7
    exact h7
  · intro b hb b' hb'
    have h7 : P.allL (B.map P.code) (fun y => P.comm n (P.code b) y) = true :=
      (P.allL_map B _).1 h6 b hb
    have h8 : P.comm n (P.code b) (P.code b') = true := (P.allL_map B _).1 h7 b' hb'
    exact (P.comm_code hn b b').1 h8

theorem normK_sound (hn : n ≤ 32) (B NP : List (Perm (Fin n)))
    (h : Syl.normK n (B.map P.code) (NP.map P.code) = true) :
    ∀ g ∈ NP, ∀ e ∈ B, ∃ e' ∈ lst B, g * e = e' * g := by
  unfold Syl.normK at h
  intro g hg e he
  have h1 : P.allL (B.map P.code)
      (fun x => P.anyL (Syl.lstK n 4 (B.map P.code))
        (fun y => Nat.beq (P.mul n (P.code g) x) (P.mul n y (P.code g)))) = true :=
    (P.allL_map NP _).1 h g hg
  have h2 : P.anyL (Syl.lstK n 4 (B.map P.code))
      (fun y => Nat.beq (P.mul n (P.code g) (P.code e)) (P.mul n y (P.code g))) = true :=
    (P.allL_map B _).1 h1 e he
  rw [lstK_code hn, P.anyL_map] at h2
  obtain ⟨e', he', h3⟩ := h2
  have h4 : Nat.beq (P.mul n (P.code g) (P.code e)) (P.mul n (P.code e') (P.code g)) = true :=
    h3
  rw [P.code_mul hn, P.code_mul hn, P.beq_iff, P.code_eq_iff hn] at h4
  exact ⟨e', he', h4⟩

end CFSG.KC.LQT.Syl.CoreSnd

end
