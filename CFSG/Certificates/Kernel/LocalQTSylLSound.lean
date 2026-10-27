module

public import Certificates.Data.Kernel.LocalQT.SylL
public import CFSG.Certificates.Kernel.LocalQTSylESound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheckInputs
import CFSG.Certificates.Kernel.LocalQTSylProved
import CFSG.Certificates.Kernel.LocalQTSmallSound

public section

namespace CFSG.KC.LQT.Syl

open Equiv CFSG.QuasithinUnique.Setup.X1 CFSG.KC.LQT.W

theorem getK_codes {n : ℕ} (H : Subgroup (Perm (Fin n))) (L : List H) (j : ℕ) :
    getK (L.map fun x : H => codeP (x : Perm (Fin n))) j (P.one n) =
      codeP ((L.getD j 1 : H) : Perm (Fin n)) := by
  induction L generalizing j with
  | nil =>
    change P.one n = codeP ((([] : List H).getD j 1 : H) : Perm (Fin n))
    rw [List.getD_nil, Subgroup.coe_one]
    exact P.code_one
  | cons x L ih =>
    cases j with
    | zero =>
      change codeP (x : Perm (Fin n)) = _
      rw [List.getD_cons_zero]
    | succ j =>
      change getK (L.map fun x : H => codeP (x : Perm (Fin n))) j (P.one n) = _
      rw [List.getD_cons_succ]
      exact ih j

theorem eltK_loop {n : ℕ} (hn : n ≤ 32) (H : Subgroup (Perm (Fin n))) (B : List H) (m : ℕ) :
    ∀ (k : ℕ) (acc : H) (j : ℕ),
    (Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun acc _ _ => acc)
      (fun _ ih acc d j => letN (Bool.rec (motive := fun _ => Nat) acc
        (P.mul n acc (getK (B.map fun x : H => codeP (x : Perm (Fin n))) j (P.one n)))
        (Nat.beq (Nat.mod d 2) 1)) fun acc' => ih acc' (Nat.div d 2) (Nat.succ j)) k :
      Nat → Nat → Nat → Nat) (codeP (acc : Perm (Fin n))) (m / 2 ^ j) j =
      codeP (((List.range' j k).foldl
        (fun acc i => if m.testBit i then acc * B.getD i 1 else acc) acc : H) : Perm (Fin n)) := by
  intro k
  induction k with
  | zero => intro acc j; rfl
  | succ k ih =>
    intro acc j
    rw [List.range'_succ, List.foldl_cons]
    have hd : Nat.div (m / 2 ^ j) 2 = m / 2 ^ (j + 1) := by
      change m / 2 ^ j / 2 = _
      rw [Nat.div_div_eq_div_mul, pow_succ]
    have hl : ∀ (y : ℕ) (f : ℕ → ℕ), letN y f = f y := fun y f => by cases y <;> rfl
    change letN _ _ = _
    rw [hl, hd]
    by_cases hb : m.testBit j
    · have h1 : Nat.beq (Nat.mod (m / 2 ^ j) 2) 1 = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
        exact P.beq_iff.2 hb
      have hm : ∀ σ τ : Perm (Fin n), P.mul n (codeP σ) (codeP τ) = codeP (σ * τ) :=
        P.code_mul hn
      rw [if_pos hb, h1, getK_codes, hm, ← Subgroup.coe_mul]
      exact ih _ _
    · have h1 : Nat.beq (Nat.mod (m / 2 ^ j) 2) 1 = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
        exact Bool.eq_false_iff.2 fun h => hb (P.beq_iff.1 h)
      rw [if_neg hb, h1]
      exact ih _ _

theorem lst_codes (B : List S24) {BC : List ℕ}
    (hB : B.map (fun x : S24 => codeP (x : Perm (Fin 24))) = BC) :
    (m24Lst B).map (fun x : S24 => codeP (x : Perm (Fin 24))) = lstK 24 6 BC := by
  subst hB
  have h64 : Nat.pow 2 6 = 64 := rfl
  rw [m24Lst, lstK, h64, List.map_map]
  refine List.map_congr_left fun m _ => ?_
  have h := eltK_loop (by norm_num) _ B m 6 1 0
  have h1 : P.one 24 = codeP ((1 : S24) : Perm (Fin 24)) := P.code_one
  rw [Nat.pow_zero, Nat.div_one, ← List.range_eq_range', ← h1] at h
  rw [Function.comp_apply, m24Elt, eltK]
  exact h.symm

theorem eab_sound (B : List S24) {BC : List ℕ}
    (hB : B.map (fun x : S24 => codeP (x : Perm (Fin 24))) = BC) (h : eabK 24 6 BC = true) :
    (m24Lst B).length = 64 ∧ (m24Lst B).Nodup ∧ (1 : S24) ∈ m24Lst B ∧
      (∀ x ∈ m24Lst B, ∀ y ∈ m24Lst B, x * y ∈ m24Lst B) ∧ (∀ x ∈ m24Lst B, x * x = 1) ∧
      (∀ x ∈ m24Lst B, ∀ y ∈ m24Lst B, x * y = y * x) ∧ (∀ b ∈ B, b ∈ m24Lst B) := by
  have hn : (24 : ℕ) ≤ 32 := by norm_num
  have hL := lst_codes B hB
  unfold eabK at h
  rw [P.andB_iff] at h
  obtain ⟨hs, h2⟩ := h
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff] at h2
  obtain ⟨hi, hc, hb, -⟩ := h2
  rw [← hL] at hs hi hc hb
  obtain ⟨s1, s2, s3, s4, -⟩ := sub_sound _ (m24Lst B) (m24Lst B) 6 rfl rfl hs
  have hmem : ∀ x ∈ m24Lst B, Pf.cH _ x ∈ (m24Lst B).map fun x : S24 => codeP (x : Perm (Fin 24)) :=
    fun x hx => List.mem_map_of_mem hx
  refine ⟨s1, s2, s3, s4, fun x hx => ?_, fun x hx y hy => ?_, fun b hb' => ?_⟩
  · have := (P.allL_iff _ _).1 hi _ (hmem x hx)
    rw [Pf.cH_mul hn, Pf.cH_one, Pf.beq_cH hn] at this
    exact this
  · have := (P.allL_iff _ _).1 ((P.allL_iff _ _).1 hc _ (hmem x hx)) _ (hmem y hy)
    rw [Pf.comm_cH hn] at this
    exact this
  · subst hB
    have := (P.allL_iff _ _).1 hb (Pf.cH _ b) (List.mem_map_of_mem hb')
    rw [CFSG.KC.LQT.S.memL_iff] at this
    exact (Pf.mem_map_cH hn b _).1 this

end CFSG.KC.LQT.Syl

end
