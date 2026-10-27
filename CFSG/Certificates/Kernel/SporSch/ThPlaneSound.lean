
module

public import CFSG.Sporadic.ThSchreier.UASpaceBase
import CFSG.Certificates.Kernel.SporSch.ThRowsProved
public import CFSG.Certificates.Kernel.SporSch.ThRowsDefs
public import Certificates.Data.Kernel.SporSch.ThRows

public section

namespace CFSG.KS.SporSch

open CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.KS.SporSch.Pf

private theorem strictB_wc (y : Nat) (k : Nat → Bool) : CFSG.KC.Enum.strictB y k = k y := by
  cases y <;> rfl

private theorem bAnd_wc {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

private theorem bIf_wc {c t e : Bool} :
    Bool.rec (motive := fun _ => Bool) e t c = true ↔
      (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c <;> simp

private theorem icode_three {z : Int} (h : CFSG.KS.Mathieu.icode z = 3) : z = -1 := by
  cases z with
  | ofNat n =>
    have h' : n + n = 3 := h
    omega
  | negSucc n =>
    have h' : n + 1 + (n + 1) + 1 = 3 := h
    obtain rfl : n = 0 := by omega
    rfl

private theorem icode_five {z : Int} (h : CFSG.KS.Mathieu.icode z = 5) : z = -2 := by
  cases z with
  | ofNat n =>
    have h' : n + n = 5 := h
    omega
  | negSucc n =>
    have h' : n + 1 + (n + 1) + 1 = 5 := h
    obtain rfl : n = 1 := by omega
    rfl

private theorem wcFrom_cons (LC : Nat → Nat) (z : Int) (t : List Int) (s : Nat) :
    wcFrom LC (z :: t) s = Bool.rec (motive := fun _ => Bool) false (wcFrom LC t (s + 1))
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (Nat.beq (LC s) 1)
          (Nat.beq (CFSG.KS.Mathieu.icode z) 5))
        (Nat.beq (LC s) 0) (Nat.beq (CFSG.KS.Mathieu.icode z) 3)) := by
  show CFSG.KC.Enum.strictB (CFSG.KS.Mathieu.icode z) (fun c =>
    Bool.rec (motive := fun _ => Bool) false (wcFrom LC t (s + 1))
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (Nat.beq (LC s) 1) (Nat.beq c 5))
        (Nat.beq (LC s) 0) (Nat.beq c 3))) = _
  rw [strictB_wc]

private theorem wcFrom_spec {LC : Nat → Nat} {w : List Int} :
    ∀ {s : Nat}, wcFrom LC w s = true → ∀ k (hk : k < w.length),
      (w[k] = -1 ∧ LC (s + k) = 0) ∨ (w[k] = -2 ∧ LC (s + k) = 1) := by
  induction w with
  | nil => intro s _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons z t ih =>
    intro s h k hk
    rw [wcFrom_cons, bAnd_wc, bIf_wc, bAnd_wc] at h
    obtain ⟨hz, hrest⟩ := h
    cases k with
    | zero =>
      rw [List.getElem_cons_zero, Nat.add_zero]
      rcases hz with ⟨h3, h0⟩ | ⟨_, h5, h1⟩
      · exact Or.inl ⟨icode_three (Nat.eq_of_beq_eq_true h3), Nat.eq_of_beq_eq_true h0⟩
      · exact Or.inr ⟨icode_five (Nat.eq_of_beq_eq_true h5), Nat.eq_of_beq_eq_true h1⟩
    | succ k =>
      have hk' : k < t.length := by simpa using hk
      rw [List.getElem_cons_succ, show s + (k + 1) = s + 1 + k by omega]
      exact ih hrest k hk'

theorem wc_sound {LC : Nat → Nat} {w : List Int} (h : wcFrom LC w 0 = true) :
    ∀ k < w.length, (w[k]! = -1 ∧ LC k = 0) ∨ (w[k]! = -2 ∧ LC k = 1) := by
  intro k hk
  rw [getElem!_pos w k hk]
  simpa using wcFrom_spec h k hk

theorem frApply_sound {R : Nat → Nat} {x : Nat} (hR : ∀ i < 248, R i < 2 ^ 248) (_hx : x < 2 ^ 248) :
    frApply (frTable (rowsV R)) (v4OfNat x) = v4OfNat (vmT R x) :=
  V4.eq_of_toVec_eq (frApply_frTable_wf (rowsV_wf hR) _) (v4OfNat_wf (vmT_lt hR x))
    (frApply_rowsV x)

theorem mulRowsId_sound {X : Nat → Nat} (hX : ∀ i < 248, X i < 2 ^ 248) :
    mulRows (rowsV X) (idRows ()) = rowsV X := by
  apply Array.ext (by rw [mulRows_size])
  intro i h1 h2
  have hi : i < 248 := by rw [rowsV_size] at h2; exact h2
  have hXi : i < (rowsV X).size := by rw [rowsV_size]; exact hi
  change (Array.map (fun x => frApply (frTable (idRows ())) x) (rowsV X))[i]'(by
    rw [Array.size_map]; exact hXi) = _
  rw [Array.getElem_map, getElem_rowsV X hXi]
  apply V4.eq_of_toVec_eq (frApply_frTable_wf idRows_wf _) (v4OfNat_wf (hX i hi))
  have hone : ∀ j k : Fin 248, (((idRows ())[j.val]?).getD V4.zero).toVec k =
      (1 : Matrix (Fin 248) (Fin 248) (ZMod 2)) j k := fun j k => by
    rw [← rowsMatrix_apply, rowsMatrix_idRows]
  rw [frApply_frTable_toVec]
  funext k
  simp only [hone, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem inUAT_sound {Q : Nat → Nat} {x : Nat} (hQ : ∀ i < 248, Q i < 2 ^ 248) (hx : x < 2 ^ 248)
    (h : Nat.shiftRight (vmT Q x) 120 = 0) : inUAT (frTable (rowsV Q)) (v4OfNat x) = true := by
  have h' : vmT Q x >>> 120 = 0 := h
  rw [inUAT, frApply_sound hQ hx]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.not_eq_true']
  intro k hk
  by_cases hk' : k < 120
  · exact Or.inl hk'
  · right
    rw [v4OfNat_testBit _ (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, k = 120 + j := ⟨k - 120, by omega⟩
    rw [← Nat.testBit_shiftRight, h', Nat.zero_testBit]

end CFSG.KS.SporSch

end
