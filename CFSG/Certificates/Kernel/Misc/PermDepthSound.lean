module

public import Certificates.Data.Kernel.Misc.PermDepth
public import CFSG.Certificates.Kernel.Misc.PermClosSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.Clos

open CFSG.KC.LQT

theorem depth_le {PA D : ℕ → ℕ} {dmax k : ℕ} (h : depthAt PA D dmax k = true) : D k ≤ dmax :=
  Nat.ble_eq.mp (P.andB_iff.1 h).1

theorem reach_of_tree {H : Type*} [Group H] {enc : H → ℕ} {M : ℕ → ℕ → ℕ} {one : ℕ}
    (henc : ClosEnc enc M one) (gens : List H) {G : ℕ → ℕ} {N dmax : ℕ} {E PA D : ℕ → ℕ}
    (hG : ∀ j < gens.length, G j = enc (gens.getD j 1))
    (ht : ∀ k < N, treeAt M one G gens.length E PA k = true)
    (hd : ∀ k < N, depthAt PA D dmax k = true)
    (R : ℕ → H → Prop) (h1 : R 0 1)
    (hstep : ∀ d g, ∀ l < gens.length, R d g → R (d + 1) (g * gens.getD l 1)) :
    ∀ k < N, ∃ g, enc g = E k ∧ R (D k) g := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hdk := (P.andB_iff.1 (hd k hk)).2
    cases k with
    | zero =>
      have h0 : Nat.beq (E 0) one = true := ht 0 hk
      have hd0 : Nat.beq (D 0) 0 = true := hdk
      refine ⟨1, by rw [henc.enc_one, Nat.eq_of_beq_eq_true h0], ?_⟩
      rw [Nat.eq_of_beq_eq_true hd0]
      exact h1
    | succ k =>
      have h : P.letB (PA (k + 1)) (fun r => P.letB (Nat.land r 16777215) fun p =>
          P.letB (Nat.shiftRight r 24) fun l => CFSG.KC.Ord.andB (Nat.blt p (k + 1))
            (CFSG.KC.Ord.andB (Nat.blt l gens.length) (Nat.beq (E (k + 1)) (M (E p) (G l))))) =
          true := ht (k + 1) hk
      have hdk' : Nat.beq (D (k + 1)) (D (Nat.land (PA (k + 1)) 16777215) + 1) = true := hdk
      rw [P.letB_eq, P.letB_eq, P.letB_eq] at h
      obtain ⟨hp, h⟩ := P.andB_iff.1 h
      obtain ⟨hl, h⟩ := P.andB_iff.1 h
      have hp' := Nat.blt_eq.mp hp
      have hl' := Nat.blt_eq.mp hl
      obtain ⟨g, hge, hgR⟩ := ih _ hp' (by omega)
      refine ⟨g * gens.getD (Nat.shiftRight (PA (k + 1)) 24) 1, ?_, ?_⟩
      · rw [henc.enc_mul, hge, ← hG _ hl']
        exact (Nat.eq_of_beq_eq_true h).symm
      · rw [Nat.eq_of_beq_eq_true hdk']
        exact hstep _ _ _ hl' hgR

end CFSG.KC.Misc.Clos

end
