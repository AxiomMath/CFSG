module

public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KS.CB

open CFSG.KC.Enum CFSG.ONSchreier.Native

@[expose] noncomputable def trInvK (PAR LAB : Nat → Nat) (INV : Nat → Nat → Nat) (fuel : Nat) :
    Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih k p => nIf(Nat.beq k (nat_lit 0), p, ih (PAR k) (INV (LAB k) p))) fuel

theorem trInvApp_eq {n m r : Nat} {PTS POS PAR LAB : Nat → Nat} {INV : Nat → Nat → Nat}
    {invs : Array (Array Nat)} (hm : ∀ k < m, PAR k < m ∧ LAB k < r)
    (hinv : ∀ j < r, ∀ x < n, invs[j]![x]! = INV j x ∧ INV j x < n) :
    ∀ (fuel k p : Nat), k < m → p < n →
      trInvApp invs ⟨Array.ofFn (n := m) fun k => PTS k.val, Array.ofFn (n := n) fun z => POS z.val,
        Array.ofFn (n := m) fun k => PAR k.val, Array.ofFn (n := m) fun k => LAB k.val⟩ fuel k p =
      trInvK PAR LAB INV fuel k p
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, p, hk, hp => by
    unfold trInvApp
    by_cases h0 : k = 0
    · subst h0
      rfl
    · have hbk : (k == 0) = false := by simpa using h0
      simp only [hbk, Bool.false_eq_true, ↓reduceIte]
      have e1 : (Array.ofFn (n := m) fun k => PAR k.val)[k]! = PAR k := by
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
      have e2 : (Array.ofFn (n := m) fun k => LAB k.val)[k]! = LAB k := by
        rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
      rw [e1, e2, (hinv (LAB k) (hm k hk).2 p hp).1,
        trInvApp_eq hm hinv fuel (PAR k) (INV (LAB k) p) (hm k hk).1 (hinv (LAB k) (hm k hk).2 p hp).2]
      change _ = nIf(Nat.beq k (nat_lit 0), p, trInvK PAR LAB INV fuel (PAR k) (INV (LAB k) p))
      have hb0 : Nat.beq k (nat_lit 0) = false := by
        cases k with
        | zero => exact absurd rfl h0
        | succ k => rfl
      rw [hb0]

end CFSG.KS.CB

end
