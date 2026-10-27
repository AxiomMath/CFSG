module

public import CFSG.Certificates.Kernel.Co2InvS.Mat
public import Certificates.Data.Kernel.Co2Smith.Rows
public import Certificates.Data.CFSGNative.Co2Smith.Check

public section

namespace CFSG.KC.Co2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.Sporadic.SmallF2.Native

theorem cK_eq (A : Nat) : cK A = A % 2 ^ 484 := by
  change A % _ = A % 2 ^ 484
  rw [show (2 : Nat) ^ 484 = nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642816 by decide]

theorem unpack_mod (A : Nat) : unpackR 22 (A % 2 ^ 484) = unpackR 22 A := by
  apply Array.ext
  · simp [unpackR]
  · intro i h1 h2
    have hi : i < 22 := by simpa [unpackR] using h1
    simp only [unpackR, Array.getElem_ofFn]
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    by_cases hj : j < 22
    · have : j + 22 * i < 484 := by omega
      simp [hj, this]
    · simp [hj]

theorem beq_unpack (A B : Nat) : (unpackR 22 A == unpackR 22 B) = eqK A B := by
  rw [eqK, cK_eq, cK_eq, ← unpack_mod A, ← unpack_mod B]
  exact unpack_beq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))

theorem bne_unpack (A B : Nat) : (unpackR 22 A != unpackR 22 B) = !eqK A B := by
  rw [bne, beq_unpack]

theorem eq_unpack_iff (A B : Nat) : unpackR 22 A = unpackR 22 B ↔ cK A = cK B := by
  have h := beq_unpack A B
  rw [eqK] at h
  constructor
  · intro e
    rw [e, beq_self_eq_true] at h
    exact Nat.eq_of_beq_eq_true h.symm
  · intro e
    rw [e, Nat.beq_refl] at h
    exact beq_iff_eq.1 h

theorem eq_unpack_of_eqK {A B : Nat} (h : eqK A B = true) : unpackR 22 A = unpackR 22 B :=
  (eq_unpack_iff A B).2 (Nat.eq_of_beq_eq_true h)

theorem wK_nil (P : Nat → Nat) : wK P [] = IDP := rfl

theorem wK_cons (P : Nat → Nat) (k : Nat) (w : List Nat) : wK P (k :: w) = mulV (P k) (wK P w) :=
  rfl

theorem wRows_unpack (L : Array (Array Nat)) (P : Nat → Nat) :
    ∀ w : List Nat, (∀ k ∈ w, L[k]! = unpackR 22 (P k)) →
      CFSG.Sporadic.Co2Smith.Native.wRows L w = unpackR 22 (wK P w)
  | [], _ => by rw [CFSG.Sporadic.Co2Smith.Native.wRows, wK_nil, idRows_eq]
  | k :: w, h => by
    rw [CFSG.Sporadic.Co2Smith.Native.wRows, wK_cons, h k (List.mem_cons_self ..),
      wRows_unpack L P w (fun j hj => h j (List.mem_cons_of_mem _ hj)), mulRows_unpack]

theorem powRows_unpack (A : Nat) : ∀ e : Nat, powRows 22 (unpackR 22 A) e = unpackR 22 (powK A e)
  | 0 => by rw [powRows, idRows_eq]; rfl
  | e + 1 => by
    rw [powRows, powRows_unpack A e, mulRows_unpack]
    rfl

theorem commRows_unpack (A B : Nat) :
    CFSG.Sporadic.Co2Smith.Native.commRows (unpackR 22 A) (unpackR 22 B) = commK A B := by
  rw [CFSG.Sporadic.Co2Smith.Native.commRows, mulRows_unpack, mulRows_unpack, beq_unpack, commK]

end CFSG.KC.Co2Smith
