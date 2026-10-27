module

public import Certificates.Data.Kernel.G2Three.Sec1T1
public import CFSG.Certificates.Kernel.G2Three.Sec1Tab
import CFSG.Certificates.Kernel.Co1DceCover

public section

set_option exponentiation.threshold 512

namespace CFSG.KC.G2Three.Sec1

open Subgroup CFSG.KS.Mat3 CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.G2Three CFSG.KD.G2Three.Sec1
  CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

theorem SWP_eq (x : ℕ) : SWP x = x / 2 ^ 392 + x % 2 ^ 392 * 2 ^ 392 := by
  have hLP : LP = 2 ^ 392 - 1 := pow_sub_one_eq 392
  change x >>> 392 + (x &&& LP) <<< 392 = _
  rw [hLP, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]

theorem SWP_parts {x : ℕ} (hx : OkP x) :
    SWP x % 2 ^ 392 = x / 2 ^ 392 ∧ SWP x / 2 ^ 392 = x % 2 ^ 392 := by
  rw [SWP_eq]
  exact ⟨split_mod (lt_of_canon hx.2), split_div (lt_of_canon hx.2)⟩

theorem okP_SWP {x : ℕ} (hx : OkP x) : OkP (SWP x) := by
  obtain ⟨e1, e2⟩ := SWP_parts hx
  rw [OkP, e1, e2]
  exact ⟨hx.2, hx.1⟩

theorem wanti_conj (A B : Matrix (Fin 14) (Fin 14) (ZMod 3)) :
    wanti 1 1 * wdiag A B * wanti 1 1 = wdiag B A := by
  rw [wanti_mul_wdiag, wanti_mul_wanti, one_mul, one_mul, mul_one, mul_one]

theorem decP_SWP {x : ℕ} (hx : OkP x) : decP (SWP x) = wanti 1 1 * decP x * wanti 1 1 := by
  obtain ⟨e1, e2⟩ := SWP_parts hx
  rw [decP, decP, e1, e2, wanti_conj]

variable {G : Type} [Group G] (ρ : G →* Wm)

theorem enc_SWP {s : G} (hs : ρ s = wanti 1 1) (hs2 : s * s = 1) {x : ℕ} {g : G}
    (hx : Enc ρ x g) : Enc ρ (SWP x) (s * g * s⁻¹) := by
  have hsi : s⁻¹ = s := (eq_inv_of_mul_eq_one_left hs2).symm
  refine ⟨okP_SWP hx.1, ?_⟩
  rw [hsi, map_mul, map_mul, hs, hx.2, decP_SWP hx.1]

theorem closF_at {f : ℕ → ℕ → ℕ} {X G POS : ℕ → ℕ} {n k lo m hi : ℕ}
    (h : closF f X G POS n k lo m hi = true) (hm : m ≤ 64 * hi) :
    ∀ j < m, POS (lo + j) < n ∧ X (POS (lo + j)) = f (X ((lo + j) / k)) (G ((lo + j) % k)) :=
  fun j hj => by
  obtain ⟨h1, h2⟩ := bAnd_g2 (allBelow_g2 h hm j hj)
  exact ⟨Nat.blt_eq.mp h1, Nat.eq_of_beq_eq_true h2⟩

theorem bor_iff (a b : Bool) : Bool.rec (motive := fun _ => Bool) b true a = true ↔ a = true ∨ b = true := by
  cases a <;> simp

theorem cntMK_spec (X A B C : ℕ → ℕ) {k n hi : ℕ} (hn : n ≤ 64 * hi) :
    cntMK X A B C k n hi = ((Finset.range n).filter fun i => ∀ s < k,
      MULP (X i) (A s) = MULP (B s) (X i) ∨ MULP (X i) (A s) = MULP (C s) (X i)).card := by
  have hf : ∀ i, strictN (X i) (fun x => Bool.rec (motive := fun _ => ℕ) 0 1
      (allR k fun s => strictB (MULP x (A s)) fun y => Bool.rec (motive := fun _ => Bool)
        (Nat.beq y (MULP (C s) x)) true (Nat.beq y (MULP (B s) x)))) =
      if (∀ s < k, MULP (X i) (A s) = MULP (B s) (X i) ∨ MULP (X i) (A s) = MULP (C s) (X i))
        then 1 else 0 := by
    intro i
    rw [CFSG.KS.Mat3.strictN_eq3]
    generalize X i = x at *
    have key : (allR k fun s => strictB (MULP x (A s)) fun y =>
        Bool.rec (motive := fun _ => Bool) (Nat.beq y (MULP (C s) x)) true
          (Nat.beq y (MULP (B s) x))) = true ↔ ∀ s < k,
        MULP x (A s) = MULP (B s) x ∨ MULP x (A s) = MULP (C s) x := by
      rw [allR_iff]
      refine forall₂_congr fun s _ => ?_
      rw [strictB_eq, bor_iff, Nat.beq_eq, Nat.beq_eq]
    cases e : (allR k fun s => strictB (MULP x (A s)) fun y =>
        Bool.rec (motive := fun _ => Bool) (Nat.beq y (MULP (C s) x)) true
          (Nat.beq y (MULP (B s) x)))
    · have hp : ¬ ∀ s < k, MULP x (A s) = MULP (B s) x ∨ MULP x (A s) = MULP (C s) x :=
        fun h => absurd (key.2 h) (by rw [e]; decide)
      exact (if_neg hp).symm
    · exact (if_pos (key.1 e)).symm
  rw [Finset.card_filter]
  unfold cntMK
  rw [CFSG.Certificates.Co1D.sumBelow_spec _ hn]
  exact Finset.sum_congr rfl fun i _ => hf i

end CFSG.KC.G2Three.Sec1

end
