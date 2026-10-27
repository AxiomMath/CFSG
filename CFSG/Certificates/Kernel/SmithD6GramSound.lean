module

public import Certificates.Data.Kernel.SmithD6.GramCheck
public import CFSG.Certificates.Kernel.KeyTreeChunksSound
import CFSG.Certificates.Kernel.SmithD6WtSound

public section

namespace CFSG.KD.SmithD6

open CFSG.KC.KeyTree

@[expose] def FComb (bs : List Nat) : Prop :=
  ∃ x, 0 < x ∧ x < 4096 ∧ x &&& 63 = 0 ∧
    ∀ P : Nat → Prop, P 0 → (∀ y, P y → ∀ b ∈ bs, P (y ^^^ b)) → P x

theorem selGo_sound (d : Nat) : ∀ (bs : List Nat) (k : Nat) (P : Nat → Prop), P 0 →
    (∀ y, P y → ∀ b ∈ bs, P (y ^^^ b)) → P (selGo d bs k)
  | [], _, _, h0, _ => h0
  | b :: bs, k, P, h0, hcl => by
    have e : selGo d (b :: bs) k = (b * fld(d, k, 1)) ^^^ selGo d bs (k + 1) := rfl
    have hr := selGo_sound d bs (k + 1) P h0 fun y hy c hc => hcl y hy c (List.mem_cons_of_mem _ hc)
    rw [e, fld_one_eq]
    cases d.testBit k
    · simpa using hr
    · rw [cond_true, Nat.mul_one, Nat.xor_comm]
      exact hcl _ hr b List.mem_cons_self

theorem inFB_sound {x : Nat} (h : inFB x = true) : 0 < x ∧ x < 4096 ∧ x &&& 63 = 0 := by
  obtain ⟨h1, h⟩ := band_true h
  obtain ⟨h2, h3⟩ := band_true h
  exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3⟩

theorem selA_sound {d : Nat} {B : Array Nat} (h : selA d B = true) : FComb B.toList := by
  rcases B with ⟨bs⟩
  obtain ⟨h1, h2, h3⟩ := inFB_sound h
  exact ⟨_, h1, h2, h3, fun P h0 hcl => selGo_sound d bs 0 P h0 hcl⟩

theorem gramGo_sound : ∀ (ss : List Nat) (Bs : List (Array Nat)) (ds : List Nat),
    gramGo ss Bs ds = true → ∀ i < ss.length, i < Bs.length →
      (ss.getD i 0).testBit 31 = true ∨ FComb (Bs.getD i #[]).toList
  | [], _, _, _, i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, [], _, h, _, _, _ => by simp [gramGo] at h
  | _ :: _, _ :: _, [], h, _, _, _ => by simp [gramGo] at h
  | s :: ss, B :: Bs, d :: ds, h, i, hi, hB => by
    have e : gramGo (s :: ss) (B :: Bs) (d :: ds) = bAnd(Bool.rec (motive := fun _ => Bool)
        (selA d B) true (Nat.beq (fld(s, 31, 1)) 1), gramGo ss Bs ds) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := band_true h
    rcases i with _ | i
    · rw [List.getD_cons_zero, List.getD_cons_zero]
      cases hb : Nat.beq (fld(s, 31, 1)) 1
      · rw [hb] at h1
        exact Or.inr (selA_sound h1)
      · left
        have h3 := Nat.eq_of_beq_eq_true hb
        rw [fld_one_eq] at h3
        cases ht : s.testBit 31
        · rw [ht] at h3
          exact absurd h3 (by decide)
        · rfl
    · rw [List.getD_cons_succ, List.getD_cons_succ]
      exact gramGo_sound ss Bs ds h2 i (by simpa using hi) (by simpa using hB)

end CFSG.KD.SmithD6

end
