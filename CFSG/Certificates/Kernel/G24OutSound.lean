module

public import Certificates.Data.Kernel.G24Out
public import CFSG.Certificates.Kernel.G24KeySound

public section

namespace CFSG.KC.G24Key

open CFSG.KC.Enum CFSG.KC.Pack

theorem bIf_eq' (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c =
    (if c = true then t else e) := by
  cases c <;> rfl

theorem cosK_eq {S : ℕ → ℕ} {γ : ℕ → Pm} (hS : ∀ l, PtRep (S l) (γ l)) {T : ℕ} {t : Pm}
    (hT : PtRep T t) (TP TG : ℕ → ℕ) (f k : ℕ) (x : Fin 1365) :
    cosK S TP TG f T k x = ((treeE γ TP TG f k * t) x : ℕ) := by
  unfold cosK
  rw [hT, downK_eq hS TP TG f k (t x)]
  rfl

theorem recO_spec {S TP TG : ℕ → ℕ} {f T A B R k r : ℕ}
    (h : recO S TP TG f T A B R k r = true) :
    (Nat.land r 1 = 0 ∧ Nat.shiftRight r 1 < 3 ∧
        cosK S TP TG f T k (cosK S TP TG f T k (Nat.shiftRight r 1)) ≠ Nat.shiftRight r 1) ∨
      (Nat.land r 1 ≠ 0 ∧ ∀ b < 3,
        wpt A B (Nat.shiftRight r 10) (Nat.land (Nat.shiftRight r 2) 255)
            (cosK S TP TG f T k b) =
          ap R (wpt A B (Nat.shiftRight r 10) (Nat.land (Nat.shiftRight r 2) 255) b)) := by
  unfold recO at h
  simp only [strictB_eq, bIf_eq', Nat.beq_eq, Nat.blt_eq] at h
  by_cases hr : Nat.land r 1 = 0
  · rw [if_pos hr] at h
    by_cases h3 : Nat.shiftRight r 1 < 3
    · rw [if_pos h3] at h
      refine Or.inl ⟨hr, h3, fun e => ?_⟩
      rw [if_pos e] at h
      exact Bool.false_ne_true h
    · rw [if_neg h3] at h
      exact absurd h Bool.false_ne_true
  · rw [if_neg hr] at h
    exact Or.inr ⟨hr, fun b hb => Nat.eq_of_beq_eq_true (allN_spec h b hb)⟩

theorem ptsK_spec {f : ℕ → ℕ} {k : ℕ} (h : ptsK f k = true) : ∀ b < 3, f b = kpt k b :=
  fun b hb => Nat.eq_of_beq_eq_true (allN_spec h b hb)

theorem fixK_spec {S : ℕ → ℕ} {J n : ℕ} (h : fixK S J n = true) :
    ∀ q < n, q ≠ 0 → ∃ j < J, ap (S j) 0 = 0 ∧ ap (S j) q ≠ q := by
  intro q hq h0
  have h1 := allN_spec h q hq
  rw [bIf_eq', if_neg (fun e => h0 (Nat.eq_of_beq_eq_true e)), bIf_eq'] at h1
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hall : allN J (fun j => bIf(bAnd(Nat.beq (ap (S j) (nat_lit 0)) (nat_lit 0),
      bIf(Nat.beq (ap (S j) q) q, false, true)), false, true)) = true :=
    CFSG.KS.PackFld.allN_of_forall fun j hj => by
      rw [bIf_eq', bIf_eq', bIf_eq']
      by_cases e0 : ap (S j) 0 = 0
      · have e1 := hne j hj e0
        simp [e0, e1]
      · simp [e0]
  rw [if_pos hall] at h1
  exact Bool.false_ne_true h1

end CFSG.KC.G24Key

end
