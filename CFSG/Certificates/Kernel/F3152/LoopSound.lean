module

public import Certificates.Data.Kernel.F3152.Forms
public import CFSG.Certificates.Kernel.Spor.F3LaneSound

public section

namespace CFSG.KS.F3152

open CFSG.F3.Native CFSG.KS.F3L

theorem eqV_iff {X Y : V} : eqV X Y = true ↔ X = Y := by
  unfold eqV
  cases h : Nat.beq X.p Y.p
  · constructor
    · intro e
      exact absurd e Bool.false_ne_true
    · rintro rfl
      rw [Nat.beq_refl] at h
      exact Bool.noConfusion h
  · have hp := Nat.eq_of_beq_eq_true h
    change Nat.beq X.m Y.m = true ↔ X = Y
    constructor
    · intro hm
      exact V.ext' hp (Nat.eq_of_beq_eq_true hm)
    · rintro rfl
      exact Nat.beq_refl _

theorem dropK_eq {α : Type} : ∀ (n : Nat) (L : List α), dropK n L = L.drop n
  | 0, L => rfl
  | n + 1, L => by
    change List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) (dropK n L) = _
    rw [dropK_eq n L, ← List.tail_drop]
    cases L.drop n <;> rfl

theorem nilK_iff {α : Type} (L : List α) : nilK L = true ↔ L = [] := by
  cases L
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => absurd h Bool.false_ne_true, fun h => nomatch h⟩

theorem linesK_spec {S : Nat → V} : ∀ {n : Nat} {L : List (Nat × Nat)} {r : Nat},
    linesK S n L r = true → ∀ t < n, ∃ N, L[t]? = some (N, 752) ∧ lineOK (S (r + t)) N = true
  | 0, _, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, [], _, h, _, _ => absurd h Bool.false_ne_true
  | n + 1, (N, len) :: L, r, h, t, ht => by
    change Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (linesK S n L (Nat.succ r)) (lineOK (S r) N)) (Nat.beq len 752) = true at h
    cases hl : Nat.beq len 752
    · rw [hl] at h
      exact absurd h Bool.false_ne_true
    rw [hl] at h
    cases hN : lineOK (S r) N
    · rw [hN] at h
      exact absurd h Bool.false_ne_true
    rw [hN] at h
    have hlen := Nat.eq_of_beq_eq_true hl
    subst hlen
    rcases t with _ | t
    · exact ⟨N, rfl, hN⟩
    · obtain ⟨N', h1, h2⟩ := linesK_spec h t (by omega)
      refine ⟨N', h1, ?_⟩
      have e : Nat.succ r + t = r + (t + 1) := by omega
      rw [e] at h2
      exact h2

theorem pullK_spec {At A : V} {G : Nat} {S : Nat → V} : ∀ {n r : Nat},
    pullK At A G S n r = true → ∀ t < n,
      (G >>> (12 * (r + t))) &&& 4095 < 3510 ∧
        mulK At (mulK (S ((G >>> (12 * (r + t))) &&& 4095)) A) = S (r + t)
  | 0, _, _, t, ht => absurd ht (Nat.not_lt_zero t)
  | n + 1, r, h, t, ht => by
    change strictT (Nat.land (Nat.shiftRight G (Nat.mul 12 r)) 4095) (fun x =>
      Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (pullK At A G S n (Nat.succ r)) (eqV (mulK At (mulK (S x) A)) (S r)))
        (Nat.blt x 3510)) = true at h
    rw [strictT_eq] at h
    cases hb : Nat.blt (Nat.land (Nat.shiftRight G (Nat.mul 12 r)) 4095) 3510
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    rw [hb] at h
    cases he : eqV (mulK At (mulK (S (Nat.land (Nat.shiftRight G (Nat.mul 12 r)) 4095)) A)) (S r)
    · rw [he] at h
      exact absurd h Bool.false_ne_true
    rw [he] at h
    rcases t with _ | t
    · exact ⟨Nat.le_of_ble_eq_true hb, eqV_iff.1 he⟩
    · have ih := pullK_spec h t (by omega)
      have e : Nat.succ r + t = r + (t + 1) := by omega
      rw [e] at ih
      exact ih

end CFSG.KS.F3152

end
