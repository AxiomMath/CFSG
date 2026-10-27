module

public import Certificates.Data.Kernel.LocalQT.Outer
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck

public section

namespace CFSG.KC.LQT.W

open Equiv CFSG.QuasithinUnique.Setup.X1

theorem outer_sound {n : ℕ} (S : List (Perm (Fin n))) (r : Perm (Fin n))
    (e : List (List ℤ) × List ℤ) {LS : List ℕ} {cr : ℕ} (hS : S.map codeP = LS)
    (hr : codeP r = cr) (hk : outerC n cr LS e.1 e.2 = true) :
    ((e.1.map (evalG S)).length == 3 && decide
      (evalG ((e.1.map (evalG S)).map fun x => r * (x * r * x⁻¹)) e.2 ^ 11 = 1 ∧
        evalG ((e.1.map (evalG S)).map fun x => r * (x * r * x⁻¹)) e.2 ≠ 1)) = true := by
  subst hS hr
  have hc : (codeP : Perm (Fin n) → ℕ) = P.code := rfl
  unfold outerC at hk
  rw [P.andB_iff, P.andB_iff, P.letB_eq] at hk
  obtain ⟨hn, hl, hk⟩ := hk
  have hn : n ≤ 32 := Nat.le_of_ble_eq_true hn
  have hev : ∀ (L : List (Perm (Fin n))) (w : List ℤ),
      evalZK n (L.map codeP) w = P.code (evalG L w) := by
    intro L w
    induction w with
    | nil => exact P.code_one
    | cons z w ih =>
      change P.mul n (letZ n (L.map codeP) z) (evalZK n (L.map codeP) w) = _
      rw [ih, evalG]
      have hz : letZ n (L.map codeP) z = P.code (if 0 < z then L.getD (z.toNat - 1) 1
          else (L.getD ((-z).toNat - 1) 1)⁻¹) := by
        rcases z with (_ | k) | k
        · change P.inv n (genAt n (L.map codeP) 0) = _
          rw [genAt_map, P.code_inv hn]
          rfl
        · change genAt n (L.map codeP) k = _
          rw [genAt_map]
          congr 1
          have h0 : (0 : ℤ) < Int.ofNat (k + 1) := Int.ofNat_lt.2 (Nat.succ_pos k)
          rw [ite_eq_left h0]
          simp
        · change P.inv n (genAt n (L.map codeP) k) = _
          rw [genAt_map, P.code_inv hn]
          congr 1
      rw [hz, P.code_mul hn]
  have hmap : (e.1.map fun k => P.mul n (codeP r) (P.mul n (P.mul n (evalZK n (S.map codeP) k)
      (codeP r)) (P.inv n (evalZK n (S.map codeP) k)))) =
      ((e.1.map (evalG S)).map fun x => r * (x * r * x⁻¹)).map codeP := by
    simp only [List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, hev]
    simp only [hc, P.code_inv hn, P.code_mul hn]
  rw [hmap, hev, P.andB_iff, P.notB_iff, P.code_pow hn, P.code_one, P.beq_code hn,
    P.beq_code hn] at hk
  have hlen : ∀ l : List (List ℤ),
      List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) l = l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      change Nat.succ _ = _
      rw [ih]
      rfl
  rw [P.beq_iff, hlen] at hl
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_map]
  exact ⟨hl, hk⟩

end CFSG.KC.LQT.W

end
