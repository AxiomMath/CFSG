module

public import Certificates.Data.Kernel.Co1PRecsOK
public import CFSG.Certificates.Kernel.Co1PPinSound

public section

namespace CFSG.KC.Co1P

open CFSG.KLie.CT CFSG.KC.TreeK

theorem walkK_flag (act : Nat → Nat → Nat) (ng : Nat) : ∀ (rs : List (Nat × Nat)) (h n : Nat)
    (F B acc : List Nat), (walkK act ng rs h n F B acc).2 = recsOKK ng rs h n
  | [], _, _, _, _, _ => rfl
  | (p, l) :: rs, h, n, F, B, acc => by
    change (Bool.rec (motive := fun _ => List Nat × Bool) (Prod.mk acc false)
        (Prod.rec (motive := fun _ => List Nat × Bool) (fun F B =>
          (fun y => Prod.rec (motive := fun _ => List Nat × Bool)
            (fun F B => walkK act ng rs p (Nat.succ n) F B (List.cons y acc)) (pushQ y F B))
            (act l (headQ F))) (popsQ (Nat.sub p h) F B))
        (CFSG.KLie.CT.andB (Nat.ble h p) (CFSG.KLie.CT.andB (Nat.blt p n) (Nat.blt l ng)))).2 =
      CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.ble h p) (CFSG.KLie.CT.andB (Nat.blt p n) (Nat.blt l ng))) (recsOKK ng rs p (Nat.succ n))
    cases CFSG.KLie.CT.andB (Nat.ble h p) (CFSG.KLie.CT.andB (Nat.blt p n) (Nat.blt l ng))
    · rfl
    · have aux : ∀ (m : Nat) (a : List Nat) (q : List Nat × List Nat),
          (Prod.rec (motive := fun _ => List Nat × Bool) (fun F B => walkK act ng rs p m F B a) q).2 =
            recsOKK ng rs p m := by
        intro m a q
        rcases q with ⟨F1, B1⟩
        exact walkK_flag act ng rs p m F1 B1 a
      have aux2 : ∀ q : List Nat × List Nat, (Prod.rec (motive := fun _ => List Nat × Bool)
          (fun F B => (fun y => Prod.rec (motive := fun _ => List Nat × Bool)
            (fun F B => walkK act ng rs p (Nat.succ n) F B (List.cons y acc)) (pushQ y F B))
            (act l (headQ F))) q).2 = recsOKK ng rs p (Nat.succ n) := by
        intro q
        rcases q with ⟨F1, B1⟩
        exact aux _ _ _
      exact aux2 _

theorem ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by
  rw [Nat.ble_eq]
  exact h

theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem recsOKK_of_pins {ng : Nat} {R : Nat → Nat} : ∀ (rs : List (Nat × Nat)) (k h : Nat),
    recsEqK R rs k = true → (∀ j < rs.length, recAtK ng R (k + j) = true) →
    (0 < rs.length → h ≤ R k / 8) → recsOKK ng rs h (k + 1) = true
  | [], _, _, _, _, _ => rfl
  | r :: rs, k, h, hr, hc, hh => by
    have hr' : CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.beq r.1 (Nat.div (R k) 8)) (Nat.beq r.2 (Nat.mod (R k) 8)))
        (recsEqK R rs (k + 1)) = true := hr
    obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true hr'
    obtain ⟨h3, h4⟩ := CFSG.KC.TreeK.andB_true h1
    have e1 : r.1 = R k / 8 := Nat.eq_of_beq_eq_true h3
    have e2 : r.2 = R k % 8 := Nat.eq_of_beq_eq_true h4
    have c0 := hc 0 (by simp)
    rw [Nat.add_zero] at c0
    obtain ⟨-, c2⟩ := CFSG.KC.TreeK.andB_true c0
    obtain ⟨c3, c4⟩ := CFSG.KC.TreeK.andB_true c2
    have ih := recsOKK_of_pins rs (k + 1) (R k / 8) h2 (fun j hj => by
        have hj' := hc (j + 1) (by simp; omega)
        have e : k + (j + 1) = k + 1 + j := by omega
        rw [e] at hj'
        exact hj') (fun hpos => by
        have c1 := hc 1 (by simp; omega)
        obtain ⟨c5, -⟩ := CFSG.KC.TreeK.andB_true c1
        rcases orB_true c5 with c6 | c6
        · exact absurd (Nat.eq_of_beq_eq_true c6) (by omega)
        · exact Nat.le_of_ble_eq_true c6)
    change CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (Nat.ble h r.1) (CFSG.KLie.CT.andB (Nat.blt r.1 (k + 1)) (Nat.blt r.2 ng)))
      (recsOKK ng rs r.1 (k + 1 + 1)) = true
    have c3' : R k / 8 ≤ k := Nat.le_of_ble_eq_true c3
    have c4' : Nat.blt (R k % 8) ng = true := c4
    rw [e1, e2, ble_true (hh (by simp)), blt_true (Nat.lt_succ_of_le c3'), c4', ih]
    rfl

theorem treePts_flag (act : Nat → Nat → Nat) (ng root : Nat) (rs : List (Nat × Nat)) :
    (treePts act ng root rs).2 = recsOKK ng rs 0 1 := by
  unfold treePts
  rw [← walkK_flag act ng rs 0 1 [root] [] [root]]

end CFSG.KC.Co1P

end
