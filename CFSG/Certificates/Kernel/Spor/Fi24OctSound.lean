module

public import Certificates.Data.Kernel.Spor.Fi24Oct
public import CFSG.Certificates.Kernel.Spor.Fi24ThreeOSound

public section

namespace CFSG.KS.Fi24Oct

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit
  CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct CFSG.KS.Fi24ThreeO

variable {NW : Nat → Nat → Nat} {NT : Nat → Nat}

theorem orB_eqO (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem notB_eqO (a : Bool) : notB a = !a := by cases a <;> rfl

theorem rootOK_spec {we : List (List Nat × Nat)} (h : rootOK NW NT we = true) :
    ∀ e ∈ we, cP NW NT e.1 0 = e.2 := fun e he => by
  have := allL_spec h e he
  rw [← ptC_eq]
  exact Nat.eq_of_beq_eq_true this

theorem commOK_spec {we : List (List Nat × Nat)} (h : commOK NW NT we = true) :
    ∀ a ∈ we, ∀ b ∈ we, cP NW NT (dW a.1) b.2 = b.2 := fun a ha b hb => by
  have := allL_spec (allL_spec h a ha) b hb
  rw [← ptC_eq]
  exact Nat.eq_of_beq_eq_true this

@[expose] noncomputable def tri (NW : Nat → Nat → Nat) (NT : Nat → Nat) (s : Nat)
    (a b : List Nat × Nat) : Nat × Nat × Nat :=
  (a.2, b.2, ptC NW NT (dW a.1) (ptC NW NT (dW b.1) s))

theorem inner_eq (s : Nat) (a : List Nat × Nat) (base : List (Nat × Nat × Nat)) :
    ∀ t : List (List Nat × Nat),
      List.rec (motive := fun _ => List (Nat × Nat × Nat)) base
        (fun b _ jh => (a.2, b.2, ptC NW NT (dW a.1) (ptC NW NT (dW b.1) s)) :: jh) t =
        t.map (tri NW NT s a) ++ base
  | [] => rfl
  | b :: t => by
    change _ :: _ = _
    rw [inner_eq s a base t]
    rfl

theorem pv_cons (s : Nat) (a : List Nat × Nat) (t : List (List Nat × Nat)) :
    pv NW NT s (a :: t) = t.map (tri NW NT s a) ++ pv NW NT s t :=
  inner_eq s a _ t

theorem mem_pv (s : Nat) : ∀ (we : List (List Nat × Nat)) {i j : Nat} (hij : i < j)
    (hj : j < we.length), tri NW NT s (we[i]'(by omega)) we[j] ∈ pv NW NT s we
  | [], _, _, _, hj => absurd hj (by simp)
  | a :: t, i, j, hij, hj => by
    rw [pv_cons, List.mem_append]
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    cases i with
    | zero =>
      left
      exact List.mem_map.2 ⟨t[j]'(by simpa using hj), List.getElem_mem _, rfl⟩
    | succ i =>
      right
      exact mem_pv s t (by omega) (by simpa using hj)

theorem pairsOK_spec {s : Nat} {we : List (List Nat × Nat)} (h : pairsOK NW NT s we = true)
    {i j k l : Nat} (hij : i < j) (hkl : k < l) (hj : j < we.length) (hl : l < we.length)
    (hd : we[i].2 ≠ we[k].2 ∧ we[i].2 ≠ we[l].2 ∧ we[j].2 ≠ we[k].2 ∧ we[j].2 ≠ we[l].2) :
    cP NW NT (dW we[i].1) (cP NW NT (dW we[j].1) s) ≠
      cP NW NT (dW we[k].1) (cP NW NT (dW we[l].1) s) := by
  have hx := mem_pv (NW := NW) (NT := NT) s we hij hj
  have hy := mem_pv (NW := NW) (NT := NT) s we hkl hl
  have e := allL_spec (allL_spec h _ hx) _ hy
  unfold meetP tri at e
  simp only [orB_eqO, notB_eqO, Bool.or_eq_true, Bool.not_eq_true'] at e
  rw [← ptC_eq, ← ptC_eq, ← ptC_eq, ← ptC_eq]
  intro hv
  rcases e with ((e | e | e | e) | e)
  · exact hd.1 (Nat.eq_of_beq_eq_true e)
  · exact hd.2.1 (Nat.eq_of_beq_eq_true e)
  · exact hd.2.2.1 (Nat.eq_of_beq_eq_true e)
  · exact hd.2.2.2 (Nat.eq_of_beq_eq_true e)
  · rw [hv] at e
    exact absurd (Nat.beq_refl _) (by rw [e]; decide)

@[expose] noncomputable def triR (NW : Nat → Nat → Nat) (NT : Nat → Nat)
    (a b : List Nat × Nat × Nat) : Nat × Nat × Nat :=
  (a.2.1, b.2.1, ptC NW NT (dW a.1) b.2.2)

theorem innerR_eq (a : List Nat × Nat × Nat) (base : List (Nat × Nat × Nat)) :
    ∀ t : List (List Nat × Nat × Nat),
      List.rec (motive := fun _ => List (Nat × Nat × Nat)) base
        (fun b _ jh => (a.2.1, b.2.1, ptC NW NT (dW a.1) b.2.2) :: jh) t =
        t.map (triR NW NT a) ++ base
  | [] => rfl
  | b :: t => by
    change _ :: _ = _
    rw [innerR_eq a base t]
    rfl

theorem pvR_cons (a : List Nat × Nat × Nat) (t : List (List Nat × Nat × Nat)) :
    pvR NW NT (a :: t) = t.map (triR NW NT a) ++ pvR NW NT t :=
  innerR_eq a _ t

theorem pv_map_eq (s : Nat) : ∀ wv : List (List Nat × Nat × Nat),
    (∀ e ∈ wv, ptC NW NT (dW e.1) s = e.2.2) →
      pv NW NT s (wv.map fun e => (e.1, e.2.1)) = pvR NW NT wv
  | [], _ => rfl
  | a :: t, h => by
    rw [List.map_cons, pv_cons, pvR_cons,
      pv_map_eq s t (fun e he => h e (List.mem_cons_of_mem a he)), List.map_map]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    change (a.2.1, b.2.1, ptC NW NT (dW a.1) (ptC NW NT (dW b.1) s)) =
      (a.2.1, b.2.1, ptC NW NT (dW a.1) b.2.2)
    rw [h b (List.mem_cons_of_mem a hb)]

theorem pairsOK_of_R {s : Nat} {wv : List (List Nat × Nat × Nat)} (h1 : svOK NW NT s wv = true)
    (h2 : pairsR NW NT wv = true) : pairsOK NW NT s (wv.map fun e => (e.1, e.2.1)) = true := by
  have hp := pv_map_eq s wv fun e he => Nat.eq_of_beq_eq_true (allL_spec h1 e he)
  unfold pairsOK
  rw [hp]
  exact h2

theorem normOK_spec {N : List Nat} {pq : List (Nat × Nat)} (h : normOK NW NT N pq = true) :
    ∀ e ∈ pq, cP NW NT N e.1 = e.2 := fun e he => by
  have := allL_spec h e he
  rw [← ptC_eq]
  exact Nat.eq_of_beq_eq_true this

theorem cP_prodC (w : List Nat) (ws : List (List Nat)) (x : Nat) :
    cP NW NT (prodC (w :: ws)) x = cP NW NT (dW w) (cP NW NT (prodC ws) x) :=
  cP_append _ _ x

theorem prodOK_spec (hV : VN NW NT) {ws : List (List Nat)} (h : prodOK NW NT ws = true) :
    ∀ x < 306936, cP NW NT (prodC ws) x = x := by
  intro x hx
  have e : fixC NW NT (prodC ws) = ptsM := Nat.eq_of_beq_eq_true h
  have hb : (fixC NW NT (prodC ws)).testBit x = true := by
    rw [e]
    exact ptsM_bit hx
  exact ((testBit_fixC hV _ x).1 hb).2

theorem prodOK_of_planes {ws : List (List Nat)}
    (h0 : wkC NW NT (prodC ws) (Fi24FixP.idPl19 0) = Fi24FixP.idPl19 0)
    (hk : ∀ k < 18, wkC NW NT (prodC ws) (Nat.xor (Fi24FixP.idPl19 (k + 1)) (Fi24FixP.idPl19 0)) =
      Nat.xor (Fi24FixP.idPl19 (k + 1)) (Fi24FixP.idPl19 0)) :
    prodOK NW NT ws = true := by
  have hxs : ∀ a : Nat, Nat.xor a a = 0 := Nat.xor_self
  have hx0 : ∀ a : Nat, Nat.xor a 0 = a := Nat.xor_zero
  have hxa : ∀ a b c : Nat, Nat.xor (Nat.xor a b) c = Nat.xor a (Nat.xor b c) := Nat.xor_assoc
  have hs : ∀ k, k ≤ 19 → Fi24FixP.fixAcc (wkC NW NT (prodC ws)) (Fi24FixP.idPl19 0) k = ptsM := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk19
      rw [CFSG.KS.Fi24FixP.fixAcc_succ, ih (by omega)]
      unfold Fi24FixP.fixStep
      have e : Nat.xor (nIf(Nat.beq k (nat_lit 0), Fi24FixP.idPl19 0,
          Nat.xor (wkC NW NT (prodC ws) (Nat.xor (Fi24FixP.idPl19 k) (Fi24FixP.idPl19 (nat_lit 0))))
            (Fi24FixP.idPl19 0))) (Fi24FixP.idPl19 k) = 0 := by
        cases k with
        | zero => exact hxs _
        | succ j =>
          change Nat.xor (Nat.xor (wkC NW NT (prodC ws) (Nat.xor (Fi24FixP.idPl19 (j + 1))
            (Fi24FixP.idPl19 0))) (Fi24FixP.idPl19 0)) (Fi24FixP.idPl19 (j + 1)) = 0
          rw [hk j (by omega), hxa (Fi24FixP.idPl19 (j + 1)) (Fi24FixP.idPl19 0) (Fi24FixP.idPl19 0),
            hxs (Fi24FixP.idPl19 0), hx0 (Fi24FixP.idPl19 (j + 1)), hxs (Fi24FixP.idPl19 (j + 1))]
      rw [e, hx0]
      decide +kernel
  change Nat.beq (strictN (wkC NW NT (prodC ws) (Fi24FixP.idPl19 (nat_lit 0)))
    (fun P0 => Fi24FixP.fixAcc (wkC NW NT (prodC ws)) P0 (nat_lit 19))) ptsM = true
  rw [CFSG.KS.Fi24FixP.strictN_eq, h0, hs 19 (Nat.le_refl _)]
  exact Nat.beq_refl _

end CFSG.KS.Fi24Oct

end
