module

public import CFSG.Certificates.Kernel.HMathieu.GreedySound
public import CFSG.Quasithin.Background.HMathieuChain

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

variable {P : Type} [Group P] [DecidableEq P]

theorem forallGreedyAll_mats {R : List P} {D : List (Nat × Nat)}
    (T : GTabs R (cmD D) (mkD D)) (hD : D.length = R.length) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (act : P → Nat → Nat) (M : List (List Nat))
    (hM : ∀ k ≤ R.length, act (el R k) = actM (M.getD k []))
    (pr : {X : Type} → (X → Nat → Nat) → List X → Bool)
    (hpr : ∀ {X Y : Type} (a : X → Nat → Nat) (a' : Y → Nat → Nat) (g : X → Y) (l : List X),
      (∀ x ∈ l, a x = a' (g x)) → pr a l = pr a' (l.map g)) (k : Nat)
    (hK : gAllR R.length (fun st y => M.getD y [] :: st) (fun _ _ st => pr actM st) k []
      [R.length] (2 ^ R.length - 1) [] D 0 = true) :
    forallGreedyAll posF R (pr act) k [] = true := by
  have hel : ∀ x ∈ R, act x = actM (M.getD (R.idxOf x) []) := by
    intro x hx
    rw [← hM _ (idxOf_le x), el_idxOf (Or.inl hx)]
  rw [forallGreedyAll_eq_gAllS_nil T hpos (pr act) (fun st y => M.getD y [] :: st)
    (fun _ _ st => pr actM st) (fun l => l.map fun x => M.getD (R.idxOf x) [])
    (fun _ _ _ _ _ => rfl) (fun l hl _ => hpr _ _ _ l fun x hx => hel x (hl x hx)) k,
    List.map_nil, ← gAllR_eq hD _ _ k [] [R.length] _ [] (by simp [startK])]
  exact hK

theorem forallGreedyAll_matsL {R : List P} {D : List (Nat × Nat)}
    (T : GTabs R (cmD D) (mkD D)) (hD : D.length = R.length) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (M : List (List Nat)) (pred : List P → Bool)
    (predK : List Nat → List Nat → List (List Nat) → Bool)
    (hpred : ∀ l, (∀ y ∈ l, y ∈ R) → IndepList l → pred l = predK (l.map R.idxOf)
      ((subprods l).map R.idxOf) (l.map fun x => M.getD (R.idxOf x) [])) (k : Nat)
    (hK : gAllR R.length (fun st y => M.getD y [] :: st) predK k [] [R.length]
      (2 ^ R.length - 1) [] D 0 = true) :
    forallGreedyAll posF R pred k [] = true := by
  rw [forallGreedyAll_eq_gAllS_nil T hpos pred (fun st y => M.getD y [] :: st) predK
    (fun l => l.map fun x => M.getD (R.idxOf x) []) (fun _ _ _ _ _ => rfl) hpred k,
    List.map_nil, ← gAllR_eq hD _ _ k [] [R.length] _ [] (by simp [startK])]
  exact hK

theorem fixMasks_cons' {X : Type} (n : Nat) (act : X → Nat → Nat) (x : X) (l : List X) :
    fixMasks n act (x :: l) = (fixMasks n act l).filter fun m => act x m == m := by
  unfold fixMasks
  rw [List.filter_filter]
  refine List.filter_congr fun m _ => ?_
  rw [List.all_cons, Bool.and_comm]

theorem fixMasks_nil {X : Type} (n : Nat) (act : X → Nat → Nat) :
    fixMasks n act [] = List.range (2 ^ n) := by
  unfold fixMasks
  simp

@[expose] def fixSt (n : Nat) (Ms : List (List Nat)) : List (List Nat) × List Nat :=
  (Ms, fixMasks n actM Ms)

theorem forallGreedyAll_fix {R : List P} {D : List (Nat × Nat)}
    (T : GTabs R (cmD D) (mkD D)) (hD : D.length = R.length) {posF : P → Nat}
    (hpos : ∀ x, posF x = R.idxOf x) (M : List (List Nat)) (n : Nat) (pred : List P → Bool)
    (predK : List Nat → List Nat → List (List Nat) × List Nat → Bool)
    (hpred : ∀ l, (∀ y ∈ l, y ∈ R) → IndepList l → pred l = predK (l.map R.idxOf)
      ((subprods l).map R.idxOf) (fixSt n (l.map fun x => M.getD (R.idxOf x) []))) (k : Nat)
    (hK : gAllR R.length (fun st y => (M.getD y [] :: st.1,
        st.2.filter fun m => actM (M.getD y []) m == m)) predK k [] [R.length]
      (2 ^ R.length - 1) ([], List.range (2 ^ n)) D 0 = true) :
    forallGreedyAll posF R pred k [] = true := by
  rw [forallGreedyAll_eq_gAllS_nil T hpos pred _ predK
    (fun l => fixSt n (l.map fun x => M.getD (R.idxOf x) [])) (fun x l _ _ _ => ?_) hpred k]
  · simp only [List.map_nil, fixSt, fixMasks_nil]
    rw [← gAllR_eq hD _ _ k [] [R.length] _ _ (by simp [startK])]
    exact hK
  · simp only [fixSt, List.map_cons, fixMasks_cons']

end CFSG.KC.HMathieu

end
