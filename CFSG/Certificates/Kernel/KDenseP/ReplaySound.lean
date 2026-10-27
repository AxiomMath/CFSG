module

public import Certificates.Data.Kernel.KDenseP.Replay

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense

theorem rpAnd {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

theorem rpOr {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> simp [orB]

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem forceB_eq (s : St) (k : St → Bool) : forceB s k = andB (flagOf s) (k s) := by
  obtain ⟨f, X, A, W⟩ := s
  cases f
  · rfl
  · change strictB X (fun X' => strictB A (fun A' => strictB W (fun W' => k (true, X', A', W')))) = _
    rw [strictB_eq, strictB_eq, strictB_eq]
    rfl

theorem stEqN_self (n : Nat) (s : St) : stEqN n s s = flagOf s := by
  obtain ⟨f, X, A, W⟩ := s
  change andB f (andB f (andB (Nat.beq (normN SX n X) (normN SX n X))
    (andB (Nat.beq (normN SA n A) (normN SA n A)) (Nat.beq (normN SX n W) (normN SX n W))))) = f
  rw [Nat.beq_refl, Nat.beq_refl, Nat.beq_refl]
  cases f <;> rfl

theorem upd_eq (T : Nat → St) (j : Nat) (r : St) : upd T j r j = r := by
  change Bool.rec (motive := fun _ => St) (T j) r (Nat.beq j j) = r
  rw [Nat.beq_refl]

theorem upd_ne {T : Nat → St} {j x : Nat} (r : St) (h : x ≠ j) : upd T j r x = T x := by
  change Bool.rec (motive := fun _ => St) (T x) r (Nat.beq x j) = T x
  cases e : Nat.beq x j
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem updD_spec {D : Nat → Bool} {j x : Nat} (h : updD D j x = true) : x = j ∨ D x = true := by
  rcases rpOr.1 h with h | h
  · exact Or.inl (Nat.eq_of_beq_eq_true h)
  · exact Or.inr h

noncomputable def rlS (run : Nat → St → St) (CH PR : Nat → Nat) (S0 : Nat → St) (w x : Nat) : St :=
  if h : w ≤ x ∧ f20 (CH (PR x)) (nat_lit 3) < x then
    run (CH (PR x)) (rlS run CH PR S0 w (f20 (CH (PR x)) (nat_lit 3)))
  else S0 x
termination_by x
decreasing_by exact h.2

theorem rlS_lt {run : Nat → St → St} {CH PR : Nat → Nat} {S0 : Nat → St} {w x : Nat} (h : x < w) :
    rlS run CH PR S0 w x = S0 x := by
  have hn : ¬(w ≤ x ∧ f20 (CH (PR x)) (nat_lit 3) < x) := fun h' => absurd h'.1 (by omega)
  rw [rlS, dif_neg hn]

theorem rlS_prod {run : Nat → St → St} {CH PR : Nat → Nat} {S0 : Nat → St} {w x : Nat}
    (h1 : w ≤ x) (h2 : f20 (CH (PR x)) (nat_lit 3) < x) :
    rlS run CH PR S0 w x = run (CH (PR x)) (rlS run CH PR S0 w (f20 (CH (PR x)) (nat_lit 3))) := by
  rw [rlS, dif_pos ⟨h1, h2⟩]

theorem rpl_cons (run : Nat → St → St) (chk : (Nat → St) → Nat → Bool) (CH PR : Nat → Nat)
    (w k : Nat) (G : List Nat) (T : Nat → St) (D : Nat → Bool) :
    rpl run chk CH PR w (k :: G) T D = andB (D (f20 (CH k) (nat_lit 3)))
      (Bool.rec (motive := fun _ => Bool)
        (andB (D (f20 (CH k) (nat_lit 4))) (andB (chk T (CH k)) (rpl run chk CH PR w G T D)))
        (forceB (run (CH k) (T (f20 (CH k) (nat_lit 3))))
          (fun r => rpl run chk CH PR w G (upd T (f20 (CH k) (nat_lit 4)) r)
            (updD D (f20 (CH k) (nat_lit 4)))))
        (prodL PR w k (CH k))) := rfl

theorem rpl_spec {n : Nat} {run : Nat → St → St} {chk : (Nat → St) → Nat → Bool}
    (hloc : ∀ S S' c, S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) → chk S c = chk S' c)
    (hprod : ∀ S c, Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      chk S c = stEqN n (run c (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))))
    {CH PR : Nat → Nat} {S0 : Nat → St} {w : Nat} :
    ∀ (G : List Nat) (T : Nat → St) (D : Nat → Bool),
      (∀ x, D x = true → T x = rlS run CH PR S0 w x) → rpl run chk CH PR w G T D = true →
      ∀ k ∈ G, chk (rlS run CH PR S0 w) (CH k) = true
  | [], _, _, _, _, _, hk => by simp at hk
  | k :: G, T, D, hT, h, k', hk' => by
    rw [rpl_cons] at h
    obtain ⟨hi, h⟩ := rpAnd.1 h
    have eI := hT _ hi
    revert h
    cases hp : prodL PR w k (CH k) <;> intro h
    · dsimp only at h
      obtain ⟨hj, h⟩ := rpAnd.1 h
      obtain ⟨hc, hr⟩ := rpAnd.1 h
      rcases List.mem_cons.1 hk' with e | e
      · rw [e, hloc _ T (CH k) eI.symm (hT _ hj).symm]
        exact hc
      · exact rpl_spec hloc hprod G T D hT hr k' e
    · dsimp only at h
      rw [forceB_eq] at h
      obtain ⟨hfl, hr⟩ := rpAnd.1 h
      obtain ⟨hk1, hp⟩ := rpAnd.1 hp
      obtain ⟨hpr, hp⟩ := rpAnd.1 hp
      obtain ⟨hlt, hw⟩ := rpAnd.1 hp
      have hk1' : Nat.beq (f20 (CH k) (nat_lit 5)) (nat_lit 1) = false := by
        cases e : Nat.beq (f20 (CH k) (nat_lit 5)) (nat_lit 1)
        · rfl
        · rw [e] at hk1
          exact absurd hk1 (by decide)
      have hpr' : PR (f20 (CH k) (nat_lit 4)) = k := Nat.eq_of_beq_eq_true hpr
      rw [Nat.blt_eq] at hlt
      have hw' : w ≤ f20 (CH k) (nat_lit 4) := Nat.le_of_ble_eq_true hw
      have h2' : f20 (CH (PR (f20 (CH k) (nat_lit 4)))) (nat_lit 3) < f20 (CH k) (nat_lit 4) := by
        rw [hpr']
        exact hlt
      have eJ : rlS run CH PR S0 w (f20 (CH k) (nat_lit 4)) =
          run (CH k) (T (f20 (CH k) (nat_lit 3))) := by
        rw [rlS_prod hw' h2', hpr', ← eI]
      have hT' : ∀ x, updD D (f20 (CH k) (nat_lit 4)) x = true →
          upd T (f20 (CH k) (nat_lit 4)) (run (CH k) (T (f20 (CH k) (nat_lit 3)))) x =
            rlS run CH PR S0 w x := by
        intro x hx
        by_cases e : x = f20 (CH k) (nat_lit 4)
        · rw [e, upd_eq, eJ]
        · rw [upd_ne _ e]
          exact hT x ((updD_spec hx).resolve_left e)
      rcases List.mem_cons.1 hk' with e | e
      · rw [e, hprod _ _ hk1', eJ, ← eI, stEqN_self]
        exact hfl
      · exact rpl_spec hloc hprod G _ _ hT' hr k' e

theorem memB_spec {k : Nat} : ∀ {l : List Nat}, memB k l = true → k ∈ l
  | [], h => absurd h Bool.false_ne_true
  | a :: l, h => by
    rcases rpOr.1 (h : orB (Nat.beq a k) (memB k l) = true) with h | h
    · rw [Nat.eq_of_beq_eq_true h]
      exact List.mem_cons.2 (Or.inl rfl)
    · exact List.mem_cons.2 (Or.inr (memB_spec h))

theorem covL_spec {GK : Nat → Nat} {G : Nat → List Nat} {ng : Nat} :
    ∀ (nch : Nat), covL GK G ng nch = true → ∀ k < nch, GK k < ng ∧ k ∈ G (GK k)
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | nch + 1, h, k, hk => by
    have h' : andB _ (covL GK G ng nch) = true := h
    obtain ⟨h1, h2⟩ := rpAnd.1 h'
    by_cases hk' : k < nch
    · exact covL_spec nch h2 k hk'
    · have e : k = nch := by omega
      subst e
      obtain ⟨a, b⟩ := rpAnd.1 h1
      rw [Nat.blt_eq] at a
      exact ⟨a, memB_spec b⟩

theorem replay_sound {n : Nat} {run : Nat → St → St} {chk : (Nat → St) → Nat → Bool}
    (hloc : ∀ S S' c, S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) → chk S c = chk S' c)
    (hprod : ∀ S c, Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      chk S c = stEqN n (run c (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))))
    {CH PR GK : Nat → Nat} {G : Nat → List Nat} {S0 : Nat → St} {w ng nch : Nat}
    (hg : ∀ g < ng, grpL run chk CH PR G S0 w g = true) (hcov : covL GK G ng nch = true) :
    ∀ k < nch, chk (rlS run CH PR S0 w) (CH k) = true := by
  intro k hk
  obtain ⟨hgk, hmem⟩ := covL_spec nch hcov k hk
  refine rpl_spec hloc hprod (G (GK k)) S0 (fun x => Nat.blt x w) (fun x hx => ?_) (hg _ hgk) k hmem
  have hx' : Nat.blt x w = true := hx
  rw [Nat.blt_eq] at hx'
  exact (rlS_lt hx').symm

end CFSG.KC.KDenseP

end
