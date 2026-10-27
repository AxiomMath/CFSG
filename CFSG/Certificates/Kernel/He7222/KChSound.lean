module

public import Certificates.Data.Kernel.He7222.KChain
import Mathlib.Data.List.GetD
import CFSG.Certificates.Kernel.OrbRow.LevelSound
public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.KC.HeChain

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KS.PF

theorem drop_facts {α : Type*} {x : α} {L l : List α} {i : ℕ} (hL : x :: L = l.drop i) :
    ∃ hi : i < l.length, l[i] = x ∧ L = l.drop (i + 1) := by
  have hi : i < l.length := by
    rcases Nat.lt_or_ge i l.length with h1 | h1
    · exact h1
    · have : l.drop i = [] := List.drop_eq_nil_iff.mpr h1
      rw [this] at hL
      exact absurd hL (List.cons_ne_nil _ _)
  refine ⟨hi, ?_, ?_⟩
  · have := congrArg List.head? hL
    rw [List.head?_cons, List.head?_drop, List.getElem?_eq_getElem hi] at this
    exact (Option.some.inj this).symm
  · have := congrArg List.tail hL
    rw [List.tail_cons, List.tail_drop] at this
    exact this

theorem kgW_sound {n w m idn : ℕ} {Ts : List (List ℕ)} {s : ℕ} {G : List ℕ}
    {U : List (List ℕ)} : ∀ (L : List (List ℕ)) (q : ℕ), L = U.drop q → q ≤ U.length →
    List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.beq q (lenS G))
      (fun u _ ih q => strictB (getS G q) (fun g =>
        bAnd(tupOK Ts u, bAnd(Nat.beq (tupK n w m idn Ts u) g,
          bAnd(commK n w m (Nat.mul n w) g s, strictB (Nat.succ q) ih))))) L q = true →
    U.length = G.length ∧ ∀ i, q ≤ i → i < U.length →
      tupOK Ts (U.getD i []) = true ∧ tupK n w m idn Ts (U.getD i []) = G.getD i 0 ∧
      commK n w m (n * w) (G.getD i 0) s = true := by
  intro L
  induction L with
  | nil =>
    intro q hL hq h
    have hU : U.length ≤ q := List.drop_eq_nil_iff.mp hL.symm
    have h' : Nat.beq q (lenS G) = true := h
    rw [lenS_eq] at h'
    have := Nat.eq_of_beq_eq_true h'
    exact ⟨by omega, fun i hi hi' => absurd hi' (by omega)⟩
  | cons u L ih =>
    intro q hL hq h
    obtain ⟨hqU, hu, hL'⟩ := drop_facts hL
    have h' : strictB (getS G q) (fun g =>
        bAnd(tupOK Ts u, bAnd(Nat.beq (tupK n w m idn Ts u) g,
          bAnd(commK n w m (Nat.mul n w) g s, strictB (Nat.succ q)
            (List.rec (motive := fun _ => Nat → Bool) (fun q => Nat.beq q (lenS G))
              (fun u _ ih q => strictB (getS G q) (fun g =>
                bAnd(tupOK Ts u, bAnd(Nat.beq (tupK n w m idn Ts u) g,
                  bAnd(commK n w m (Nat.mul n w) g s, strictB (Nat.succ q) ih))))) L))))) =
        true := h
    rw [strictB_eqP (getS G q)] at h'
    simp only [bAnd_iff] at h'
    obtain ⟨ht, he, hc, hrest⟩ := h'
    rw [strictB_eqP] at hrest
    obtain ⟨hlen, hall⟩ := ih (q + 1) hL' hqU hrest
    refine ⟨hlen, fun i hi hiU => ?_⟩
    rcases Nat.lt_or_ge q i with hqi | hqi
    · exact hall i hqi hiU
    have : i = q := by omega
    subst this
    rw [List.getD_eq_getElem _ _ hqU, hu, ← getS_eq]
    exact ⟨ht, Nat.eq_of_beq_eq_true he, hc⟩

theorem kgK_sound {n w m idn : ℕ} {Ts : List (List ℕ)} {s : ℕ} {G : List ℕ}
    {U : List (List ℕ)} (h : kgK n w m idn Ts s G U = true) :
    U.length = G.length ∧ ∀ i < U.length,
      tupOK Ts (U.getD i []) = true ∧ tupK n w m idn Ts (U.getD i []) = G.getD i 0 ∧
      commK n w m (n * w) (G.getD i 0) s = true := by
  obtain ⟨h1, h2⟩ := kgW_sound U 0 rfl (Nat.zero_le _) h
  exact ⟨h1, fun i hi => h2 i (Nat.zero_le _) hi⟩

@[expose] def chainGens (G0 : List ℕ) (S : List (List ℕ)) (i : ℕ) : List ℕ :=
  if i = 0 then G0 else S.getD (i - 1) []

theorem chainW_sound {n w m idn : ℕ} {G0 B : List ℕ} {R T S Ref Nn : List (List ℕ)} :
    ∀ (L : List (List ℕ)) (i : ℕ) (G : List ℕ), L = T.drop i → i ≤ T.length →
    (i < B.length → G = chainGens G0 S i) →
    List.rec (motive := fun _ => Nat → List Nat → Bool) (fun i _ => Nat.beq i (lenS B))
      (fun Ti _ ih i G => bAnd(treeK n w m idn G (getS B i) (getLs R i) Ti,
        strictB (Nat.succ i) (fun i' => bIf(Nat.blt i' (lenS B),
          bAnd(schK n w m G (getS B i) (getLs R i) Ti (getLs Ref i') (getLs Nn i) (getLs S i),
            ih i' (getLs S i)),
          ih i' G)))) L i G = true →
    T.length = B.length ∧ ∀ j, i ≤ j → j < T.length →
      treeK n w m idn (chainGens G0 S j) (B.getD j 0) (R.getD j []) (T.getD j []) = true ∧
      (j + 1 < B.length → schK n w m (chainGens G0 S j) (B.getD j 0) (R.getD j [])
        (T.getD j []) (Ref.getD (j + 1) []) (Nn.getD j []) (S.getD j []) = true) := by
  intro L
  induction L with
  | nil =>
    intro i G hL hi _ h
    have hT : T.length ≤ i := List.drop_eq_nil_iff.mp hL.symm
    have h' : Nat.beq i (lenS B) = true := h
    rw [lenS_eq] at h'
    have := Nat.eq_of_beq_eq_true h'
    exact ⟨by omega, fun j hj hj' => absurd hj' (by omega)⟩
  | cons Ti L ih =>
    intro i G hL hi hG0 h
    obtain ⟨hiT, hTi, hL'⟩ := drop_facts hL
    have h' : bAnd(treeK n w m idn G (getS B i) (getLs R i) Ti,
        strictB (Nat.succ i) (fun i' => bIf(Nat.blt i' (lenS B),
          bAnd(schK n w m G (getS B i) (getLs R i) Ti (getLs Ref i') (getLs Nn i) (getLs S i),
            List.rec (motive := fun _ => Nat → List Nat → Bool) (fun i _ => Nat.beq i (lenS B))
              (fun Ti _ ih i G => bAnd(treeK n w m idn G (getS B i) (getLs R i) Ti,
                strictB (Nat.succ i) (fun i' => bIf(Nat.blt i' (lenS B),
                  bAnd(schK n w m G (getS B i) (getLs R i) Ti (getLs Ref i') (getLs Nn i)
                    (getLs S i), ih i' (getLs S i)),
                  ih i' G)))) L i' (getLs S i)),
          List.rec (motive := fun _ => Nat → List Nat → Bool) (fun i _ => Nat.beq i (lenS B))
              (fun Ti _ ih i G => bAnd(treeK n w m idn G (getS B i) (getLs R i) Ti,
                strictB (Nat.succ i) (fun i' => bIf(Nat.blt i' (lenS B),
                  bAnd(schK n w m G (getS B i) (getLs R i) Ti (getLs Ref i') (getLs Nn i)
                    (getLs S i), ih i' (getLs S i)),
                  ih i' G)))) L i' G))) = true := h
    rw [bAnd_iff, strictB_eqP (Nat.succ i)] at h'
    obtain ⟨htr, hrest⟩ := h'
    have hTj : T.getD i [] = Ti := by rw [List.getD_eq_getElem _ _ hiT, hTi]
    rcases Bool.eq_false_or_eq_true (Nat.blt (i + 1) (lenS B)) with hb | hb
    · have hb' : i + 1 < B.length := by rw [← lenS_eq]; exact Nat.blt_eq.mp hb
      rw [hb, bAnd_iff] at hrest
      obtain ⟨hs, hrest'⟩ := hrest
      have hG' : i + 1 < B.length → getLs S i = chainGens G0 S (i + 1) := fun _ => by
        rw [chainGens, if_neg (by omega), getLs_eq]
        rfl
      obtain ⟨hlen, hall⟩ := ih (i + 1) _ hL' hiT hG' hrest'
      refine ⟨hlen, fun j hj hjT => ?_⟩
      rcases Nat.lt_or_ge i j with hij | hij
      · exact hall j hij hjT
      have : j = i := by omega
      subst this
      rw [hTj, ← hG0 (by omega), ← getS_eq, ← getLs_eq]
      refine ⟨htr, fun _ => ?_⟩
      rw [← getLs_eq, ← getLs_eq, ← getLs_eq]
      exact hs
    · have hb' : ¬ i + 1 < B.length := by
        rw [← lenS_eq]
        intro hc
        rw [Nat.blt_eq.mpr hc] at hb
        exact absurd hb (by simp)
      rw [hb] at hrest
      obtain ⟨hlen, hall⟩ := ih (i + 1) G hL' hiT (fun h => absurd h hb') hrest
      refine ⟨hlen, fun j hj hjT => ?_⟩
      rcases Nat.lt_or_ge i j with hij | hij
      · exact hall j hij hjT
      have : j = i := by omega
      subst this
      rw [hTj, ← hG0 (by omega), ← getS_eq, ← getLs_eq]
      exact ⟨htr, fun h => absurd h hb'⟩

theorem chainK_sound {n w m idn : ℕ} {G0 B : List ℕ} {R T S Ref Nn : List (List ℕ)}
    (h : chainK n w m idn G0 B R T S Ref Nn = true) :
    T.length = B.length ∧ ∀ j < T.length,
      treeK n w m idn (chainGens G0 S j) (B.getD j 0) (R.getD j []) (T.getD j []) = true ∧
      (j + 1 < B.length → schK n w m (chainGens G0 S j) (B.getD j 0) (R.getD j [])
        (T.getD j []) (Ref.getD (j + 1) []) (Nn.getD j []) (S.getD j []) = true) := by
  obtain ⟨h1, h2⟩ := chainW_sound T 0 G0 rfl (Nat.zero_le _) (fun _ => rfl) h
  exact ⟨h1, fun j hj => h2 j (Nat.zero_le _) hj⟩

theorem invLW_sound {n w m idn : ℕ} {T TI : List ℕ} : ∀ (L : List ℕ) (j : ℕ), L = T.drop j →
    j ≤ T.length →
    List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (lenS TI))
      (fun t _ ih j => bAnd(invK n w m idn t (getS TI j), strictB (Nat.succ j) ih)) L j = true →
    TI.length = T.length ∧ ∀ i, j ≤ i → i < T.length →
      invK n w m idn (T.getD i 0) (TI.getD i 0) = true := by
  intro L
  induction L with
  | nil =>
    intro j hL hj h
    have hT : T.length ≤ j := List.drop_eq_nil_iff.mp hL.symm
    have h' : Nat.beq j (lenS TI) = true := h
    rw [lenS_eq] at h'
    have := Nat.eq_of_beq_eq_true h'
    exact ⟨by omega, fun i hi hi' => absurd hi' (by omega)⟩
  | cons t L ih =>
    intro j hL hj h
    obtain ⟨hjT, htj, hL'⟩ := drop_facts hL
    have h' : bAnd(invK n w m idn t (getS TI j), strictB (Nat.succ j)
        (List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (lenS TI))
          (fun t _ ih j => bAnd(invK n w m idn t (getS TI j), strictB (Nat.succ j) ih)) L)) =
        true := h
    rw [bAnd_iff, strictB_eqP (Nat.succ j)] at h'
    obtain ⟨hlen, hall⟩ := ih (j + 1) hL' hjT h'.2
    refine ⟨hlen, fun i hi hiT => ?_⟩
    rcases Nat.lt_or_ge j i with hji | hji
    · exact hall i hji hiT
    have : i = j := by omega
    subst this
    rw [List.getD_eq_getElem _ _ hjT, htj, ← getS_eq]
    exact h'.1

theorem invLK_sound {n w m idn : ℕ} {T TI : List ℕ} (h : invLK n w m idn T TI = true) :
    TI.length = T.length ∧ ∀ i < T.length, invK n w m idn (T.getD i 0) (TI.getD i 0) = true := by
  obtain ⟨h1, h2⟩ := invLW_sound T 0 rfl (Nat.zero_le _) h
  exact ⟨h1, fun i hi => h2 i (Nat.zero_le _) hi⟩

end CFSG.KC.HeChain

end
