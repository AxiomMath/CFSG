module

public import Certificates.Data.Kernel.J2StdOrbK
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalJ2Tests

public section

namespace CFSG.KC.J2StdOrb

open CFSG.KC.Enum CFSG.ComponentClassification.RankTwoClassical.J2Std

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem bAnd_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

variable {K : Nat → Nat} {B : Nat}

theorem foldQ_cons (q x : Nat) (L : List Nat) :
    foldQ K B q (x :: L) = foldQ K B (stepQ K B q x) L :=
  strictN_eq _ _

theorem foldQ_append (L₁ L₂ : List Nat) :
    ∀ q, foldQ K B q (L₁ ++ L₂) = foldQ K B (foldQ K B q L₁) L₂ := by
  induction L₁ with
  | nil => intro q; rfl
  | cons x L ih => intro q; rw [List.cons_append, foldQ_cons, foldQ_cons, ih]

theorem stepQ_spec {q x : Nat} (h : stepQ K B q x ≠ 0) :
    q ≠ 0 ∧ x < B ∧ q ≤ K x + 1 ∧ stepQ K B q x = K x + 2 := by
  unfold stepQ at h ⊢
  rw [strictN_eq] at h ⊢
  cases hq : Nat.beq q 0 <;> cases h1 : Nat.blt x B <;> cases h2 : Nat.ble q (Nat.succ (K x)) <;>
    rw [hq, h1, h2] at h <;> first | exact absurd rfl h | skip
  exact ⟨Nat.ne_of_beq_eq_false hq, Nat.blt_eq.mp h1, Nat.le_of_ble_eq_true h2, rfl⟩

theorem foldQ_spec : ∀ (L : List Nat) (q : Nat), foldQ K B q L ≠ 0 →
    q ≠ 0 ∧ (∀ x ∈ L, x < B) ∧ natChain (L.map K) = true ∧ ∀ x ∈ L.head?, q ≤ K x + 1
  | [], q, h => ⟨h, by simp, by simp [natChain], by simp⟩
  | x :: L, q, h => by
    rw [foldQ_cons] at h
    obtain ⟨h0, hlt, hch, hhd⟩ := foldQ_spec L _ h
    obtain ⟨hq, hx, hle, he⟩ := stepQ_spec h0
    refine ⟨hq, fun y hy => ?_, ?_, fun y hy => ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · exact hlt y hy
    · cases L with
      | nil => simp [natChain]
      | cons y L =>
        have hy := hhd y rfl
        rw [he] at hy
        simp only [List.map_cons, natChain, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by simpa using hch⟩
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      rw [← hy]
      exact hle

theorem lastL_cons_cons (x y : Nat) (L : List Nat) : lastL (x :: y :: L) = lastL (y :: L) := rfl

theorem foldQ_last : ∀ (L : List Nat) (q : Nat), L ≠ [] → foldQ K B q L ≠ 0 →
    foldQ K B q L = K (lastL L) + 2
  | [], _, h, _ => absurd rfl h
  | [x], q, _, h => by
    rw [foldQ_cons] at h ⊢
    exact (stepQ_spec h).2.2.2
  | x :: y :: L, q, _, h => by
    rw [foldQ_cons] at h ⊢
    rw [lastL_cons_cons]
    exact foldQ_last (y :: L) _ (List.cons_ne_nil _ _) h

theorem getL_get : ∀ (Ls : List (Array Nat)) (c : Nat) (h : c < Ls.length),
    getL Ls c = Ls[c].toList
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: Ls, c + 1, h => getL_get Ls c (by simpa using h)

theorem consB_ne {L : List Nat} (h : consB L = true) : L ≠ [] := by
  cases L
  · exact absurd h (by decide)
  · exact List.cons_ne_nil _ _

theorem qPrev_succ (Ls : List (Array Nat)) (c : Nat) : qPrev K Ls (c + 1) = qOf K (getL Ls c) := rfl

theorem chunks_sound (Ls : List (Array Nat)) (hc : ∀ c < Ls.length, chunkOK K B Ls c = true) :
    foldQ K B 1 (Ls.flatMap Array.toList) ≠ 0 := by
  have key : ∀ j ≤ Ls.length, foldQ K B 1 ((Ls.take j).flatMap Array.toList) = qPrev K Ls j := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      obtain ⟨hne, hf⟩ := bAnd_true (hc j (by omega))
      have hne' := consB_ne hne
      have hf' : foldQ K B (qPrev K Ls j) (getL Ls j) ≠ 0 := by
        intro e
        rw [e] at hf
        exact absurd hf (by decide)
      rw [List.take_succ, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.flatMap_append, foldQ_append, ih (by omega), List.flatMap_singleton,
        ← getL_get Ls j (by omega), foldQ_last _ _ hne' hf', qPrev_succ, qOf]
  have h := key Ls.length le_rfl
  rw [List.take_length] at h
  rw [h]
  cases Ls.length with
  | zero => exact Nat.one_ne_zero
  | succ c => rw [qPrev_succ, qOf]; exact Nat.succ_ne_zero _

theorem lenL_aux : ∀ (L : List Nat) (s : Nat),
    List.rec (motive := fun _ => Nat → Nat) (fun s => s) (fun _ _ ih s => strictN (Nat.succ s) ih)
      L s = s + L.length
  | [], s => rfl
  | _ :: L, s => by
    change strictN (Nat.succ s) _ = _
    rw [strictN_eq, lenL_aux L, List.length_cons]
    omega

theorem lenLs_eq : ∀ Ls : List (Array Nat), lenLs Ls = (Ls.flatMap Array.toList).length
  | [] => rfl
  | x :: Ls => by
    change Nat.add (lenL x.toList) (lenLs Ls) = _
    rw [lenLs_eq Ls, List.flatMap_cons, List.length_append, lenL, lenL_aux]
    simp

theorem orbOK_of_chunks {W : Array Nat} {Ls : List (Array Nat)} {k : Nat} {ps : List Nat}
    {F : Nat → Array Nat} (hW : W = (Ls.flatMap Array.toList).toArray) (hk : lenLs Ls = k)
    (hK : ∀ w < 604800, keyAt ps (F w) = K w)
    (hc : ∀ c < Ls.length, chunkOK K 604800 Ls c = true) : orbOK W k ps F = true := by
  obtain ⟨-, hlt, hch, -⟩ := foldQ_spec _ _ (chunks_sound Ls hc)
  subst hW
  have hmap : (Ls.flatMap Array.toList).map (fun w => keyAt ps (F w)) =
      (Ls.flatMap Array.toList).map K := List.map_congr_left fun w hw => hK w (hlt w hw)
  simp only [orbOK, Bool.and_eq_true, beq_iff_eq, List.size_toArray, List.toList_toArray, hmap]
  refine ⟨⟨by rw [← hk, lenLs_eq], ?_⟩, hch⟩
  rw [List.all_toArray', List.all_eq_true]
  · exact fun x hx => decide_eq_true (hlt x hx)
  · simp

end CFSG.KC.J2StdOrb

end
