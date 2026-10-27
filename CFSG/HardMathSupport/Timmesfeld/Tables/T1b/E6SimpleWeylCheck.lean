module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylCheck

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.AGLEmbedding.R3

@[expose] def e6HypK : List Nat := [1, 0, 2, 0, 1, 2]

@[expose] def kDotL (v : List Nat) : Nat :=
  ((List.range 6).foldl (fun s i => s + e6HypK.getD i 0 * v.getD i 0) 0) % 3

@[expose] def e6HypVecs (_ : Unit := ()) : List (List Nat) :=
  (allVecs 3 6).filter fun v => kDotL v == 0

@[expose] def nfixHypOf (V : List (List Nat)) (A : List Nat) : Nat :=
  (V.filter fun v => matVecA6 A.toArray v == v).length

@[expose] def nInterHypOf (V : List (List Nat)) (A B : List Nat) : Nat :=
  (V.filter fun v => matVecA6 A.toArray v == v && matVecA6 B.toArray v == v).length

@[expose] def nfixHyp (A : List Nat) : Nat := nfixHypOf (e6HypVecs ()) A

@[expose] def nInterHyp (A B : List Nat) : Nat := nInterHypOf (e6HypVecs ()) A B

@[expose] def e6LengthCheck (_ : Unit := ()) : Bool :=
  (e6HypVecs ()).length == 243

@[expose] def e6NfixCheck (_ : Unit := ()) : Bool :=
  let V := e6HypVecs ()
  ((e6SylL ()).filter isO3L).all fun A => decide (nfixHypOf V A ≤ 27)

@[expose] def e6InterCheck (_ : Unit := ()) : Bool :=
  let V := e6HypVecs ()
  let O := (e6SylL ()).filter isO3L
  O.all fun A => O.all fun B =>
    decide (A ≠ B → B ≠ mmulL 3 6 A A → mmulL 3 6 A B = mmulL 3 6 B A →
      nInterHypOf V A B ≤ 9)

@[expose] def e6SimpleCheck (_ : Unit := ()) : Bool :=
  e6LengthCheck () && (e6NfixCheck () && e6InterCheck ())

structure E6SimpleFacts : Prop where
  length : (e6HypVecs ()).length = 243
  nfix_le : ∀ A ∈ (e6SylL ()).filter isO3L, nfixHypOf (e6HypVecs ()) A ≤ 27
  nInter_le : ∀ A ∈ (e6SylL ()).filter isO3L, ∀ B ∈ (e6SylL ()).filter isO3L,
    A ≠ B → B ≠ mmulL 3 6 A A → mmulL 3 6 A B = mmulL 3 6 B A →
      nInterHypOf (e6HypVecs ()) A B ≤ 9

private theorem length_of_check (h : e6LengthCheck () = true) : (e6HypVecs ()).length = 243 := by
  rw [e6LengthCheck] at h
  exact of_decide_eq_true h

private theorem nfix_of_check (h : e6NfixCheck () = true) :
    ∀ A ∈ (e6SylL ()).filter isO3L, nfixHypOf (e6HypVecs ()) A ≤ 27 := by
  rw [e6NfixCheck, List.all_eq_true] at h
  intro A hA
  exact of_decide_eq_true (h A hA)

private theorem inter_of_check (h : e6InterCheck () = true) :
    ∀ A ∈ (e6SylL ()).filter isO3L, ∀ B ∈ (e6SylL ()).filter isO3L,
      A ≠ B → B ≠ mmulL 3 6 A A → mmulL 3 6 A B = mmulL 3 6 B A →
        nInterHypOf (e6HypVecs ()) A B ≤ 9 := by
  rw [e6InterCheck, List.all_eq_true] at h
  intro A hA
  have h' := h A hA
  rw [List.all_eq_true] at h'
  intro B hB hAB hAB2 hc
  exact of_decide_eq_true (h' B hB) hAB hAB2 hc

theorem e6SimpleFacts_of_check (h : e6SimpleCheck () = true) : E6SimpleFacts := by
  rw [e6SimpleCheck] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hlen, h2⟩ := h
  obtain ⟨hnfix, hInter⟩ := h2
  exact ⟨length_of_check hlen, nfix_of_check hnfix, inter_of_check hInter⟩

theorem mem_e6HypVecs {v : List Nat} :
    v ∈ e6HypVecs () ↔ v ∈ allVecs 3 6 ∧ kDotL v = 0 := by
  simp [e6HypVecs, beq_iff_eq]

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
