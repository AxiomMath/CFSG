module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Pair
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48Data

public section

namespace CFSG.AGLEmbedding.ChevOuterD48

@[expose] def eP (i : ℕ) : Pr := wordP (d48E.getD i [])

@[expose] def nWord (j : ℕ) : List ℕ := (d48N.getD j (0, [])).2

@[expose] def nHyp (j : ℕ) : ℕ := (d48N.getD j (0, [])).1

@[expose] def numN : ℕ := d48N.length

@[expose] def nP (j : ℕ) : Pr := wordP (nWord j)

@[expose] def nInvP (j : ℕ) : Pr := wordP (invWord (nWord j))

@[expose] def nList : List Pr := (List.range numN).map nP

@[expose] def nInvList : List Pr := (List.range numN).map nInvP

@[expose] def hypX (h : ℕ) : Pr :=
  match h with
  | 0 => eP 0
  | 1 => eP 0
  | 2 => eP 1
  | 3 => mulP (eP 0) (eP 1)
  | _ => mulP (eP 0) (powP (eP 1) 2)

@[expose] def hypY (h : ℕ) : Pr :=
  match h with
  | 0 => eP 1
  | _ => eP 2

@[expose] def slpElt (i : ℕ) : Pr :=
  if i < 2 * numN then
    (if i % 2 = 0 then nList.getD (i / 2) oneP else nInvList.getD (i / 2) oneP)
  else (letterArr (i - 2 * numN), 0)

@[expose] def slpP (ids : List ℕ) : Pr := ids.foldl (fun acc i => mulP acc (slpElt i)) oneP

@[expose] def D48CheckE : Prop :=
  (∀ i ∈ List.range 3, powP (eP i) 3 = oneP) ∧
  mulP (eP 0) (eP 1) = mulP (eP 1) (eP 0) ∧
  mulP (eP 0) (eP 2) = mulP (eP 2) (eP 0) ∧
  mulP (eP 1) (eP 2) = mulP (eP 2) (eP 1) ∧
  (∀ a ∈ List.range 3, ∀ b ∈ List.range 3, ∀ c ∈ List.range 3, (a = 0 ∧ b = 0 ∧ c = 0) ∨
    mulP (mulP (powP (eP 0) a) (powP (eP 1) b)) (powP (eP 2) c) ≠ oneP)

@[expose] def D48CheckHyp : Prop :=
  ∀ h ∈ List.range 5, powP (hypX h) 3 = oneP ∧ powP (hypY h) 3 = oneP ∧
    mulP (hypX h) (hypY h) = mulP (hypY h) (hypX h) ∧
    ∀ a ∈ List.range 3, ∀ b ∈ List.range 3, (a = 0 ∧ b = 0) ∨
      mulP (powP (hypX h) a) (powP (hypY h) b) ≠ oneP

@[expose] def D48CheckN : Prop :=
  ∀ j ∈ List.range numN, nHyp j < 5 ∧ mulP (nP j) (nInvP j) = oneP ∧
    ∀ g ∈ [hypX (nHyp j), hypY (nHyp j)], ∃ s ∈ List.range 3, ∃ t ∈ List.range 3,
      mulP (mulP (nP j) g) (nInvP j) = mulP (powP (hypX (nHyp j)) s) (powP (hypY (nHyp j)) t)

@[expose] def D48CheckSlp : Prop :=
  (∀ x ∈ d48Slp1, x.1 < 24 ∧ (∀ i ∈ x.2, i < 2 * numN) ∧ slpP x.2 = (letterArr x.1, 0)) ∧
  (∀ x ∈ d48Slp2, x.1 < 24 ∧
    (∀ i ∈ x.2, i < 2 * numN ∨ (2 * numN ≤ i ∧ (i - 2 * numN) ∈ d48Slp1.map (·.1))) ∧
    slpP x.2 = (letterArr x.1, 0)) ∧
  (∀ k ∈ List.range 24, k ∈ (d48Slp1 ++ d48Slp2).map (·.1))

instance instDecidableE : Decidable D48CheckE := by
  unfold D48CheckE
  infer_instance

instance instDecidableHyp : Decidable D48CheckHyp := by
  unfold D48CheckHyp
  infer_instance

instance instDecidableN : Decidable D48CheckN := by
  unfold D48CheckN
  infer_instance

instance instDecidableSlp : Decidable D48CheckSlp := by
  unfold D48CheckSlp
  infer_instance

@[expose] def D48Check : Prop := D48CheckE ∧ D48CheckHyp ∧ D48CheckN ∧ D48CheckSlp

instance instDecidableCheck : Decidable D48Check := by
  unfold D48Check
  infer_instance

end CFSG.AGLEmbedding.ChevOuterD48
