module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterRep
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Data

public section

namespace CFSG.AGLEmbedding.ChevOuter

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two

@[expose] def invWord (w : List ℕ) : List ℕ :=
  w.reverse.flatMap fun s => if s < 18 then [s] else [18, 18]

@[expose] def d42eP (i : ℕ) : Pr := wordP (d42E.getD i [])

@[expose] def d42nP (j : ℕ) : Pr := wordP (d42N.getD j [])

@[expose] def d42nInvP (j : ℕ) : Pr := wordP (invWord (d42N.getD j []))

@[expose] def d42nList : List Pr := (List.range (d42N1 + d42N2)).map d42nP

@[expose] def d42nInvList : List Pr := (List.range (d42N1 + d42N2)).map d42nInvP

@[expose] def d42slpElt (i : ℕ) : Pr :=
  if i % 2 = 0 then d42nList.getD (i / 2) oneP else d42nInvList.getD (i / 2) oneP

@[expose] def d42slpP (ids : List ℕ) : Pr := ids.foldl (fun acc i => mulP acc (d42slpElt i)) oneP

@[expose] def D42Check : Prop :=
  (∀ i ∈ List.range 3, powP (d42eP i) 3 = oneP) ∧
  mulP (d42eP 0) (d42eP 1) = mulP (d42eP 1) (d42eP 0) ∧
  mulP (d42eP 0) (d42eP 2) = mulP (d42eP 2) (d42eP 0) ∧
  mulP (d42eP 1) (d42eP 2) = mulP (d42eP 2) (d42eP 1) ∧
  (∀ a ∈ List.range 3, ∀ b ∈ List.range 3, ∀ c ∈ List.range 3, (a = 0 ∧ b = 0 ∧ c = 0) ∨
    mulP (mulP (powP (d42eP 0) a) (powP (d42eP 1) b)) (powP (d42eP 2) c) ≠ oneP) ∧
  (∀ j ∈ List.range (d42N1 + d42N2), mulP (d42nP j) (d42nInvP j) = oneP) ∧
  (∀ j ∈ List.range d42N1, ∀ g ∈ [0, 1], ∃ s ∈ List.range 3, ∃ t ∈ List.range 3,
    mulP (mulP (d42nP j) (d42eP g)) (d42nInvP j) = mulP (powP (d42eP 0) s) (powP (d42eP 1) t)) ∧
  (∀ j ∈ List.range d42N2, ∀ g ∈ [0, 2], ∃ s ∈ List.range 3, ∃ t ∈ List.range 3,
    mulP (mulP (d42nP (d42N1 + j)) (d42eP g)) (d42nInvP (d42N1 + j)) =
      mulP (powP (d42eP 0) s) (powP (d42eP 2) t)) ∧
  (∀ x ∈ d42Slp, (∀ i ∈ x.2, i < 2 * (d42N1 + d42N2)) ∧ d42slpP x.2 = (letterArr x.1, 0)) ∧
  (∀ k ∈ List.range 18, ∃ x ∈ d42Slp, x.1 = k)

instance : Decidable D42Check := by
  unfold D42Check
  infer_instance

end CFSG.AGLEmbedding.ChevOuter
