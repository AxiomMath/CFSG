module

public import Certificates.Data.Kernel.Co2SmithS.Rows
public import CFSG.Certificates.Kernel.Co2InvS.Mat

public section

namespace CFSG.KC.Co2SmithS

open CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co2Smith.Native

theorem wK_cons (f : Nat → Nat) (k : Nat) (w : List Nat) : wK f (k :: w) = mulV (f k) (wK f w) :=
  rfl

theorem wK_lt (f : Nat → Nat) : ∀ w : List Nat, wK f w < 2 ^ 484
  | [] => IDP_lt
  | k :: w => by rw [wK_cons]; exact mulV_lt _ _

theorem wRows_eq {L : Array (Array Nat)} {f : Nat → Nat} {n : Nat}
    (hL : ∀ k < n, L[k]! = unpackR 22 (f k)) :
    ∀ w : List Nat, (∀ k ∈ w, k < n) → wRows L w = unpackR 22 (wK f w)
  | [], _ => idRows_eq
  | k :: w, hw => by
    have e : wRows L (k :: w) = mulRows 22 L[k]! (wRows L w) := rfl
    rw [e, hL k (hw k (List.mem_cons_self ..)),
      wRows_eq hL w fun j hj => hw j (List.mem_cons_of_mem _ hj), mulRows_unpack, wK_cons]

theorem wRows_beq {L : Array (Array Nat)} {f : Nat → Nat} {n : Nat}
    (hL : ∀ k < n, L[k]! = unpackR 22 (f k)) {w w' : List Nat} (hw : ∀ k ∈ w, k < n)
    (hw' : ∀ k ∈ w', k < n) : (wRows L w == wRows L w') = Nat.beq (wK f w) (wK f w') := by
  rw [wRows_eq hL w hw, wRows_eq hL w' hw', unpack_beq (wK_lt f w) (wK_lt f w')]

theorem wRows_beq_id {L : Array (Array Nat)} {f : Nat → Nat} {n : Nat}
    (hL : ∀ k < n, L[k]! = unpackR 22 (f k)) {w : List Nat} (hw : ∀ k ∈ w, k < n) :
    (wRows L w == idRows 22) = Nat.beq (wK f w) IDP := by
  rw [wRows_eq hL w hw, idRows_eq, unpack_beq (wK_lt f w) IDP_lt]

theorem validM_unpack (M : Nat) : validM (unpackR 22 M) = true := by
  unfold validM
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [unpackR], fun i hi => ?_⟩
  simp only [unpackR, Array.getElem_ofFn]
  exact Nat.mod_lt _ (by decide)

theorem all_congr' {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.all p = l.all q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem sCode_lt (l : Fin 8 × Bool) : sCode l < 16 := by
  unfold sCode
  split <;> omega

theorem map_sCode_lt (r : List (Fin 8 × Bool)) : ∀ k ∈ r.map sCode, k < 16 := by
  intro k hk
  obtain ⟨l, -, rfl⟩ := List.mem_map.1 hk
  exact sCode_lt l

theorem sp6Check_eq {seeds : Array (Array Nat)} {F : Nat → Nat} {a b : Nat}
    (hF : ∀ k < 16, (sp6LetterRows seeds)[k]! = unpackR 22 (F k))
    (ha : mRows seeds [2] = unpackR 22 a) (hb : mRows seeds [3] = unpackR 22 b)
    (hab : a < 2 ^ 484 ∧ b < 2 ^ 484) :
    sp6Check seeds = sp6CheckK F a b := by
  unfold sp6Check sp6CheckK
  dsimp only
  have h1 : ∀ i ∈ List.range 8, (wRows (sp6LetterRows seeds) [2 * i, 2 * i + 1] == idRows 22) =
      Nat.beq (wK F [2 * i, 2 * i + 1]) IDP := by
    intro i hi
    have hi' := List.mem_range.1 hi
    refine wRows_beq_id hF fun k hk => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have h2 : ∀ r ∈ sp6Rels (), (wRows (sp6LetterRows seeds) (r.map sCode) == idRows 22) =
      Nat.beq (wK F (r.map sCode)) IDP := fun r _ => wRows_beq_id hF (map_sCode_lt r)
  have h3 : ∀ i ∈ List.finRange 8, (wRows (sp6LetterRows seeds)
      ((commWordsN (sp6Pairs i)).map sCode) == wRows (sp6LetterRows seeds) [2 * i.val]) =
      Nat.beq (wK F ((commWordsN (sp6Pairs i)).map sCode)) (wK F [2 * i.val]) := by
    intro i _
    refine wRows_beq hF (map_sCode_lt _) fun k hk => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  have h4 : ∀ (w : List (Fin 8 × Bool)) (c : Nat), mRows seeds [c] = unpackR 22 (if c = 2 then a else b) →
      c = 2 ∨ c = 3 → (wRows (sp6LetterRows seeds) (w.map sCode) == mRows seeds [c]) =
        Nat.beq (wK F (w.map sCode)) (if c = 2 then a else b) := by
    intro w c hc hc'
    rw [hc, wRows_eq hF _ (map_sCode_lt w)]
    refine unpack_beq (wK_lt F _) ?_
    split
    · exact hab.1
    · exact hab.2
  rw [all_congr' h1, all_congr' h2, all_congr' h3,
    h4 _ 2 (by simpa using ha) (Or.inl rfl), h4 _ 3 (by simpa using hb) (Or.inr rfl)]
  simp

end CFSG.KC.Co2SmithS

end
