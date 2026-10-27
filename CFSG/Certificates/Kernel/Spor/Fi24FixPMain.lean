module

public import CFSG.Certificates.Kernel.Spor.Fi24FixPSound
public import Certificates.Data.Fi24ThreeFix
public import Certificates.Data.Fi24PairSize
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.KS.Fi24FixP

open CFSG.KC CFSG.KC.Fi24FixP CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi24.Native Timmesfeld.Fi24Cl
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Solomon.Coordinator.Fi24PairSize Finset

theorem ap_compT' {n : Nat} (P Q : Table) {i : Nat} (hi : i < n) :
    ap (compT n P Q) i = ap P (ap Q i) := by
  unfold compT ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ap_idT' {n : Nat} (hn : n < 2 ^ 32) {i : Nat} (hi : i < n) : ap (idT n) i = i := by
  unfold idT ap
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega)]

variable {L : Array Table} {A σ : Nat → Nat → Nat}

theorem ap_foldr (hL : ∀ l < 26, ∀ x < 306936, ap L[l]! x = σ l x)
    (hlt : ∀ l < 26, ∀ x < 306936, σ l x < 306936) : ∀ (w : List Nat), (∀ l ∈ w, l < 26) →
    ∀ x < 306936, ap (w.foldr (fun l T => compT 306936 L[l]! T) (idT 306936)) x = w.foldr σ x ∧
      w.foldr σ x < 306936
  | [], _, x, hx => by
    rw [List.foldr_nil, List.foldr_nil]
    exact ⟨ap_idT' (n := 306936) (by norm_num) hx, hx⟩
  | l :: w, hw, x, hx => by
    have hl := hw l List.mem_cons_self
    obtain ⟨e, h⟩ := ap_foldr hL hlt w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) x hx
    rw [List.foldr_cons, List.foldr_cons, ap_compT' (n := 306936) _ _ hx, e, hL l hl _ h]
    exact ⟨rfl, hlt l hl _ h⟩

theorem len_filter_range (n : Nat) (p : Nat → Bool) :
    ((List.range n).filter p).length = #((range n).filter fun x => p x = true) := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  simp only [Bool.decide_eq_true]

theorem fixCount24_eq {T : Table} {g : Nat → Nat} (hT : ∀ x < 306936, ap T x = g x) :
    fixCount24 T = #((range 306936).filter fun x => g x = x) := by
  unfold fixCount24
  rw [len_filter_range]
  apply congrArg
  apply Finset.filter_congr
  intro x hx
  rw [mem_range] at hx
  rw [beq_iff_eq, hT x hx]

theorem fixCount24_of (hL : ∀ l < 26, ∀ x < 306936, ap L[l]! x = σ l x)
    (hlt : ∀ l < 26, ∀ x < 306936, σ l x < 306936)
    (hσ : ∀ l < 26, ∀ q < 524288, σ l q < 524288)
    (hA : ∀ l < 26, ∀ v q, q < 524288 → (A l v).testBit q = v.testBit (σ l q))
    {w : List Nat} (hw : ∀ l ∈ w, l < 26) {c : Nat} (h : fixOK A w c = true) :
    fixCount24 (wordTable L w) = c := by
  rw [fixCount24_eq (T := wordTable L w) (g := w.foldr σ) fun x hx => (ap_foldr hL hlt w hw x hx).1]
  exact fixOK_spec (fun l hl => hσ l (hw l hl)) (fun l hl => hA l (hw l hl)) h

theorem fixCnt_of {O : Enum} (hL : ∀ l < 26, ∀ x < 306936, ap (chainLetters O)[l]! x = σ l x)
    (hlt : ∀ l < 26, ∀ x < 306936, σ l x < 306936)
    (hσ : ∀ l < 26, ∀ q < 524288, σ l q < 524288)
    (hA : ∀ l < 26, ∀ v q, q < 524288 → (A l v).testBit q = v.testBit (σ l q))
    {w : List Nat} (hw : ∀ l ∈ w, l < 26) {c : Nat} (h : fixOK A w c = true) :
    fixCnt (wordTab (mkCtx O) w) = c := by
  have e1 : fixCnt (wordTab (mkCtx O) w) = fixCount24 (wordTable (chainLetters O) w) := by
    unfold fixCnt fixCount24
    rw [List.countP_eq_length_filter]
    rfl
  rw [e1]
  exact fixCount24_of hL hlt hσ hA hw h

theorem fi24RepFixOK_of {O : Enum}
    (hL : ∀ l < 26, ∀ x < 306936, ap (chainLetters O)[l]! x = σ l x)
    (hlt : ∀ l < 26, ∀ x < 306936, σ l x < 306936)
    (hσ : ∀ l < 26, ∀ q < 524288, σ l q < 524288)
    (hA : ∀ l < 26, ∀ v q, q < 524288 → (A l v).testBit q = v.testBit (σ l q))
    (h : repFixData.all (fun d => fixOK A d.1 d.2) = true) : fi24RepFixOK O = true := by
  have hw : ∀ d ∈ repFixData, ∀ l ∈ d.1, l < 26 := by decide
  unfold fi24RepFixOK
  rw [List.all_eq_true] at h ⊢
  intro d hd
  rw [fixCount24_of hL hlt hσ hA (hw d hd) (h d hd), beq_self_eq_true]

end CFSG.KS.Fi24FixP

end
