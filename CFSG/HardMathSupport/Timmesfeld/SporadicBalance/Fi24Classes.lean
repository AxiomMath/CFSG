module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import Certificates.Certificate13693
public import Certificates.Data.CFSGNative.Timmesfeld.Fi24Cl
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Sporadic.Fi24 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three _root_.Timmesfeld.Fi24Cl

open CFSG.Sporadic.Fi24.Native (chainBase)

local notation "LET" => CFSG.Sporadic.Fi24.letters

open scoped Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Fi24Sylow

section Tables

theorem wordTable_nil (letters : Array Table) : wordTable letters [] = idT 306936 := by
  unfold wordTable
  exact List.foldr_nil

theorem wordTable_cons (letters : Array Table) (l : ℕ) (w : List ℕ) :
    wordTable letters (l :: w) = compT 306936 letters[l]! (wordTable letters w) := by
  unfold wordTable
  exact List.foldr_cons

theorem rep_wordTable : ∀ w : List ℕ, (∀ z ∈ w, z < (LET).size) →
    Rep 306936 (wordTable LET w) (wordElt w)
  | [], _ => by
    rw [wordTable_nil]
    unfold wordElt
    rw [List.map_nil, List.prod_nil]
    exact Rep.idT (by norm_num)
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := rep_wordTable w fun z hz => hw z (List.mem_cons_of_mem _ hz)
    rw [wordTable_cons]
    unfold wordElt
    rw [List.map_cons, List.prod_cons]
    exact (rep_pairG_all l hl).compT ih

theorem idx_wordElt : ∀ w : List ℕ, (∀ z ∈ w, z < (LET).size) → ∀ x < 306936,
    idx 306936 (wordElt w) x = apWord LET w x
  | [], _, x, hx => by
    unfold wordElt apWord
    rw [List.map_nil, List.prod_nil, idx_one]
    rfl
  | l :: w, hw, x, hx => by
    have hl := hw l List.mem_cons_self
    have ih := idx_wordElt w (fun z hz => hw z (List.mem_cons_of_mem _ hz)) x hx
    have e1 : wordElt (l :: w) = pairG gs l * wordElt w := by
      unfold wordElt
      rw [List.map_cons, List.prod_cons]
    have e2 : apWord LET (l :: w) x = ap LET[l]! (apWord LET w x) := by
      unfold apWord
      exact List.foldr_cons
    rw [e1, e2, idx_mul, ← ih]
    exact (rep_pairG_all l hl _ (idx_lt _ hx)).symm

theorem pairG_flip (l : ℕ) :
    pairG gs (if l % 2 = 0 then l + 1 else l - 1) = (pairG gs l)⁻¹ := by
  by_cases h : l % 2 = 0
  · have h1 : ¬ (l + 1) % 2 = 0 := by omega
    simp [pairG, h, h1, show (l + 1) / 2 = l / 2 by omega]
  · have h1 : (l - 1) % 2 = 0 := by omega
    simp [pairG, h, h1, show (l - 1) / 2 = l / 2 by omega]

theorem wordElt_invWord (w : List ℕ) : wordElt (invWord w) = (wordElt w)⁻¹ := by
  unfold wordElt invWord
  rw [List.map_reverse, List.map_map, List.prod_inv_reverse, List.map_map]
  congr 2
  exact List.map_congr_left fun l _ => pairG_flip l

theorem eq_of_base {x y : J}
    (h : ∀ t < 6, idx 306936 x chainBase[t]! = idx 306936 y chainBase[t]!) : x = y := by
  have h1 : y⁻¹ * x = 1 := sep _ fun t ht => by
    rw [idx_mul, h t (by rw [chainBase_size] at ht; exact ht), ← idx_mul, inv_mul_cancel,
      idx_one]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

end Tables

section Enumeration

variable {G : Array Table} {P : Array (ℕ × ℕ)} {img : Array ℕ}
  {N : ℕ}

theorem letters_size_eq : (LET).size = 26 := by
  rw [letters_size, actionFacts.words_size]

end Enumeration

section Main

theorem fi24ThreeClasses_holds : Fi24ThreeClasses :=
  Certificates.certificate13693

end Main

end Fi24Sylow

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
