module

public import CFSG.Certificates.Kernel.GilmanCensus.RelSound
import all Certificates.Data.Census
public import CFSG.Certificates.Kernel.GilmanCensus.ClosureSound

public section

namespace Certificates.GilmanCensusK

open Certificates.Census

theorem bitsA_length : ∀ (f i m b : Nat), m < 2 ^ b → (bitsA f i m).length ≤ b
  | 0, _, _, _, _ => by simp [bitsA]
  | f + 1, i, m, b, hm => by
    simp only [bitsA]
    split
    · simp
    · rename_i h0
      have hb : b ≠ 0 := by
        rintro rfl
        simp at hm
        simp [hm] at h0
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hm2 : m / 2 < 2 ^ b := by rw [Nat.pow_succ] at hm; omega
      have := bitsA_length f (i + 1) (m / 2) b hm2
      split <;> simp <;> omega

theorem closureOf_eq {dt : Data} {dk : DK} (h : Rel dt dk) (ids : List Nat)
    (hids : ∀ i ∈ ids, i < dk.N) (hn : ids.length ≤ 128) :
    closureOf dt ids.toArray = closureK dk ids := by
  rw [closure_eq dt (fun i => dk.reflP.getD i 0) ids.toArray
    (fun i hi j hj => h.refl i (hids i (by simpa using hi)) j hj)
    (fun i hi => Nat.lt_trans (hids i (by simpa using hi)) h.Nlt) (by simpa using hn)]
  simp only [List.toList_toArray]
  rfl

theorem forIn_yieldG {α β : Type} (g : β → α → β) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, f a b = ForInStep.yield (g b a)) :
    ∀ (l : List α) (init : β), forIn (m := Id) l init f = l.foldl g init
  | [], _ => rfl
  | a :: l, init => by
    rw [List.forIn_cons, hf]
    exact forIn_yieldG g f hf l (g init a)

theorem flatMap_congr' {α β : Type} (f g : α → List β) : ∀ (l : List α),
    (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_congr' f g l (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem all_congr' {α : Type} (p q : α → Bool) : ∀ (l : List α), (∀ x ∈ l, p x = q x) → l.all p = l.all q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      all_congr' p q l (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem ite_pure {β : Type} (P : Prop) [Decidable P] (a b : β) :
    (if P then pure (ForInStep.yield a) else pure (ForInStep.yield b) : Id (ForInStep β)) =
      ForInStep.yield (if P then a else b) := by
  split <;> rfl

theorem arr_all {α : Type} (l : List α) (p : α → Bool) : l.toArray.all p = l.all p := by
  simp

theorem ext_loop (c : Nat → Int → Bool) : ∀ (l : List Nat) (out : Array (Nat × Int)),
    (l.foldl (fun out i => [(1 : Int), -1].foldl
      (fun o sg => if c i sg = true then o.push (i, sg) else o) out) out).toList =
      out.toList ++ l.flatMap fun i => ([(1 : Int), -1].filter (c i)).map fun sg => (i, sg)
  | [], out => by simp
  | i :: l, out => by
    rw [List.foldl_cons, ext_loop c l, List.flatMap_cons, ← List.append_assoc]
    congr 1
    by_cases h1 : c i 1 = true <;> by_cases h2 : c i (-1) = true <;> simp [h1, h2]

theorem extensions_eq {dt : Data} {dk : DK} (h : Rel dt dk) (common X : Nat)
    (hc : common < 2 ^ dk.N) (hX : X < 2 ^ dk.N) :
    (extensions dt common X).toList = extensionsK dk common X := by
  have hN := Nat.le_of_lt h.Nlt
  have hY : X ^^^ (X &&& common) < 2 ^ dk.N := by
    apply Nat.lt_of_le_of_lt _ hX
    apply Nat.le_of_testBit
    intro t ht
    simp only [Nat.testBit_xor, Nat.testBit_and] at ht
    cases hx : X.testBit t <;> simp_all
  unfold extensions extensionsK
  rw [simpOf_eq h common hc, kindOf_eq h X hX]
  dsimp only
  rw [List.size_toArray]
  split
  · rfl
  · rw [bitsOf_eq _ (pow_mono_128 _ _ hY hN), List.forIn_toArray]
    have hss : ∀ j ∈ simpOfK dk common, j < dk.N := fun j hj =>
      bitsK_lt common dk.N j hc (List.mem_filter.mp hj).1
    have hsl : (simpOfK dk common).length ≤ dk.N :=
      Nat.le_trans (List.length_filter_le _ _) (bitsA_length 128 0 common dk.N hc)
    let c : Nat → Int → Bool := fun i sg =>
      ((simpOfK dk common).toArray.all fun j => decide (sg * dt.G[i]![j]! ≤ 0)) &&
        closureOf dt ((simpOfK dk common).toArray.push i) == X
    rw [forIn_yieldG (fun out i => [(1 : Int), -1].foldl
      (fun o sg => if c i sg = true then o.push (i, sg) else o) out)]
    · change (List.foldl _ #[] _).toList = _
      rw [ext_loop c]
      simp only [Array.toList_empty, List.nil_append]
      apply flatMap_congr'
      intro i hi
      have hiN := bitsK_lt _ dk.N i hY hi
      congr 1
      apply List.filter_congr
      intro sg _
      simp only [c, arr_all, List.push_toArray]
      rw [closureOf_eq h _ (fun j hj => by
          rcases List.mem_append.mp hj with hj | hj
          · exact hss j hj
          · simp at hj
            omega)
        (by have := h.Nlt; simp; omega)]
      rw [all_congr' _ (fun j => decide (sg * gI dk i j ≤ 0)) _
        (fun j hj => by rw [h.G i j hiN (hss j hj)])]
    · intro i out
      rw [forIn_yieldG (fun o sg => if c i sg = true then o.push (i, sg) else o)]
      · rfl
      · intro sg o
        rw [ite_pure]
        rfl

end Certificates.GilmanCensusK

end
