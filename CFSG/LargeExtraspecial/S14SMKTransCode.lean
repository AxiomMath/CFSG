module

public import CFSG.LargeExtraspecial.S14SMKTransCheck
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LargeExtraspecial.SMod20Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.SmithE CFSG.LargeExtraspecial.SMod20

theorem decode_mod (a : ℕ) : decode (a % 2 ^ 20) = decode a := by
  funext m
  rw [decode_apply, decode_apply, Nat.testBit_mod_two_pow]
  simp [m.2]

theorem mod_eq_of_decode_eq {a b : ℕ} (h : decode a = decode b) : a % 2 ^ 20 = b % 2 ^ 20 :=
  eq_of_decode_eq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (by rw [decode_mod, decode_mod, h])

theorem xorSel_cons (b : ℕ) (bs : List ℕ) (m : ℕ) :
    xorSel (b :: bs) m = (if m % 2 = 1 then b else 0) ^^^ xorSel bs (m / 2) := rfl

theorem decode_xorSel_mem {U : Submodule (ZMod 2) V} :
    ∀ (bs : List ℕ), (∀ b ∈ bs, decode b ∈ U) → ∀ m, decode (xorSel bs m) ∈ U
  | [], _, _ => by
    show decode 0 ∈ U
    rw [decode_zero]
    exact U.zero_mem
  | b :: bs, h, m => by
    rw [xorSel_cons, decode_xor]
    refine U.add_mem ?_ (decode_xorSel_mem bs (fun x hx => h x (List.mem_cons_of_mem _ hx)) _)
    split
    · exact h b (List.mem_cons_self ..)
    · rw [decode_zero]
      exact U.zero_mem

theorem le_finrank_of_indepOK {U : Submodule (ZMod 2) V} {bs : List ℕ}
    (hbs : ∀ b ∈ bs, decode b ∈ U) (h : indepOK bs = true) : bs.length ≤ finrank (ZMod 2) U := by
  classical
  have hd := Sporadic.Th.allIn_eq_true.1 h
  let f : Fin (2 ^ bs.length) → U := fun m => ⟨decode (xorSel bs m.val),
    decode_xorSel_mem bs hbs _⟩
  have hf : Function.Injective f := by
    intro m m' hmm
    have e : decode (xorSel bs m.val) = decode (xorSel bs m'.val) := congrArg Subtype.val hmm
    have h1 := (Sporadic.Th.allIn_eq_true.1 (hd m.val (Nat.zero_le _) m.2)) m'.val
      (Nat.zero_le _) m'.2
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
    rcases h1 with h1 | h1
    · exact Fin.ext h1
    · exact absurd (mod_eq_of_decode_eq e) h1
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Nat.card_eq_fintype_card (α := U), Module.card_eq_pow_finrank (K := ZMod 2),
    ZMod.card] at hc
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hc

theorem finrank_span_decode_le (bs : List ℕ) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) {u | ∃ b ∈ bs, u = decode b}) ≤ bs.length := by
  have e : {u : V | ∃ b ∈ bs, u = decode b} = Set.range fun j : Fin bs.length => decode bs[j] := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hb
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨_, List.getElem_mem _, rfl⟩
  rw [e]
  exact (finrank_range_le_card _).trans (by simp)

end CFSG.LargeExtraspecial.S14.SMK
