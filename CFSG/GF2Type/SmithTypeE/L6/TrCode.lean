module

public import Certificates.Data.SmithL6Tr
public import CFSG.LargeExtraspecial.SMod20Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup Module CFSG.SmithL6
open CFSG.LargeExtraspecial.SMod20 (V decode decode_xor decode_zero eq_of_decode_eq)

theorem decode_mod (a : ℕ) : decode (a % 2 ^ 20) = decode a := by
  funext m
  rw [CFSG.LargeExtraspecial.SMod20.decode_apply, CFSG.LargeExtraspecial.SMod20.decode_apply,
    Nat.testBit_mod_two_pow]
  simp [m.2]

theorem mod_eq_of_decode_eq {a b : ℕ} (h : decode a = decode b) : a % 2 ^ 20 = b % 2 ^ 20 :=
  eq_of_decode_eq (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (by rw [decode_mod, decode_mod, h])

theorem trXorSel_cons (b : ℕ) (bs : List ℕ) (m : ℕ) :
    trXorSel (b :: bs) m = (if m % 2 = 1 then b else 0) ^^^ trXorSel bs (m / 2) := rfl

theorem decode_trXorSel_mem {U : Submodule (ZMod 2) V} :
    ∀ (bs : List ℕ), (∀ b ∈ bs, decode b ∈ U) → ∀ m, decode (trXorSel bs m) ∈ U
  | [], _, _ => by
    show decode 0 ∈ U
    rw [decode_zero]
    exact U.zero_mem
  | b :: bs, h, m => by
    rw [trXorSel_cons, decode_xor]
    refine U.add_mem ?_ (decode_trXorSel_mem bs (fun x hx => h x (List.mem_cons_of_mem _ hx)) _)
    split
    · exact h b (List.mem_cons_self ..)
    · rw [decode_zero]
      exact U.zero_mem

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

end CFSG.GF2Type.SmithTypeE.L6
