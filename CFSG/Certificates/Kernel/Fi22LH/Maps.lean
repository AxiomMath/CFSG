module

public import CFSG.Certificates.Kernel.Fi22LH.Bits
public import CFSG.Certificates.Kernel.Spor.TabWords

public section

namespace CFSG.KS.Fi22LH

open CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native CFSG.KS.TW

theorem allIn_lo {lo hi : Nat} {p : Nat → Bool} :
    allIn lo hi p = true ↔ ∀ i, lo ≤ i → i < hi → p i = true := by
  unfold allIn
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i h1 h2
    have := h ⟨i - lo, by omega⟩ (List.mem_finRange _)
    simp only at this
    rwa [Nat.add_sub_cancel' h1] at this
  · intro h ⟨i, hi⟩ _
    exact h (lo + i) (by omega) (by omega)

theorem mapsOnto_of {T : Table} {A B : Bits} {SA SB : Nat → Prop} (hA : BitsIs A SA)
    (hB : BitsIs B SB) (hT : ∀ x < 3510, ap T x < 3510) (h : ∀ x < 3510, SB (ap T x) ↔ SA x) :
    mapsOnto T A B = true := by
  unfold mapsOnto
  rw [allIn_iff]
  intro x hx
  rw [beq_iff_eq]
  apply Bool.eq_iff_iff.2
  rw [hB.2 _ (by have := hT x hx; omega), hA.2 x (by omega)]
  exact h x hx

theorem mapsOnto_spec {T : Table} {A B : Bits} (h : mapsOnto T A B = true) {x : Nat}
    (hx : x < 3510) : bitAt B (ap T x) = bitAt A x := by
  unfold mapsOnto at h
  rw [allIn_iff] at h
  exact beq_iff_eq.1 (h x hx)

theorem canonKey_inj {a b : Nat} (ha : a < 2 ^ 3510) (hb : b < 2 ^ 3510)
    (h : canonKey (bitsOfNat a) = canonKey (bitsOfNat b)) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 3510
  · have e : i ∈ canonKey (bitsOfNat a) ↔ i ∈ canonKey (bitsOfNat b) := by rw [h]
    unfold canonKey at e
    simp only [List.mem_filter, List.mem_range, hi, true_and] at e
    rw [(bitsIs_bitsOfNat a).2 i (by omega), (bitsIs_bitsOfNat b).2 i (by omega)] at e
    exact Bool.eq_iff_iff.2 e
  · have hp : 2 ^ 3510 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem foldl_insert_of' {α : Type} [BEq α] [LawfulBEq α] [Hashable α] (K : Nat → α) {n : Nat}
    (hinj : ∀ i < n, ∀ j < n, K i = K j → i = j) {k : Nat} (hk : k < n) :
    ((List.range n).foldl (fun t k => t.insert (K k) k) (∅ : Std.HashMap α Nat))[K k]? =
      some k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    rcases Nat.lt_or_ge k n with h | h
    · have hne : (K n == K k) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        have := hinj n (by omega) k (by omega) e
        omega
      rw [hne]
      exact ih (fun i hi j hj e => hinj i (by omega) j (by omega) e) h
    · have : k = n := by omega
      subst this
      rw [beq_self_eq_true]
      rfl

theorem foldl_insert_none' {α : Type} [BEq α] [LawfulBEq α] [Hashable α] (K : Nat → α) {n : Nat}
    {B : α} (hB : ∀ k < n, K k ≠ B) :
    ((List.range n).foldl (fun t k => t.insert (K k) k) (∅ : Std.HashMap α Nat))[B]? = none := by
  induction n with
  | zero => exact Std.HashMap.getElem?_empty
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.HashMap.getElem?_insert]
    have hne : (K n == B) = false := by
      rw [beq_eq_false_iff_ne]
      exact hB n (by omega)
    rw [hne]
    exact ih fun k hk => hB k (by omega)

end CFSG.KS.Fi22LH
