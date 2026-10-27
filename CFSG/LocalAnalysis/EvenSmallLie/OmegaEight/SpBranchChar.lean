module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchCode
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] def chiV (n b v : ℕ) : Bool :=
  (List.range n).foldl (fun r j => r ^^ (v &&& b).testBit j) false

theorem chiV_succ (n b v : ℕ) : chiV (n + 1) b v = (chiV n b v ^^ (v &&& b).testBit n) := by
  unfold chiV
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem chiV_xor (n b v w : ℕ) : chiV n b (v ^^^ w) = (chiV n b v ^^ chiV n b w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [chiV_succ, chiV_succ, chiV_succ, ih, Nat.testBit_land, Nat.testBit_xor, Nat.testBit_land,
      Nat.testBit_land]
    cases chiV n b v <;> cases chiV n b w <;> cases v.testBit n <;> cases w.testBit n <;>
      cases b.testBit n <;> rfl

theorem chiV_zero (n b : ℕ) : chiV n b 0 = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [chiV_succ, ih]; simp

theorem chiV_two_pow (b : ℕ) {n j : ℕ} (hj : j < n) : chiV n b (2 ^ j) = b.testBit j := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [chiV_succ, Nat.testBit_land, Nat.testBit_two_pow]
    by_cases h : j = n
    · subst h
      have h0 : chiV j b (2 ^ j) = false := by
        have key : ∀ m, m ≤ j → chiV m b (2 ^ j) = false := by
          intro m
          induction m with
          | zero => intro _; rfl
          | succ m ihm =>
            intro hm
            rw [chiV_succ, ihm (by omega), Nat.testBit_land, Nat.testBit_two_pow]
            simp [show j ≠ m by omega]
        exact key j le_rfl
      simp [h0]
    · rw [ih (by omega)]
      simp [h]

@[expose] def vecOK (N : ℕ) (par pj : ℕ → ℕ) (vec : ℕ → ℕ) : Bool :=
  vec 0 == 0 && (List.range N).all fun c => c == 0 || vec c == (vec (par c) ^^^ 2 ^ pj c)

namespace CodeIso

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul)

theorem xi_eq_chiV (h0 : mul 0 0 = 0) {gens : List ℕ} (hgens : ∀ g ∈ gens, g < N)
    {par pj dep vec : ℕ → ℕ}
    (htree : treeOK mul gens N par pj dep = true) (hvec : vecOK N par pj vec = true)
    (ξ : H →* Multiplicative (ZMod 2)) {b : ℕ}
    (hb : ∀ j, j < gens.length → ξ (Φ.g (gens.getD j 0)) =
      Multiplicative.ofAdd (if b.testBit j then 1 else 0)) {c : ℕ} (hc : c < N) :
    ξ (Φ.g c) = Multiplicative.ofAdd (if chiV gens.length b (vec c) then 1 else 0) := by
  unfold treeOK at htree
  unfold vecOK at hvec
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hvec
  obtain ⟨hv0, hvc⟩ := hvec
  have key : ∀ d c, dep c < d → c < N →
      ξ (Φ.g c) = Multiplicative.ofAdd (if chiV gens.length b (vec c) then 1 else 0) := by
    intro d
    induction d with
    | zero => intro c hc; omega
    | succ d ih =>
      intro c hcd hcN
      by_cases h0c : c = 0
      · subst h0c
        rw [hv0, chiV_zero, ← Φ.f_one h0, Φ.g_f, _root_.map_one]
        rfl
      have hc' := List.all_eq_true.1 htree c (List.mem_range.2 hcN)
      simp only [Bool.or_eq_true, beq_iff_eq, h0c, false_or, Bool.and_eq_true,
        decide_eq_true_eq] at hc'
      obtain ⟨⟨⟨hpj, hmul⟩, hpar⟩, hdep⟩ := hc'
      have hv := (hvc c hcN).resolve_left h0c
      have hgl : gens.getD (pj c) 0 < N := by
        rw [List.getD_eq_getElem _ _ hpj]; exact hgens _ (List.getElem_mem hpj)
      have e1 : Φ.g c = Φ.g (par c) * Φ.g (gens.getD (pj c) 0) := by
        apply Φ.inj
        rw [Φ.map_mul, Φ.f_g hpar, Φ.f_g hgl, Φ.f_g hcN, hmul]
      rw [e1, _root_.map_mul, ih _ (by omega) hpar, hb _ hpj, hv, chiV_xor, chiV_two_pow b hpj]
      cases chiV gens.length b (vec (par c)) <;> cases b.testBit (pj c) <;> rfl
  exact key _ c (Nat.lt_succ_self _) hc

end CodeIso

end CFSG.EvenSmallLie.OmegaEight.SpBranch
