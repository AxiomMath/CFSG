module

public import Certificates.Data.Kernel.F2FixRank
public import Mathlib.Data.Fintype.BigOperators

public section

namespace CFSG.KC.F2FixRank

open CFSG.KC.XorBits

theorem xorB_congr_sel {f g : ℕ → ℕ} (x : ℕ) :
    ∀ k, (∀ i < k, x.testBit i = true → f i = g i) → xorB f x k = xorB g x k
  | 0, _ => rfl
  | k + 1, h => by
    rw [xorB_succ, xorB_succ, xorB_congr_sel x k fun i hi => h i (Nat.lt_succ_of_lt hi)]
    by_cases hb : x.testBit k = true
    · rw [ite_eq_left hb, ite_eq_left hb, h k (Nat.lt_succ_self k) hb]
    · rw [ite_eq_right hb, ite_eq_right hb]

theorem eq_zero_of_fix {c B : ℕ → ℕ} {fs : List ℕ} {n : ℕ} (h : fixRankOK c B fs n = true)
    {v : ℕ} (hv : v < 2 ^ n) (hfix : xorB c v n = v) (hfs : ∀ j ∈ fs, v.testBit j = false) :
    v = 0 := by
  unfold fixRankOK at h
  rw [List.all_eq_true] at h
  have hL : xorB (fun i => c i ^^^ 2 ^ i) v n = 0 := by
    rw [xorB_xor_fun, hfix, xorB_two_pow hv, Nat.xor_self]
  have hP : ∀ a b, xorB B (a ^^^ b) n = xorB B a n ^^^ xorB B b n := fun a b => xorB_xor B a b n
  have h0 : xorB B (xorB (fun i => c i ^^^ 2 ^ i) v n) n =
      xorB (fun i => xorB B (c i ^^^ 2 ^ i) n) v n :=
    xorB_hom (P := fun a => xorB B a n) hP _ v n
  rw [hL, xorB_zero] at h0
  rw [xorB_congr_sel (g := fun i => 2 ^ i) v n ?_, xorB_two_pow hv] at h0
  · exact h0.symm
  intro i hi hb
  have hi' := h i (List.mem_range.2 hi)
  simp only [Bool.or_eq_true, beq_iff_eq] at hi'
  rcases hi' with hc | hc
  · rw [hfs i (List.contains_iff_mem.1 hc)] at hb
    exact absurd hb Bool.false_ne_true
  · exact hc

theorem card_fix_le {c B : ℕ → ℕ} {fs : List ℕ} {n : ℕ} (h : fixRankOK c B fs n = true) :
    ((Finset.range (2 ^ n)).filter fun v => xorB c v n = v).card ≤ 2 ^ fs.length := by
  classical
  have key : ∀ u ∈ (Finset.range (2 ^ n)).filter (fun v => xorB c v n = v),
      ∀ v ∈ (Finset.range (2 ^ n)).filter (fun v => xorB c v n = v),
      (fun j : Fin fs.length => u.testBit fs[j]) = (fun j : Fin fs.length => v.testBit fs[j]) →
      u = v := by
    intro u hu v hv he
    simp only [Finset.mem_filter, Finset.mem_range] at hu hv
    have hw := eq_zero_of_fix h (Nat.xor_lt_two_pow hu.1 hv.1)
      (by rw [xorB_xor, hu.2, hv.2]) fun j hj => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
        have := congrFun he ⟨k, hk⟩
        simp only [Fin.getElem_fin] at this
        rw [Nat.testBit_xor, this, Bool.xor_self]
    calc u = u ^^^ (u ^^^ v) := by rw [hw, Nat.xor_zero]
      _ = v := by rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  calc ((Finset.range (2 ^ n)).filter fun v => xorB c v n = v).card
      ≤ (Finset.univ : Finset (Fin fs.length → Bool)).card :=
        Finset.card_le_card_of_injOn (fun v j => v.testBit fs[j]) (fun _ _ => Finset.mem_univ _)
          fun u hu v hv he => key u hu v hv he
    _ = 2 ^ fs.length := by simp

end CFSG.KC.F2FixRank

end
