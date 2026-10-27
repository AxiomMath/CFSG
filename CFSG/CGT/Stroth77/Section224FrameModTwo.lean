module

public import CFSG.CGT.Stroth77.Section225FrameModTwo
public import CFSG.CGT.Stroth77.Section224UniformSq

public section

namespace CFSG.CGT.Stroth77

open Matrix

namespace Stroth224Frame

open Stroth225Frame

@[expose] def barRhoOne : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

theorem type100_bar :
    (∀ i j, ((Type100.uvM i j : ℤ) : ZMod 2) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) ∧
    (∀ i j, ((Type100.tM i j : ℤ) : ZMod 2) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) ∧
    (∀ i j, ((Type100.uM i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, ((Type100.ρM i j : ℤ) : ZMod 2) = barRhoOne i j) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide

theorem familyOne_bar {τ : StrothTypeIndex} (hfam : τ.m + 1 = τ.n) :
    (∀ i j, ((τ.action.uv i j : ℤ) : ZMod 2) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) ∧
    (∀ i j, ((τ.action.t i j : ℤ) : ZMod 2) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) ∧
    (∀ i j, ((τ.action.u i j : ℤ) : ZMod 2) = barU i j) ∧
    (∀ i j, ((τ.action.ρ i j : ℤ) : ZMod 2) = barRhoOne i j) := by
  have hmod : (∀ i j, τ.action.uv i j ≡ Type100.uvM i j [ZMOD 2]) ∧
      (∀ i j, τ.action.t i j ≡ Type100.tM i j [ZMOD 2]) ∧
      (∀ i j, τ.action.u i j ≡ Type100.uM i j [ZMOD 2]) ∧
      (∀ i j, τ.action.ρ i j ≡ Type100.ρM i j [ZMOD 2]) := by
    rcases familyOne_disjunction τ hfam with ⟨m, rfl⟩ | ⟨s, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩ |
        ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
    · exact modTwo_t100 m
    · exact modTwo_t101 s
    · exact modTwo_t110 t
    · exact modTwo_t111 t
    · exact modTwo_t120 m hm
    · exact modTwo_t121 m hm
    · exact modTwo_t130 m hm
    · exact modTwo_t131 m hm
  obtain ⟨h1, h2, h3, h4⟩ := hmod
  obtain ⟨b1, b2, b3, b4⟩ := type100_bar
  exact ⟨fun i j => ((ZMod.intCast_eq_intCast_iff _ _ 2).mpr (h1 i j)).trans (b1 i j),
    fun i j => ((ZMod.intCast_eq_intCast_iff _ _ 2).mpr (h2 i j)).trans (b2 i j),
    fun i j => ((ZMod.intCast_eq_intCast_iff _ _ 2).mpr (h3 i j)).trans (b3 i j),
    fun i j => ((ZMod.intCast_eq_intCast_iff _ _ 2).mpr (h4 i j)).trans (b4 i j)⟩

theorem familyOne_four {τ : StrothTypeIndex} (hfam : τ.m + 1 = τ.n) :
    (4 : ℤ) ∣ τ.action.uv 1 0 - 2 ∧ (4 : ℤ) ∣ τ.action.uv 2 0 - 2 ∧
    (4 : ℤ) ∣ τ.action.t 1 0 - 2 ∧ (4 : ℤ) ∣ τ.action.t 2 0 ∧
    (4 : ℤ) ∣ τ.action.u 1 0 ∧ (4 : ℤ) ∣ τ.action.u 2 0 ∧
    (4 : ℤ) ∣ τ.action.ρ 1 0 ∧ (4 : ℤ) ∣ τ.action.ρ 2 0 := by
  rcases familyOne_disjunction τ hfam with ⟨m, rfl⟩ | ⟨s, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩ |
      ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩
  · refine ⟨⟨-1, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> rfl
  · refine ⟨⟨-1, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;> rfl
  · refine ⟨⟨-1 + 2 ^ t, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨2 ^ t, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type110.action, SigmaFourAction.ofMatEq, Type110.uvM,
        Type110.tM, Type110.uM, Type110.ρM, uMat, ofCols_apply] <;> ring
  · refine ⟨⟨-1 + 2 ^ t, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨2 ^ t, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type111.action, SigmaFourAction.ofMatEq, Type111.uvM,
        Type111.tM, Type111.uM, Type111.ρM, uMat, ofCols_apply] <;> ring
  · refine ⟨⟨0, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type120.actionPaper, Type120.action,
        SigmaFourAction.ofMatEq, Type120.uvM, Type120.tM, Type120.uM, Type120.ρM, uMat,
        ofCols_apply]
  · refine ⟨⟨0, ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type121.actionPaper, Type121.action,
        SigmaFourAction.ofMatEq, Type121.uvM, Type121.tM, Type121.uM, Type121.ρM, uMat,
        ofCols_apply]
  · refine ⟨⟨2 ^ (m - 2), ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1 + 2 ^ (m - 2), ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type130.actionPaper, Type130.action,
        SigmaFourAction.ofMatEq, Type130.uvM, Type130.tM, Type130.uM, Type130.ρM, uMat,
        ofCols_apply]
    all_goals
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
      rw [Nat.add_sub_cancel, pow_add]
      ring
  · refine ⟨⟨2 ^ (m - 2), ?_⟩, ⟨-1, ?_⟩, ⟨0, ?_⟩, ⟨1 + 2 ^ (m - 2), ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩,
      ⟨0, ?_⟩, ⟨0, ?_⟩⟩ <;>
      simp [StrothTypeIndex.action, Type131.actionPaper, Type131.action,
        SigmaFourAction.ofMatEq, Type131.uvM, Type131.tM, Type131.uM, Type131.ρM, uMat,
        ofCols_apply]
    all_goals
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
      rw [Nat.add_sub_cancel, pow_add]
      ring

theorem familyOne_k {τ : StrothTypeIndex} (hfam : τ.m + 1 = τ.n) :
    τ.k = ![τ.m, τ.m + 1, τ.m + 1] := by
  rw [τ.k_eq, hfam]

theorem matAct_torusHalf_familyOne {k : Fin 3 → ℕ} {m : ℕ} (hk : k = ![m, m + 1, m + 1])
    (hm : 1 ≤ m) (M : IntMat) (hM : Compat k M) (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h00 : ((M 0 0 : ℤ) : ZMod 2) = A 0 0) (h01 : A 0 1 = 0) (h02 : A 0 2 = 0)
    (h10 : (4 : ℤ) ∣ M 1 0 - 2 * ((A 1 0).val : ℤ)) (h11 : ((M 1 1 : ℤ) : ZMod 2) = A 1 1)
    (h12 : ((M 1 2 : ℤ) : ZMod 2) = A 1 2) (h20 : (4 : ℤ) ∣ M 2 0 - 2 * ((A 2 0).val : ℤ))
    (h21 : ((M 2 1 : ℤ) : ZMod 2) = A 2 1) (h22 : ((M 2 2 : ℤ) : ZMod 2) = A 2 2)
    (ε : Fin 3 → ZMod 2) :
    matAct k M hM (torusHalf k ε) = torusHalf k (A *ᵥ ε) := by
  subst hk
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have same : ∀ (n : ℕ) (z : ℤ) (a : ZMod 2), 1 ≤ n → (z : ZMod 2) = a →
      (2 : ℤ) ^ n ∣ 2 ^ (n - 1) * z - 2 ^ (n - 1) * (a.val : ℤ) := by
    intro n z a hn h
    obtain ⟨t, ht⟩ := two_dvd_sub_val_of_intCast_eq h
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    refine ⟨t, ?_⟩
    rw [Nat.add_sub_cancel, ← mul_sub, ht, pow_succ]
    ring
  have key : ∀ i j, (2 : ℤ) ^ (![m + 1, m + 1 + 1, m + 1 + 1] i) ∣
      2 ^ (![m + 1, m + 1 + 1, m + 1 + 1] j - 1) * M i j -
        2 ^ (![m + 1, m + 1 + 1, m + 1 + 1] i - 1) * ((A i j).val : ℤ) := by
    intro i j
    fin_cases i <;> fin_cases j
    · show (2 : ℤ) ^ (m + 1) ∣ 2 ^ (m + 1 - 1) * M 0 0 - 2 ^ (m + 1 - 1) * ((A 0 0).val : ℤ)
      exact same _ _ _ (by omega) h00
    · show (2 : ℤ) ^ (m + 1) ∣ 2 ^ (m + 1 + 1 - 1) * M 0 1 - 2 ^ (m + 1 - 1) * ((A 0 1).val : ℤ)
      rw [h01, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero, Nat.add_sub_cancel]
      exact ⟨M 0 1, by ring⟩
    · show (2 : ℤ) ^ (m + 1) ∣ 2 ^ (m + 1 + 1 - 1) * M 0 2 - 2 ^ (m + 1 - 1) * ((A 0 2).val : ℤ)
      rw [h02, ZMod.val_zero, Nat.cast_zero, mul_zero, sub_zero, Nat.add_sub_cancel]
      exact ⟨M 0 2, by ring⟩
    · show (2 : ℤ) ^ (m + 1 + 1) ∣ 2 ^ (m + 1 - 1) * M 1 0 -
        2 ^ (m + 1 + 1 - 1) * ((A 1 0).val : ℤ)
      obtain ⟨t, ht⟩ := h10
      exact ⟨t, by rw [Nat.add_sub_cancel, Nat.add_sub_cancel]; linear_combination (2 : ℤ) ^ m * ht⟩
    · show (2 : ℤ) ^ (m + 1 + 1) ∣ 2 ^ (m + 1 + 1 - 1) * M 1 1 -
        2 ^ (m + 1 + 1 - 1) * ((A 1 1).val : ℤ)
      exact same _ _ _ (by omega) h11
    · show (2 : ℤ) ^ (m + 1 + 1) ∣ 2 ^ (m + 1 + 1 - 1) * M 1 2 -
        2 ^ (m + 1 + 1 - 1) * ((A 1 2).val : ℤ)
      exact same _ _ _ (by omega) h12
    · show (2 : ℤ) ^ (m + 1 + 1) ∣ 2 ^ (m + 1 - 1) * M 2 0 -
        2 ^ (m + 1 + 1 - 1) * ((A 2 0).val : ℤ)
      obtain ⟨t, ht⟩ := h20
      exact ⟨t, by rw [Nat.add_sub_cancel, Nat.add_sub_cancel]; linear_combination (2 : ℤ) ^ m * ht⟩
    · show (2 : ℤ) ^ (m + 1 + 1) ∣ 2 ^ (m + 1 + 1 - 1) * M 2 1 -
        2 ^ (m + 1 + 1 - 1) * ((A 2 1).val : ℤ)
      exact same _ _ _ (by omega) h21
    · show (2 : ℤ) ^ (m + 1 + 1) ∣ 2 ^ (m + 1 + 1 - 1) * M 2 2 -
        2 ^ (m + 1 + 1 - 1) * ((A 2 2).val : ℤ)
      exact same _ _ _ (by omega) h22
  funext i
  rw [matAct_apply, torusHalf_apply, Matrix.mulVec, dotProduct, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [torusHalf_apply]
    exact entryHom_halfHom hM i j _ _ (key i j)

theorem familyOne_torusBar {τ : StrothTypeIndex} (hfam : τ.m + 1 = τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (v : Torus τ.k) :
    torusBar τ.k hk (τ.action.φuv v) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        torusBar τ.k hk v ∧
    torusBar τ.k hk (τ.action.φt v) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
        torusBar τ.k hk v ∧
    torusBar τ.k hk (τ.action.φu v) = barU *ᵥ torusBar τ.k hk v ∧
    torusBar τ.k hk (τ.action.φρ v) = barRhoOne *ᵥ torusBar τ.k hk v := by
  obtain ⟨huv, ht, hu, hρ⟩ := familyOne_bar hfam
  exact ⟨torusBar_matAct _ hk _ _ _ huv v, torusBar_matAct _ hk _ _ _ ht v,
    torusBar_matAct _ hk _ _ _ hu v, torusBar_matAct _ hk _ _ _ hρ v⟩

theorem familyOne_torusHalf {τ : StrothTypeIndex} (hfam : τ.m + 1 = τ.n) (hm : 1 ≤ τ.m)
    (ε : Fin 3 → ZMod 2) :
    τ.action.φuv (torusHalf τ.k ε) = torusHalf τ.k (topUv *ᵥ ε) ∧
    τ.action.φt (torusHalf τ.k ε) = torusHalf τ.k (topT *ᵥ ε) ∧
    τ.action.φu (torusHalf τ.k ε) = torusHalf τ.k (topU *ᵥ ε) ∧
    τ.action.φρ (torusHalf τ.k ε) = torusHalf τ.k (topRho *ᵥ ε) := by
  obtain ⟨huv, ht, hu, hρ⟩ := familyOne_bar hfam
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := familyOne_four hfam
  have hk := familyOne_k hfam
  have v1 : (1 : ZMod 2).val = 1 := rfl
  have v0 : (0 : ZMod 2).val = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine matAct_torusHalf_familyOne hk hm _ _ topUv ((huv 0 0).trans (by decide)) (by decide)
      (by decide) ?_ ((huv 1 1).trans (by decide)) ((huv 1 2).trans (by decide)) ?_
      ((huv 2 1).trans (by decide)) ((huv 2 2).trans (by decide)) ε
    · rw [show topUv 1 0 = 1 by decide, v1]; simpa using e1
    · rw [show topUv 2 0 = 1 by decide, v1]; simpa using e2
  · refine matAct_torusHalf_familyOne hk hm _ _ topT ((ht 0 0).trans (by decide)) (by decide)
      (by decide) ?_ ((ht 1 1).trans (by decide)) ((ht 1 2).trans (by decide)) ?_
      ((ht 2 1).trans (by decide)) ((ht 2 2).trans (by decide)) ε
    · rw [show topT 1 0 = 1 by decide, v1]; simpa using e3
    · rw [show topT 2 0 = 0 by decide, v0]; simpa using e4
  · refine matAct_torusHalf_familyOne hk hm _ _ topU ((hu 0 0).trans (by decide)) (by decide)
      (by decide) ?_ ((hu 1 1).trans (by decide)) ((hu 1 2).trans (by decide)) ?_
      ((hu 2 1).trans (by decide)) ((hu 2 2).trans (by decide)) ε
    · rw [show topU 1 0 = 0 by decide, v0]; simpa using e5
    · rw [show topU 2 0 = 0 by decide, v0]; simpa using e6
  · refine matAct_torusHalf_familyOne hk hm _ _ topRho ((hρ 0 0).trans (by decide))
      (by decide) (by decide) ?_ ((hρ 1 1).trans (by decide)) ((hρ 1 2).trans (by decide)) ?_
      ((hρ 2 1).trans (by decide)) ((hρ 2 2).trans (by decide)) ε
    · rw [show topRho 1 0 = 0 by decide, v0]; simpa using e7
    · rw [show topRho 2 0 = 0 by decide, v0]; simpa using e8

end Stroth224Frame

end CFSG.CGT.Stroth77
