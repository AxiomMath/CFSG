module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStab

public section

namespace CFSG.ComponentClassification.AS81.Hexa

@[expose] def basisV : Fin 6 → Fin 64 := ![1, 2, 4, 8, 16, 32]

@[expose] def bitComp (v : Fin 64) (i : Fin 6) : Fin 64 := if v.val.testBit i then basisV i else 0

theorem eq_xorF_bitComp : ∀ v : Fin 64, v = xorF (bitComp v 0) (xorF (bitComp v 1)
    (xorF (bitComp v 2) (xorF (bitComp v 3) (xorF (bitComp v 4) (bitComp v 5))))) := by
  decide

@[expose] def boolPow {M : Type*} [One M] (c : Bool) (x : M) : M := if c then x else 1

@[expose] def coef1 (v : Fin 64) (i : Fin 6) : Bool := v.val.testBit i

@[expose] def coef2 (v : Fin 64) (i j : Fin 6) : Bool :=
  decide (i < j) && v.val.testBit i && v.val.testBit j

@[expose] def coefSum1 (l : List (Fin 64)) (i : Fin 6) : Bool :=
  l.foldr (fun v acc => xor (coef1 v i) acc) false

@[expose] def coefSum2 (l : List (Fin 64)) (i j : Fin 6) : Bool :=
  l.foldr (fun v acc => xor (coef2 v i j) acc) false

section QuadMap

variable {M : Type*} [CommGroup M]

structure IsQuadMap (q : Fin 64 → M) (b : Fin 64 → Fin 64 → M) : Prop where
  sq : ∀ x : M, x * x = 1
  q_xor : ∀ v w, q (xorF v w) = q v * q w * b v w
  b_xor : ∀ u v w, b u (xorF v w) = b u v * b u w
  b_comm : ∀ v w, b v w = b w v

@[expose] def linQ (q : Fin 64 → M) (b : Fin 64 → Fin 64 → M) (c₁ : Fin 6 → Bool)
    (c₂ : Fin 6 → Fin 6 → Bool) : M :=
  (∏ i, boolPow (c₁ i) (q (basisV i))) * ∏ i, ∏ j, boolPow (c₂ i j) (b (basisV i) (basisV j))

theorem boolPow_xor (hsq : ∀ x : M, x * x = 1) (c d : Bool) (x : M) :
    boolPow (xor c d) x = boolPow c x * boolPow d x := by
  cases c <;> cases d <;> simp [boolPow, hsq]

theorem linQ_xor (q : Fin 64 → M) (b : Fin 64 → Fin 64 → M) (hsq : ∀ x : M, x * x = 1)
    (c₁ d₁ : Fin 6 → Bool) (c₂ d₂ : Fin 6 → Fin 6 → Bool) :
    linQ q b (fun i => xor (c₁ i) (d₁ i)) (fun i j => xor (c₂ i j) (d₂ i j)) =
      linQ q b c₁ c₂ * linQ q b d₁ d₂ := by
  simp only [linQ, boolPow_xor hsq, Finset.prod_mul_distrib]
  rw [mul_mul_mul_comm]

namespace IsQuadMap

variable {q : Fin 64 → M} {b : Fin 64 → Fin 64 → M} (h : IsQuadMap q b)
include h

theorem b_zero (u : Fin 64) : b u 0 = 1 := by
  have h1 := h.b_xor u 0 0
  rw [show xorF 0 0 = 0 by decide] at h1
  calc b u 0 = b u 0 * b u 0 * (b u 0)⁻¹ := by group
    _ = 1 := by rw [← h1, mul_inv_cancel]

theorem q_zero : q 0 = 1 := by
  have h1 := h.q_xor 0 0
  rw [show xorF 0 0 = 0 by decide, h.b_zero, mul_one] at h1
  calc q 0 = q 0 * q 0 * (q 0)⁻¹ := by group
    _ = 1 := by rw [← h1, mul_inv_cancel]

theorem q_bitComp (v : Fin 64) (i : Fin 6) :
    q (bitComp v i) = boolPow (v.val.testBit i) (q (basisV i)) := by
  unfold bitComp boolPow
  split_ifs
  · rfl
  · exact h.q_zero

theorem b_bitComp (v : Fin 64) (i j : Fin 6) :
    b (bitComp v i) (bitComp v j) =
      boolPow (v.val.testBit i && v.val.testBit j) (b (basisV i) (basisV j)) := by
  unfold bitComp boolPow
  by_cases hi : v.val.testBit i <;> by_cases hj : v.val.testBit j <;> simp only [hi, hj] <;>
    simp only [Bool.and_self, Bool.and_false, Bool.false_and, ite_true, ite_false,
      Bool.false_eq_true]
  · exact h.b_zero _
  · rw [h.b_comm]
    exact h.b_zero _
  · exact h.b_zero _

theorem expand (v : Fin 64) : q v = linQ q b (coef1 v) (coef2 v) := by
  conv_lhs => rw [eq_xorF_bitComp v]
  simp only [h.q_xor, h.b_xor, h.q_bitComp, h.b_bitComp, linQ, coef1, coef2,
    Fin.prod_univ_six]
  simp +decide only [boolPow, decide_true, decide_false, Bool.true_and, Bool.false_and,
    Bool.false_eq_true, ite_false, one_mul, mul_one]
  ac_rfl

theorem prod_map_q (l : List (Fin 64)) : (l.map q).prod = linQ q b (coefSum1 l) (coefSum2 l) := by
  induction l with
  | nil => simp [linQ, boolPow, coefSum1, coefSum2]
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons, ih, h.expand v, ← linQ_xor q b h.sq]
    rfl

theorem prod_map_q_eq_one {l D : List (Fin 64)} (hD : ∀ o ∈ D, q o = 1)
    (h1 : coefSum1 l = coefSum1 D) (h2 : coefSum2 l = coefSum2 D) : (l.map q).prod = 1 := by
  rw [h.prod_map_q l, h1, h2, ← h.prod_map_q D]
  exact List.prod_eq_one fun x hx => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    exact hD o ho

end IsQuadMap

end QuadMap

end CFSG.ComponentClassification.AS81.Hexa
