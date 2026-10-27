module

public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KC.BM.Fi23Glue

open CFSG.Sporadic.GLQ

variable {G : Type*} [Group G]

@[expose] def invWord (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

theorem letter_neg (x y : G) (l : ℤ) (hl : l = 1 ∨ l = 2) : letter x y (-l) = (letter x y l)⁻¹ := by
  rcases hl with rfl | rfl <;> simp [letter]

theorem signedWord_append (x y : G) (u v : List ℤ) :
    signedWord x y (u ++ v) = signedWord x y u * signedWord x y v := by
  simp [signedWord]

theorem signedWord_invWord (x y : G) (p : List ℤ) (hp : ∀ l ∈ p, l = 1 ∨ l = 2) :
    signedWord x y (invWord p) = (signedWord x y p)⁻¹ := by
  induction p with
  | nil => simp [invWord, signedWord]
  | cons l p ih =>
    have hl := hp l List.mem_cons_self
    have ih := ih fun l' h => hp l' (List.mem_cons_of_mem _ h)
    have e : invWord (l :: p) = invWord p ++ [-l] := by simp [invWord]
    rw [e, signedWord_append, ih]
    simp [signedWord, letter_neg x y l hl, mul_inv_rev]

theorem signedWord_conj (x y : G) (p m : List ℤ) (hp : ∀ l ∈ p, l = 1 ∨ l = 2) :
    signedWord x y (p ++ m ++ invWord p) =
      signedWord x y p * signedWord x y m * (signedWord x y p)⁻¹ := by
  rw [signedWord_append, signedWord_append, signedWord_invWord x y p hp]

theorem eq_conj_of_mul_eq {a p d : G} (h : a * p = p * d) : a = p * d * p⁻¹ := by
  rw [← h, mul_inv_cancel_right]

theorem eq_conj_of_mul_eq' {r r' c : G} (h : c * r' = r * c) : r' = c⁻¹ * r * c := by
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem conj_sq {p d : G} (h : d * d = 1) : (p * d * p⁻¹) * (p * d * p⁻¹) = 1 := by
  simp [mul_assoc, ← mul_assoc d, h]

theorem comm_relator {X Y : G} (hX : X * X = 1) (hY : Y * Y = 1) (h : X * Y = Y * X) :
    X * Y * (X * Y) = 1 := by
  rw [mul_assoc, ← mul_assoc Y, ← h, mul_assoc, hY, mul_one, hX]

theorem edge_relator {X Y E : G} (hE : X * Y = E) (h : E * E * E = 1) :
    X * Y * (X * Y) * (X * Y) = 1 := by
  rw [hE, h]

theorem rank_of_cert {n k : ℕ} (hk : k ≤ n) {M P Q : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hPQ : P * M = Q)
    (hQ : LinearIndependent (ZMod 2) (fun i : {i : Fin n // i.val < k} => Q i))
    (hQ0 : ∀ i : Fin n, k ≤ i.val → Q i = 0)
    (hP : LinearIndependent (ZMod 2) (fun i : {i : Fin n // k ≤ i.val} => P i)) :
    M.rank = k := by
  have hrow : ∀ i, M.vecMulLinear (P i) = Q i := by
    intro i
    rw [← hPQ]
    rfl
  have hrk : M.rank = Module.finrank (ZMod 2) (LinearMap.range M.vecMulLinear) := by
    rw [Matrix.rank_eq_finrank_span_row, range_vecMulLinear]
  have hlow : k ≤ Module.finrank (ZMod 2) (LinearMap.range M.vecMulLinear) := by
    have hli : LinearIndependent (ZMod 2) (fun i : {i : Fin n // i.val < k} =>
        (⟨Q i, P i, hrow i⟩ : LinearMap.range M.vecMulLinear)) :=
      LinearIndependent.of_comp (LinearMap.range M.vecMulLinear).subtype hQ
    have := hli.fintype_card_le_finrank
    rwa [Fintype.card_fin_lt_of_le hk] at this
  have hc : Fintype.card {i : Fin n // k ≤ i.val} = n - k := by
    have e : Fintype.card {i : Fin n // k ≤ i.val} = Fintype.card {i : Fin n // ¬ i.val < k} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i => not_lt.symm)
    rw [e, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_fin_lt_of_le hk]
  let A : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.of fun i j => if k ≤ i.val then P i j else 0
  have hA : A * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    by_cases h : k ≤ i.val
    · have e := congrFun (hQ0 i h) j
      rw [← hPQ, Matrix.mul_apply] at e
      simpa [A, h] using e
    · simp [A, h]
  have hAr : n - k ≤ A.rank := by
    rw [Matrix.rank_eq_finrank_span_row]
    have hmem : ∀ i : {i : Fin n // k ≤ i.val},
        P i ∈ Submodule.span (ZMod 2) (Set.range A.row) := by
      intro i
      have e : A.row i = P i := by
        funext j
        simp [A, Matrix.row, i.2]
      rw [← e]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hli : LinearIndependent (ZMod 2) (fun i : {i : Fin n // k ≤ i.val} =>
        (⟨P i, hmem i⟩ : Submodule.span (ZMod 2) (Set.range A.row))) :=
      LinearIndependent.of_comp (Submodule.span (ZMod 2) (Set.range A.row)).subtype hP
    have h := hli.fintype_card_le_finrank
    rwa [hc] at h
  have hsum := Matrix.rank_add_rank_le_card_of_mul_eq_zero hA
  rw [Fintype.card_fin] at hsum
  omega

end CFSG.KC.BM.Fi23Glue

end
