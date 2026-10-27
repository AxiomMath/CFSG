module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Span

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Form

open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Span

@[expose] def dense (u : List (ℕ × ℤ)) (a : ℕ) : ℤ :=
  (u.map fun x => if x.1 = a then x.2 else 0).sum

@[expose] def colZ (L : List Entry) (p a : ℕ) : ℤ :=
  applyEnt (R := ℤ) L (fun r => if r = p then 1 else 0) a

theorem dense_colOf (L : List Entry) (p a : ℕ) : dense (colOf L p) a = colZ L p a := by
  induction L with
  | nil => simp [dense, colOf, colZ, applyEnt]
  | cons e L ih =>
    have h1 : colZ (e :: L) p a = (if e.2.1 = a then (e.2.2 : ℤ) * (if e.1 = p then 1 else 0) else 0)
        + colZ L p a := by
      simp [colZ, applyEnt]
    have h2 : dense (colOf (e :: L) p) a =
        (if e.1 = p then (if e.2.1 = a then e.2.2 else 0) else 0) + dense (colOf L p) a := by
      by_cases hep : e.1 = p
      · simp [colOf, List.filter_cons, dense, hep]
      · simp [colOf, List.filter_cons, dense, hep]
    rw [h1, h2, ih]
    by_cases hep : e.1 = p <;> by_cases hea : e.2.1 = a <;> simp [hep, hea]

@[expose] def Bz (A B : ℕ → ℤ) : ℤ :=
  ∑ a ∈ Finset.range 28, ∑ b ∈ Finset.range 28, A a * gramZ a b * B b

theorem dense_cons (x : ℕ × ℤ) (u : List (ℕ × ℤ)) (a : ℕ) :
    dense (x :: u) a = (if x.1 = a then x.2 else 0) + dense u a := by
  simp [dense]

theorem dense_nil (a : ℕ) : dense [] a = 0 := by simp [dense]

theorem sum_gram_dense (a : ℕ) (w : List (ℕ × ℤ)) (hw : ∀ y ∈ w, y.1 < 28) :
    ∑ b ∈ Finset.range 28, gramZ a b * dense w b =
      (w.map fun y => y.2 * gramZ a y.1).sum := by
  induction w with
  | nil => simp [dense_nil]
  | cons y w ih =>
    have hy : y.1 < 28 := hw y (by simp)
    have ih' := ih (fun z hz => hw z (by simp [hz]))
    simp only [dense_cons, mul_add, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [ih']
    congr 1
    have e : ∀ b, gramZ a b * (if y.1 = b then y.2 else 0) =
        if y.1 = b then gramZ a b * y.2 else 0 := by
      intro b
      split_ifs <;> simp
    simp only [mul_ite, mul_zero, e]
    rw [Finset.sum_ite_eq]
    simp [hy]
    ring

theorem Bz_dense_cons (x : ℕ × ℤ) (u : List (ℕ × ℤ)) (B : ℕ → ℤ) (hx : x.1 < 28) :
    Bz (dense (x :: u)) B = x.2 * (∑ b ∈ Finset.range 28, gramZ x.1 b * B b) + Bz (dense u) B := by
  unfold Bz
  simp only [dense_cons, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  congr 1
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have e : ∀ a, (if x.1 = a then x.2 * gramZ a b * B b else 0) = (if x.1 = a then x.2 * gramZ a b * B b else 0) := fun a => rfl
  rw [Finset.sum_ite_eq]
  simp [hx]
  ring

theorem Bz_dense_left (u : List (ℕ × ℤ)) (hu : ∀ x ∈ u, x.1 < 28) (B : ℕ → ℤ) :
    Bz (dense u) B = (u.map fun x => x.2 * ∑ b ∈ Finset.range 28, gramZ x.1 b * B b).sum := by
  induction u with
  | nil => simp [Bz, dense_nil]
  | cons x u ih =>
    have hx : x.1 < 28 := hu x (by simp)
    have ih' := ih (fun y hy => hu y (by simp [hy]))
    rw [Bz_dense_cons x u B hx, ih']
    simp only [List.map_cons, List.sum_cons]

theorem bilinZ_eq_Bz (u w : List (ℕ × ℤ)) (hu : ∀ x ∈ u, x.1 < 28) (hw : ∀ y ∈ w, y.1 < 28) :
    bilinZ u w = Bz (dense u) (dense w) := by
  rw [Bz_dense_left u hu]
  unfold bilinZ
  congr 1
  apply List.map_congr_left
  intro x hx
  rw [sum_gram_dense x.1 w hw, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro y _
  ring

theorem valid_rows : (∀ n < 4, ∀ k ∈ [1, 2], ∀ e ∈ entries Tag.D4 n k, e.2.1 < 28) ∧
    (∀ n < 4, ∀ k ∈ [1, 2], ∀ e ∈ entries Tag.D4 (negI n) k, e.2.1 < 28) := by
  decide +kernel

theorem colList_rows (i : ℕ) (hi : i < 4) (sgn : Bool) (k : ℕ) (hk : k ≤ 2) (p : ℕ) (hp : p < 28) :
    ∀ x ∈ colList i sgn k p, x.1 < 28 := by
  intro x hx
  unfold colList at hx
  by_cases hk0 : k = 0
  · simp only [hk0, if_true, List.mem_singleton] at hx
    subst hx
    exact hp
  · simp only [hk0, if_false] at hx
    have hk12 : k = 1 ∨ k = 2 := by omega
    unfold colOf at hx
    simp only [List.mem_map, List.mem_filter] at hx
    obtain ⟨e, ⟨he, -⟩, rfl⟩ := hx
    by_cases hs : sgn = true
    · simp only [hs, if_true] at he
      have := valid_rows.1 i hi k (by rcases hk12 with rfl | rfl <;> simp) e he
      exact this
    · simp only [hs, Bool.false_eq_true, if_false] at he
      have := valid_rows.2 i hi k (by rcases hk12 with rfl | rfl <;> simp) e he
      exact this

theorem colZ_cast {K : Type} [Field K] (L : List Entry) (p a : ℕ) :
    ((colZ L p a : ℤ) : K) = applyEnt L (fun q => if q = p then (1 : K) else 0) a := by
  unfold colZ
  have h := applyEnt_map' (Int.castRingHom K) L (fun r : ℕ => (if r = p then (1 : ℤ) else 0)) a
  simp only [Int.coe_castRingHom] at h
  rw [h]
  congr 1
  funext q
  split_ifs <;> simp

section KLevel

variable {K : Type} [Field K]

@[expose] def Bzk (A B : ℕ → K) : K :=
  ∑ a ∈ Finset.range 28, ∑ b ∈ Finset.range 28, A a * (gramZ a b : K) * B b

theorem Bzk_add_left (A A' B : ℕ → K) : Bzk (fun a => A a + A' a) B = Bzk A B + Bzk A' B := by
  unfold Bzk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem Bzk_add_right (A B B' : ℕ → K) : Bzk A (fun b => B b + B' b) = Bzk A B + Bzk A B' := by
  unfold Bzk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem Bzk_smul_left (k : K) (A B : ℕ → K) : Bzk (fun a => k * A a) B = k * Bzk A B := by
  unfold Bzk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem Bzk_smul_right (k : K) (A B : ℕ → K) : Bzk A (fun b => k * B b) = k * Bzk A B := by
  unfold Bzk
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem Bzk_expand (P0 P1 P2 Q0 Q1 Q2 : ℕ → K) (c : K) :
    Bzk (fun a => P0 a + c * P1 a + c ^ 2 * P2 a) (fun b => Q0 b + c * Q1 b + c ^ 2 * Q2 b) =
      Bzk P0 Q0 + c * (Bzk P0 Q1 + Bzk P1 Q0) + c ^ 2 * (Bzk P0 Q2 + Bzk P1 Q1 + Bzk P2 Q0) +
        c ^ 3 * (Bzk P1 Q2 + Bzk P2 Q1) + c ^ 4 * Bzk P2 Q2 := by
  have hL : ∀ (A : ℕ → K), Bzk (fun a => P0 a + c * P1 a + c ^ 2 * P2 a) A =
      Bzk P0 A + c * Bzk P1 A + c ^ 2 * Bzk P2 A := by
    intro A
    rw [Bzk_add_left, Bzk_add_left, Bzk_smul_left, Bzk_smul_left]
  rw [hL]
  simp only [Bzk_add_right, Bzk_smul_right]
  ring

theorem Bzk_intcast (A B : ℕ → ℤ) :
    Bzk (fun a => (A a : K)) (fun b => (B b : K)) = ((Bz A B : ℤ) : K) := by
  unfold Bzk Bz
  push_cast
  rfl

theorem pcoord_posVec_fun {K : Type} [Field K] (p : ℕ) (hp : p < dim Tag.D4) :
    (fun a : ℕ => pcoord K (posVec Tag.D4 K p) a) = fun a => if a = p then (1 : K) else 0 := by
  funext a
  rw [pcoord, posCoord_posVec hp]

theorem Bzk_delta (p q : ℕ) (hp : p < 28) (hq : q < 28) :
    Bzk (fun a : ℕ => if a = p then (1 : K) else 0) (fun b : ℕ => if b = q then (1 : K) else 0) =
      (gramZ p q : K) := by
  unfold Bzk
  simp [Finset.sum_ite_eq', hp, hq]

end KLevel

theorem dense_colList_zero (i : ℕ) (sgn : Bool) (p : ℕ) :
    dense (colList i sgn 0 p) = fun a => if a = p then 1 else 0 := by
  funext a
  simp only [dense, colList, if_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

theorem dense_colList_pos (i k p : ℕ) (hk : k ≠ 0) :
    dense (colList i true k p) = colZ (entries Tag.D4 i k) p := by
  funext a
  simp only [colList, hk, if_false, if_true, dense_colOf]

theorem dense_colList_neg (i k p : ℕ) (hk : k ≠ 0) :
    dense (colList i false k p) = colZ (entries Tag.D4 (negI i) k) p := by
  funext a
  simp only [colList, hk, if_false, Bool.false_eq_true, dense_colOf]

theorem bilinZ_colList_zero (i : ℕ) (sgn : Bool) (p q : ℕ) :
    bilinZ (colList i sgn 0 p) (colList i sgn 0 q) = gramZ p q := by
  simp [colList, bilinZ]

theorem intcast_even_zero {K : Type} [Field K] [CharP K 2] (n : ℤ) (h : n % 2 = 0) :
    (n : K) = 0 := by
  obtain ⟨m, rfl⟩ := Int.dvd_of_emod_eq_zero h
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  push_cast
  rw [h2, zero_mul]

theorem pcoord_endHom_basis_pos {K : Type} [Field K] (i : ℕ) (hi : i < 4) (c : K) (p : ℕ)
    (hp : p < 28) :
    (fun a : ℕ => pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
        (Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) (posVec Tag.D4 K p)) a) =
      fun a => ((dense (colList i true 0 p) a : ℤ) : K) +
        c * ((dense (colList i true 1 p) a : ℤ) : K) +
        c ^ 2 * ((dense (colList i true 2 p) a : ℤ) : K) := by
  funext a
  have hdp : p < dim Tag.D4 := by
    have : dim Tag.D4 = 28 := by decide +kernel
    omega
  have h1 := pcoord_endHom_pos (K := K) ⟨i, hi⟩ c (posVec Tag.D4 K p) a
    (valid_pos i hi 1 (Or.inl rfl)) (valid_pos i hi 2 (Or.inr rfl))
  have hpa : pcoord K (posVec Tag.D4 K p) a = if a = p then (1 : K) else 0 := by
    rw [pcoord, posCoord_posVec hdp]
  rw [h1, hpa]
  have hf : (fun q : ℕ => pcoord K (posVec Tag.D4 K p) q) = fun q => if q = p then (1 : K) else 0 :=
    pcoord_posVec_fun p hdp
  simp only [Fin.val_mk]
  rw [hf, dense_colList_zero, dense_colList_pos i 1 p (by norm_num),
    dense_colList_pos i 2 p (by norm_num)]
  rw [colZ_cast, colZ_cast]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]

theorem Bzk_colList {K : Type} [Field K] (i : ℕ) (hi : i < 4) (sgn : Bool) (k l p q : ℕ)
    (hk : k ≤ 2) (hl : l ≤ 2) (hp : p < 28) (hq : q < 28) :
    Bzk (fun a => ((dense (colList i sgn k p) a : ℤ) : K))
        (fun b => ((dense (colList i sgn l q) b : ℤ) : K)) =
      ((bilinZ (colList i sgn k p) (colList i sgn l q) : ℤ) : K) := by
  rw [Bzk_intcast, bilinZ_eq_Bz _ _ (colList_rows i hi sgn k hk p hp)
    (colList_rows i hi sgn l hl q hq)]

theorem Bzk_basis_of_formula {K : Type} [Field K] [CharP K 2] (i : ℕ) (hi : i < 4) (sgn : Bool)
    (c : K) (p q : ℕ) (hp : p < 28) (hq : q < 28) (X : ℕ → ℕ → K)
    (hX : ∀ r : ℕ, r < 28 → X r = fun a => ((dense (colList i sgn 0 r) a : ℤ) : K) +
        c * ((dense (colList i sgn 1 r) a : ℤ) : K) + c ^ 2 * ((dense (colList i sgn 2 r) a : ℤ) : K))
    (hgram : ∀ d ∈ [1, 2, 3, 4], crossSum i sgn p q d % 2 = 0) :
    Bzk (X p) (X q) = (gramZ p q : K) := by
  rw [hX p hp, hX q hq]
  have e := Bzk_expand (fun a => ((dense (colList i sgn 0 p) a : ℤ) : K))
    (fun a => ((dense (colList i sgn 1 p) a : ℤ) : K)) (fun a => ((dense (colList i sgn 2 p) a : ℤ) : K))
    (fun b => ((dense (colList i sgn 0 q) b : ℤ) : K)) (fun b => ((dense (colList i sgn 1 q) b : ℤ) : K))
    (fun b => ((dense (colList i sgn 2 q) b : ℤ) : K)) c
  rw [e]
  rw [Bzk_colList i hi sgn 0 0 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 0 1 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 1 0 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 0 2 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 1 1 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 2 0 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 1 2 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 2 1 p q (by norm_num) (by norm_num) hp hq,
    Bzk_colList i hi sgn 2 2 p q (by norm_num) (by norm_num) hp hq]
  have h0 : bilinZ (colList i sgn 0 p) (colList i sgn 0 q) = gramZ p q := bilinZ_colList_zero i sgn p q
  have hc1 : bilinZ (colList i sgn 0 p) (colList i sgn 1 q) + bilinZ (colList i sgn 1 p) (colList i sgn 0 q)
      = crossSum i sgn p q 1 := by simp [crossSum, List.range_succ]
  have hc2 : bilinZ (colList i sgn 0 p) (colList i sgn 2 q) + bilinZ (colList i sgn 1 p) (colList i sgn 1 q)
      + bilinZ (colList i sgn 2 p) (colList i sgn 0 q) = crossSum i sgn p q 2 := by
    simp [crossSum, List.range_succ]
    ring
  have hc3 : bilinZ (colList i sgn 1 p) (colList i sgn 2 q) + bilinZ (colList i sgn 2 p) (colList i sgn 1 q)
      = crossSum i sgn p q 3 := by simp [crossSum, List.range_succ]
  have hc4 : bilinZ (colList i sgn 2 p) (colList i sgn 2 q) = crossSum i sgn p q 4 := by
    simp [crossSum, List.range_succ]
  have z1 := intcast_even_zero (K := K) _ (hgram 1 (by simp))
  have z2 := intcast_even_zero (K := K) _ (hgram 2 (by simp))
  have z3 := intcast_even_zero (K := K) _ (hgram 3 (by simp))
  have z4 := intcast_even_zero (K := K) _ (hgram 4 (by simp))
  have g1 : ((bilinZ (colList i sgn 0 p) (colList i sgn 1 q) : ℤ) : K) +
      ((bilinZ (colList i sgn 1 p) (colList i sgn 0 q) : ℤ) : K) = ((crossSum i sgn p q 1 : ℤ) : K) := by
    rw [← hc1]; push_cast; ring
  have g2 : ((bilinZ (colList i sgn 0 p) (colList i sgn 2 q) : ℤ) : K) +
      ((bilinZ (colList i sgn 1 p) (colList i sgn 1 q) : ℤ) : K) +
      ((bilinZ (colList i sgn 2 p) (colList i sgn 0 q) : ℤ) : K) = ((crossSum i sgn p q 2 : ℤ) : K) := by
    rw [← hc2]; push_cast; ring
  have g3 : ((bilinZ (colList i sgn 1 p) (colList i sgn 2 q) : ℤ) : K) +
      ((bilinZ (colList i sgn 2 p) (colList i sgn 1 q) : ℤ) : K) = ((crossSum i sgn p q 3 : ℤ) : K) := by
    rw [← hc3]; push_cast; ring
  have g4 : ((bilinZ (colList i sgn 2 p) (colList i sgn 2 q) : ℤ) : K) = ((crossSum i sgn p q 4 : ℤ) : K) := by
    rw [hc4]
  rw [h0, g1, g2, g3, g4, z1, z2, z3, z4]
  simp

theorem pcoord_endHom_basis_neg {K : Type} [Field K] (i : ℕ) (hi : i < 4) (c : K) (p : ℕ)
    (hp : p < 28) :
    (fun a : ℕ => pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4)
        (-Pi.single (⟨i, hi⟩ : Fin Tag.D4.rank) 1) c) (posVec Tag.D4 K p)) a) =
      fun a => ((dense (colList i false 0 p) a : ℤ) : K) +
        c * ((dense (colList i false 1 p) a : ℤ) : K) +
        c ^ 2 * ((dense (colList i false 2 p) a : ℤ) : K) := by
  funext a
  have hdp : p < dim Tag.D4 := by
    have : dim Tag.D4 = 28 := by decide +kernel
    omega
  have h1 := pcoord_endHom_neg (K := K) ⟨i, hi⟩ c (posVec Tag.D4 K p) a
    (valid_neg' i hi 1 (Or.inl rfl)) (valid_neg' i hi 2 (Or.inr rfl))
  have hpa : pcoord K (posVec Tag.D4 K p) a = if a = p then (1 : K) else 0 := by
    rw [pcoord, posCoord_posVec hdp]
  rw [h1, hpa]
  have hf : (fun q : ℕ => pcoord K (posVec Tag.D4 K p) q) = fun q => if q = p then (1 : K) else 0 :=
    pcoord_posVec_fun p hdp
  simp only [Fin.val_mk]
  rw [← negI_eq i hi]
  rw [hf, dense_colList_zero, dense_colList_neg i 1 p (by norm_num),
    dense_colList_neg i 2 p (by norm_num)]
  rw [colZ_cast, colZ_cast]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]

end CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Form

end
