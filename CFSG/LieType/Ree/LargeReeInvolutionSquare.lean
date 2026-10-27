module

public import CFSG.LieType.Ree.LargeReeInvolutionCoordinates

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeCover

@[expose] def sqCoords : List Poly :=
  [[],
   [],
   [[0, 1]],
   [],
   [[1, 13]],
   [[0, 2], [3, 13]],
   [[1, 1, 13]],
   [[0, 1, 1, 13], [0, 1, 2], [0, 14], [1, 5], [2, 3]],
   [[0, 0, 1, 1, 13], [0, 0, 14], [3, 3, 13]],
   [],
   [[12, 13]],
   [[1, 12, 13], [1, 15], [2, 12]],
   [[0, 2, 12], [0, 7], [3, 15], [5, 12]],
   [[1, 1, 15], [12, 14]],
   [[0, 1, 1, 12, 13], [0, 1, 2, 12], [0, 1, 7], [0, 12, 14], [0, 17], [1, 3, 15], [1, 4],
     [1, 5, 12], [3, 7], [9, 12]],
   [[0, 0, 1, 1, 12, 13], [0, 0, 12, 14], [0, 0, 17], [3, 3, 15], [12, 19]],
   [[2, 2, 12], [12, 13, 14], [13, 17], [14, 15]],
   [[0, 1, 2, 12, 13], [0, 1, 7, 13], [0, 2, 7], [0, 13, 17], [0, 21], [1, 3, 12, 13, 13],
     [1, 4, 13], [1, 5, 15], [2, 4], [2, 5, 12], [5, 7], [9, 12, 13], [9, 15], [10, 13]],
   [[0, 0, 2, 2, 12], [0, 0, 13, 17], [0, 0, 21], [3, 3, 12, 13, 13], [3, 3, 13, 15],
     [5, 5, 12], [12, 13, 19], [13, 16], [15, 19]],
   [[0, 1, 1, 1, 12, 13, 13], [0, 1, 1, 7, 13], [0, 1, 2, 7], [0, 1, 12, 13, 14], [0, 1, 21],
     [0, 2, 17], [0, 7, 14], [1, 1, 4, 13], [1, 1, 5, 15], [1, 2, 3, 12, 13], [1, 2, 4],
     [1, 11], [2, 2, 3, 12], [2, 9, 12], [2, 10], [3, 12, 13, 14], [3, 13, 17], [3, 14, 15],
     [3, 21], [4, 14], [5, 12, 14], [5, 17], [7, 9]],
   [[0, 0, 1, 1, 1, 12, 13, 13], [0, 0, 1, 1, 2, 12, 13], [0, 0, 1, 2, 2, 12],
     [0, 0, 1, 12, 13, 14], [0, 0, 1, 21], [0, 0, 2, 12, 14], [0, 0, 2, 17],
     [0, 1, 1, 3, 12, 13, 13], [0, 1, 2, 3, 12, 13], [0, 1, 2, 5, 12], [0, 1, 3, 7, 13],
     [0, 1, 5, 7], [0, 2, 2, 3, 12], [0, 2, 3, 7], [0, 3, 12, 13, 14], [0, 3, 13, 17],
     [0, 3, 21], [0, 5, 17], [0, 6], [1, 3, 3, 12, 13, 13], [1, 3, 4, 13], [1, 3, 5, 12, 13],
     [1, 3, 5, 15], [1, 4, 5], [1, 22], [2, 3, 3, 12, 13], [2, 3, 3, 15], [2, 3, 4],
     [2, 3, 5, 12], [2, 12, 19], [2, 16], [3, 5, 7], [3, 9, 12, 13], [3, 10, 13], [3, 11],
     [4, 9], [5, 9, 12], [5, 10], [7, 19]],
   [[0, 0, 1, 1, 2, 2, 12], [0, 0, 1, 1, 12, 13, 14], [0, 0, 1, 1, 13, 17], [0, 0, 1, 1, 21],
     [0, 0, 12, 14, 14], [0, 0, 14, 17], [1, 1, 3, 3, 13, 15], [1, 1, 5, 5, 12],
     [1, 1, 12, 13, 19], [1, 1, 13, 16], [1, 1, 22], [3, 3, 12, 13, 14], [3, 3, 13, 17],
     [3, 3, 21], [9, 9, 12], [12, 14, 19], [14, 16], [17, 19]],
   [[0, 0, 1, 1, 1, 1, 12, 13, 13, 13], [0, 0, 1, 1, 2, 2, 12, 13],
     [0, 0, 1, 1, 12, 13, 13, 14], [0, 0, 1, 1, 13, 13, 17], [0, 0, 2, 2, 17],
     [0, 0, 13, 14, 17], [0, 0, 14, 21], [1, 1, 3, 3, 13, 13, 15], [1, 1, 5, 5, 12, 13],
     [1, 1, 5, 5, 15], [1, 1, 12, 13, 13, 19], [1, 1, 13, 13, 16], [2, 2, 3, 3, 15],
     [2, 2, 12, 19], [2, 2, 16], [3, 3, 13, 14, 15], [5, 5, 12, 14], [5, 5, 17], [9, 9, 12, 13],
     [9, 9, 15], [12, 13, 14, 19], [13, 14, 16], [13, 23], [14, 22], [19, 21]],
   [[0, 0, 1, 1, 2, 2, 12, 15], [0, 0, 1, 1, 12, 12, 13, 13, 14], [0, 0, 1, 1, 13, 15, 17],
     [0, 0, 1, 1, 15, 21], [0, 0, 2, 2, 12, 12, 14], [0, 0, 2, 2, 12, 17], [0, 0, 7, 7, 14],
     [0, 0, 12, 12, 13, 14, 14], [0, 0, 12, 13, 14, 17], [0, 0, 13, 17, 17], [0, 0, 17, 21],
     [1, 1, 3, 3, 12, 12, 13, 13, 13], [1, 1, 3, 3, 12, 13, 13, 15], [1, 1, 3, 3, 13, 15, 15],
     [1, 1, 5, 5, 12, 15], [1, 1, 12, 13, 15, 19], [1, 1, 13, 15, 16], [1, 1, 15, 22],
     [2, 2, 3, 3, 12, 12, 13], [2, 2, 3, 3, 12, 15], [2, 2, 12, 12, 19],
     [3, 3, 12, 12, 13, 13, 14], [3, 3, 12, 13, 14, 15], [4, 4, 14], [5, 5, 12, 12, 14],
     [5, 5, 12, 17], [7, 7, 19], [9, 9, 12, 12, 13], [9, 9, 12, 15], [10, 10, 13],
     [12, 12, 13, 14, 19], [12, 18], [13, 16, 17], [14, 15, 16], [15, 17, 19], [15, 23],
     [16, 21], [17, 22]]]

theorem sqCoords_check : collectCheck 6000 (sylowWord ++ sylowWord) sqCoords = true := by
  decide +kernel

@[expose] def oneG : Poly :=
  [[3, 5, 7], [3, 11], [3, 21], [4, 9], [5, 9], [5, 10], [5, 17], [7, 19]]

@[expose] def oneJ : Poly :=
  [[3, 7], [17]]

@[expose] def oneH : Poly :=
  [[3, 15], [5]]

@[expose] def oneConst : List (ℕ × Poly) :=
  [(0, [[]]), (12, [[]]), (1, []), (13, []), (2, []), (14, [])]

@[expose] def oneSubsts : List (List (ℕ × Poly)) :=
  [[(6, oneG), (6 + 12, sigmaPoly oneG)], [(9, oneJ), (9 + 12, sigmaPoly oneJ)],
    [(7, oneH), (7 + 12, sigmaPoly oneH)], oneConst]

theorem oneSubsts_check : ∀ n : Fin 24, polySubstSeq oneSubsts (sqCoords.getD n []) = [] := by
  decide +kernel

@[expose] def cOneK : Poly :=
  [[9, 17]]

@[expose] def cOneE : Poly :=
  [[5, 17]]

@[expose] def cOneH : Poly :=
  [[17]]

@[expose] def cOneConst : List (ℕ × Poly) :=
  [(0, []), (12, []), (1, []), (13, []), (2, [[]]), (14, [[]]), (3, []), (15, [])]

@[expose] def cOneSubsts : List (List (ℕ × Poly)) :=
  [[(10, cOneK), (10 + 12, sigmaPoly cOneK)], [(4, cOneE), (4 + 12, sigmaPoly cOneE)],
    [(7, cOneH), (7 + 12, sigmaPoly cOneH)], cOneConst]

theorem cOneSubsts_check :
    ∀ n : Fin 24, polySubstSeq cOneSubsts (sqCoords.getD n []) = [] := by
  decide +kernel

@[expose] def cZeroConst : List (ℕ × Poly) :=
  [(0, []), (12, []), (1, []), (13, []), (2, []), (14, []), (3, []), (15, []), (5, []), (17, []),
    (7, []), (19, [])]

theorem cZero_check : sqCoords.map (polySubst (substOf cZeroConst)) =
    [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [[4, 9]], [],
      [], [[16, 21]]] := by
  decide +kernel

section Square

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

omit [Finite K] in
theorem sylowV_sq_eq_one_iff
    (a b c d e f g h i j k l : K) :
    sylowV m K a b c d e f g h i j k l ^ 2 = 1 ↔
      ∀ n : Fin 24, polyEval (coordVal m a b c d e f g h i j k l) (sqCoords.getD n []) = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sq, sylowV_eq_wordEval, ← wordEval_append]
  exact wordEval_eq_one_iff sqCoords_check _

omit [Finite K] in
theorem sq_eq_one_b
    {a b c d e f g h i j k l : K}
    (hv : sylowV m K a b c d e f g h i j k l ^ 2 = 1) : b = 0 := by
  have h28 : polyEval (coordVal m a b c d e f g h i j k l) (sqCoords.getD 4 []) = 0 :=
    (sylowV_sq_eq_one_iff a b c d e f g h i j k l).1 hv 4
  rw [show sqCoords.getD 4 [] = [[1, 13]] by decide +kernel] at h28
  simp only [polyEval, monoEval, coordVal, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero, mul_eq_zero,
    largeReeSigma_eq_zero_iff, or_self] at h28
  exact h28

omit [Finite K] in
theorem sq_eq_one_d
    {b c d e f g h i j k l : K}
    (hv : sylowV m K 0 b c d e f g h i j k l ^ 2 = 1) : d = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have hb := sq_eq_one_b hv
  have h36 : polyEval (coordVal m 0 b c d e f g h i j k l) (sqCoords.getD 12 []) = 0 :=
    (sylowV_sq_eq_one_iff 0 b c d e f g h i j k l).1 hv 12
  rw [polyEval_eq_of_polySubst (l := [(0, []), (12, []), (1, []), (13, [])])
    (by simp [polyEval, coordVal, hb, largeReeSigma_zero]) (q := [[3, 15]])
    (by decide +kernel)] at h36
  simpa [polyEval, monoEval, coordVal, largeReeSigma_eq_zero_iff] using h36

theorem sylowV_one_sq_eq_one_iff
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    (b c d e f g h i j k l : K) :
    sylowV m K 1 b c d e f g h i j k l ^ 2 = 1 ↔
      b = 0 ∧ c = 0 ∧ h = f + d * largeReeSigma m d ∧ j = d * h + largeReeSigma m f ∧
        g = h * largeReeSigma m h + f * k + e * j + d * l + d * f * h + f * j +
          f * largeReeSigma m f + d * largeReeSigma m j := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [sylowV_sq_eq_one_iff]
  set x := coordVal m (1 : K) b c d e f g h i j k l with hx
  constructor
  · intro hc
    have hb : b = 0 := sq_eq_one_b ((sylowV_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _ _ _).2 hc)
    have hc0 : c = 0 := by
      have h29 : polyEval x (sqCoords.getD 5 []) = 0 := hc 5
      rw [polyEval_eq_of_polySubst (l := [(0, [[]]), (12, [[]]), (1, []), (13, [])])
        (by simp [polyEval, monoEval, hx, coordVal, hb, largeReeSigma_zero, largeReeSigma_one])
        (q := [[2]]) (by decide +kernel)] at h29
      simpa [polyEval, monoEval, hx, coordVal] using h29
    have hL : ∀ e ∈ oneConst, polyEval x e.2 = x e.1 := by
      simp [oneConst, polyEval, monoEval, hx, coordVal, hb, hc0, largeReeSigma_zero,
        largeReeSigma_one]
    have h36 : polyEval x (sqCoords.getD 12 []) = 0 := hc 12
    have h38 : polyEval x (sqCoords.getD 14 []) = 0 := hc 14
    have h44 : polyEval x (sqCoords.getD 20 []) = 0 := hc 20
    rw [polyEval_eq_of_polySubst hL (q := [[3, 15], [5], [7]]) (by decide +kernel)] at h36
    rw [polyEval_eq_of_polySubst hL (q := [[3, 7], [9], [17]]) (by decide +kernel)] at h38
    rw [polyEval_eq_of_polySubst hL (q := [[3, 5, 7], [3, 11], [3, 21], [4, 9], [5, 9], [5, 10],
      [5, 17], [6], [7, 19]]) (by decide +kernel)] at h44
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h36 h38 h44
    refine ⟨hb, hc0, ?_, ?_, ?_⟩
    · exact eq_of_add_eq_zero_two (by linear_combination h36)
    · exact eq_of_add_eq_zero_two (by linear_combination h38)
    · exact eq_of_add_eq_zero_two (by linear_combination h44)
  · rintro ⟨hb, hc0, hh, hj, hg⟩ n
    refine polyEval_eq_zero_of_polySubstSeq (fun l hl => ?_) (oneSubsts_check n)
    simp only [oneSubsts, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
      simp only [oneG, polyEval, monoEval, coordVal, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
      rw [hg]
      ring
    · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
      simp only [oneJ, polyEval, monoEval, coordVal, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
      rw [hj]
    · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
      simp only [oneH, polyEval, monoEval, coordVal, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
      rw [hh]
      ring
    · simp [oneConst, polyEval, monoEval, hx, coordVal, hb, hc0, largeReeSigma_zero,
        largeReeSigma_one]

omit [CharP K F4.prime] in
theorem largeReeSigma_injective (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Function.Injective (largeReeSigma m : K → K) := by
  obtain ⟨σ, hσ, -⟩ := exists_sigma hK
  intro u v huv
  rw [← hσ, ← hσ] at huv
  exact σ.injective huv

omit [Finite K] [CharP K F4.prime] in
theorem largeReeSigma_mul (u v : K) :
    largeReeSigma m (u * v) = largeReeSigma m u * largeReeSigma m v :=
  mul_pow u v _

theorem sylowV_zero_one_sq_eq_one_iff
    (hK : Nat.card K = 2 ^ (2 * m + 1))
    (b d e f g h i j k l : K) :
    sylowV m K 0 b 1 d e f g h i j k l ^ 2 = 1 ↔
      b = 0 ∧ d = 0 ∧ h = largeReeSigma m f ∧ e = f * largeReeSigma m f ∧
        k = largeReeSigma m f * j := by
  have : CharP K 2 := ‹CharP K F4.prime›
  constructor
  · intro hv
    have hb := sq_eq_one_b hv
    have hd := sq_eq_one_d hv
    have hc := (sylowV_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hv
    set x := coordVal m (0 : K) b 1 d e f g h i j k l with hx
    have hL : ∀ e ∈ cOneConst, polyEval x e.2 = x e.1 := by
      simp [cOneConst, polyEval, monoEval, hx, coordVal, hb, hd, largeReeSigma_zero,
        largeReeSigma_one]
    have h41 : polyEval x (sqCoords.getD 17 []) = 0 := hc 17
    have h43 : polyEval x (sqCoords.getD 19 []) = 0 := hc 19
    rw [polyEval_eq_of_polySubst hL (q := [[4], [5, 7]]) (by decide +kernel)] at h41
    rw [polyEval_eq_of_polySubst hL (q := [[4], [5, 17], [7, 9], [10]]) (by decide +kernel)] at h43
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h41 h43
    have he : e = f * h := eq_of_add_eq_zero_two h41
    have hk : k = e + f * largeReeSigma m f + h * j :=
      eq_of_add_eq_zero_two (by linear_combination h43)
    have h44 : polyEval x (sqCoords.getD 20 []) = 0 := hc 20
    rw [← polyEval_polySubstSeq (ls := [[(10, [[4], [5, 17], [7, 9]]),
      (10 + 12, sigmaPoly [[4], [5, 17], [7, 9]])], [(4, [[5, 7]]), (4 + 12, sigmaPoly [[5, 7]])],
        cOneConst]) (fun l hl => ?_), show polySubstSeq [[(10, [[4], [5, 17], [7, 9]]),
      (10 + 12, sigmaPoly [[4], [5, 17], [7, 9]])], [(4, [[5, 7]]), (4 + 12, sigmaPoly [[5, 7]])],
        cOneConst] (sqCoords.getD 20 []) = polyMul [[7], [17]] [[5, 5], [19]] by decide +kernel,
      polyEval_polyMul] at h44
    · simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero, mul_eq_zero] at h44
      have hh : h = largeReeSigma m f := by
        rcases h44 with h44 | h44
        · exact eq_of_add_eq_zero_two h44
        · apply largeReeSigma_injective hK
          rw [largeReeSigma_sigma hK, ← eq_of_add_eq_zero_two h44, sq]
      refine ⟨hb, hd, hh, by rw [he, hh], ?_⟩
      rw [hk, he, hh]
      linear_combination (f * largeReeSigma m f) * (CharTwo.two_eq_zero : (2 : K) = 0)
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
        simp only [polyEval, monoEval, coordVal, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
        rw [hk]
        ring
      · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
        simp only [polyEval, monoEval, coordVal, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
        rw [he]
      · exact hL
  · rintro ⟨hb, hd, hh, he, hk⟩
    refine (sylowV_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _ _ _).2 fun n =>
      polyEval_eq_zero_of_polySubstSeq (fun l hl => ?_) (cOneSubsts_check n)
    simp only [cOneSubsts, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
      simp only [cOneK, polyEval, monoEval, coordVal, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
      rw [hk]
      ring
    · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
      simp only [cOneE, polyEval, monoEval, coordVal, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
      rw [he]
    · refine forall_mem_sigmaPair hK _ _ _ _ _ _ _ _ _ _ _ _ (by norm_num) (by decide +kernel) ?_
      simp only [cOneH, polyEval, monoEval, coordVal, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero]
      rw [hh]
    · simp [cOneConst, polyEval, monoEval, coordVal, hb, hd, largeReeSigma_zero,
        largeReeSigma_one]

omit [Finite K] in
theorem sylowV_zero_zero_sq_eq_one_iff
    (b d e f g h i j k l : K) :
    sylowV m K 0 b 0 d e f g h i j k l ^ 2 = 1 ↔ b = 0 ∧ d = 0 ∧ f = 0 ∧ h = 0 ∧ e * j = 0 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  constructor
  · intro hv
    have hb := sq_eq_one_b hv
    have hd := sq_eq_one_d hv
    have hc := (sylowV_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _ _ _).1 hv
    set x := coordVal m (0 : K) b 0 d e f g h i j k l with hx
    have hL : ∀ e ∈ ([(0, []), (12, []), (1, []), (13, []), (2, []), (14, []), (3, []),
        (15, [])] : List (ℕ × Poly)), polyEval x e.2 = x e.1 := by
      simp [polyEval, hx, coordVal, hb, hd, largeReeSigma_zero]
    have h41 : polyEval x (sqCoords.getD 17 []) = 0 := hc 17
    have h43 : polyEval x (sqCoords.getD 19 []) = 0 := hc 19
    have h44 : polyEval x (sqCoords.getD 20 []) = 0 := hc 20
    rw [polyEval_eq_of_polySubst hL (q := [[5, 7]]) (by decide +kernel)] at h41
    rw [polyEval_eq_of_polySubst hL (q := [[5, 17], [7, 9]]) (by decide +kernel)] at h43
    rw [polyEval_eq_of_polySubst hL (q := [[4, 9], [5, 10], [7, 19]]) (by decide +kernel)] at h44
    simp only [polyEval, monoEval, hx, coordVal, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, List.sum_cons, List.sum_nil, mul_one, add_zero] at h41 h43 h44
    have hfh : f = 0 ∧ h = 0 := by
      by_cases hh : h = 0
      · refine ⟨?_, hh⟩
        rw [hh, zero_mul, add_zero] at h43
        rcases mul_eq_zero.1 h43 with h' | h'
        · exact h'
        · exact (largeReeSigma_eq_zero_iff f).1 h'
      · have hf : f = 0 := (mul_eq_zero.1 h41).resolve_right hh
        rw [hf, zero_mul, zero_add] at h43
        have hj : j = 0 := (mul_eq_zero.1 h43).resolve_left hh
        rw [hf, hj, mul_zero, zero_mul, zero_add, zero_add] at h44
        rcases mul_eq_zero.1 h44 with h' | h'
        · exact absurd h' hh
        · exact absurd ((largeReeSigma_eq_zero_iff h).1 h') hh
    obtain ⟨hf, hh⟩ := hfh
    rw [hf, hh, zero_mul, zero_mul, add_zero, add_zero] at h44
    exact ⟨hb, hd, hf, hh, h44⟩
  · rintro ⟨hb, hd, hf, hh, hej⟩
    refine (sylowV_sq_eq_one_iff _ _ _ _ _ _ _ _ _ _ _ _).2 fun n => ?_
    set x := coordVal m (0 : K) b 0 d e f g h i j k l with hx
    have hL : ∀ e ∈ cZeroConst, polyEval x e.2 = x e.1 := by
      simp [cZeroConst, polyEval, hx, coordVal, hb, hd, hf, hh, largeReeSigma_zero]
    have hmap : (sqCoords.map (polySubst (substOf cZeroConst))).getD n
        (polySubst (substOf cZeroConst) []) =
          polySubst (substOf cZeroConst) (sqCoords.getD n []) :=
      List.getD_map _ _ _
    rw [polyEval_eq_of_polySubst hL rfl, ← hmap, cZero_check]
    have hσej : largeReeSigma m e * largeReeSigma m j = 0 := by
      rw [← largeReeSigma_mul, hej, largeReeSigma_zero]
    fin_cases n <;> simp [polyEval, monoEval, hx, coordVal, hej, hσej]

end Square

end CFSG.LieType.Ree.LargeReeInvolution
