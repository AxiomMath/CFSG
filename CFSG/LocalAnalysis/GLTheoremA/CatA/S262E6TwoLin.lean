module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6TwoSL6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262.E6TwoLin

open scoped MatrixGroups commutatorElement
open CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

variable {K : Type} [Field K] [CharP K 2]

theorem tvSLWord_eq_of_mask {w w' : List (Fin 6 × Fin 6)}
    (h : wordMask w = wordMask w') :
    tvSLWord (K := K) w = tvSLWord (K := K) w' := by
  apply Subtype.ext
  rw [coe_tvSLWord, coe_tvSLWord, ← real_wordMask (R := K) w,
    ← real_wordMask (R := K) w', h]

theorem tvSLWord_comm_of_mask {w w' : List (Fin 6 × Fin 6)}
    (h : mmul (wordMask w) (wordMask w') = mmul (wordMask w') (wordMask w)) :
    (tvSLWord (K := K) w) * tvSLWord w' = tvSLWord w' * tvSLWord w := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSLWord,
    ← real_wordMask (R := K) w, ← real_wordMask (R := K) w',
    ← real_mmul (A := wordMask w) (B := wordMask w') (length_wordMask w'),
    ← real_mmul (A := wordMask w') (B := wordMask w) (length_wordMask w), h]

@[expose] def wordElt {G : Type*} [Group G] (x y : G) : List Bool → G
  | [] => 1
  | true :: w => x * wordElt x y w
  | false :: w => y * wordElt x y w

theorem wordElt_append {G : Type*} [Group G] (x y : G) :
    ∀ u v : List Bool, wordElt x y (u ++ v) = wordElt x y u * wordElt x y v
  | [], v => by simp [wordElt]
  | b :: u, v => by
      cases b <;>
        simp only [List.cons_append, wordElt, wordElt_append x y u v, mul_assoc]

@[expose] def invWord : List Bool → List Bool
  | [] => []
  | true :: w => invWord w ++ [true]
  | false :: w => invWord w ++ [false, false]

theorem wordElt_invWord {G : Type*} [Group G] {x y : G}
    (hx2 : x ^ 2 = 1) (hy3 : y ^ 3 = 1) :
    ∀ w : List Bool, wordElt x y (invWord w) = (wordElt x y w)⁻¹
  | [] => by simp [wordElt, invWord]
  | true :: w => by
      have hxinv : x⁻¹ = x := by
        rw [pow_two] at hx2
        have h : x⁻¹ * (x * x) = x := by group
        rwa [hx2, mul_one] at h
      simp only [invWord, wordElt_append, wordElt_invWord hx2 hy3 w, wordElt,
        mul_one, mul_inv_rev, hxinv]
  | false :: w => by
      have hy2 : y ^ 2 = y⁻¹ := by
        have h : y ^ 2 * y = 1 := by
          rw [← pow_succ]
          simpa using hy3
        calc y ^ 2 = y ^ 2 * (y * y⁻¹) := by group
          _ = (y ^ 2 * y) * y⁻¹ := by group
          _ = y⁻¹ := by rw [h]; group
      simp only [invWord, wordElt_append, wordElt_invWord hx2 hy3 w, wordElt,
        mul_one, mul_inv_rev, ← pow_two, hy2]

theorem perfect_closure_of_word_identities {G : Type*} [Group G] {x y : G}
    (hx2 : x ^ 2 = 1) (hy3 : y ^ 3 = 1) {wa wb wc wd : List Bool}
    (hx : wordElt x y [true] =
      wordElt x y (wa ++ wb ++ invWord wa ++ invWord wb))
    (hy : wordElt x y [false] =
      wordElt x y (wc ++ wd ++ invWord wc ++ invWord wd)) :
    ⁅(Subgroup.closure ({x, y} : Set G)), (Subgroup.closure ({x, y} : Set G))⁆ =
      Subgroup.closure ({x, y} : Set G) := by
  set S := Subgroup.closure ({x, y} : Set G) with hS
  have hxS : x ∈ S := Subgroup.subset_closure (by simp)
  have hyS : y ∈ S := Subgroup.subset_closure (by simp)
  have hmem : ∀ w : List Bool, wordElt x y w ∈ S := by
    intro w
    induction w with
    | nil => simp [wordElt]
    | cons b w ih =>
        cases b with
        | true => exact S.mul_mem hxS ih
        | false => exact S.mul_mem hyS ih
  have hxcomm : x = ⁅wordElt x y wa, wordElt x y wb⁆ := by
    rw [commutatorElement_def, ← wordElt_invWord hx2 hy3 wa,
      ← wordElt_invWord hx2 hy3 wb, ← wordElt_append, ← wordElt_append,
      ← wordElt_append]
    rw [← hx]
    simp [wordElt]
  have hycomm : y = ⁅wordElt x y wc, wordElt x y wd⁆ := by
    rw [commutatorElement_def, ← wordElt_invWord hx2 hy3 wc,
      ← wordElt_invWord hx2 hy3 wd, ← wordElt_append, ← wordElt_append,
      ← wordElt_append]
    rw [← hy]
    simp [wordElt]
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    have h1 : a * b ∈ S := S.mul_mem ha hb
    have h2 : a⁻¹ * b⁻¹ ∈ S := S.mul_mem (S.inv_mem ha) (S.inv_mem hb)
    rw [commutatorElement_def]
    simpa [mul_assoc] using S.mul_mem h1 h2
  · refine (Subgroup.closure_le ⁅S, S⁆).mpr ?_
    intro g hg
    rcases (by simpa using hg : g = x ∨ g = y) with rfl | rfl
    · rw [hxcomm]
      exact Subgroup.commutator_mem_commutator (hmem wa) (hmem wb)
    · rw [hycomm]
      exact Subgroup.commutator_mem_commutator (hmem wc) (hmem wd)

@[expose] def expand (wx wy : List (Fin 6 × Fin 6)) :
    List Bool → List (Fin 6 × Fin 6)
  | [] => []
  | true :: w => wx ++ expand wx wy w
  | false :: w => wy ++ expand wx wy w

theorem tvSLWord_expand (wx wy : List (Fin 6 × Fin 6)) (w : List Bool) :
    tvSLWord (K := K) (expand wx wy w) =
      wordElt (tvSLWord (K := K) wx) (tvSLWord (K := K) wy) w := by
  induction w with
  | nil => simp [expand, wordElt, tvSLWord]
  | cons b w ih =>
      cases b with
      | true => simp [expand, wordElt, tvSLWord_append, ih]
      | false => simp [expand, wordElt, tvSLWord_append, ih]

@[expose] def wX1 : List (Fin 6 × Fin 6) :=
  [(0, 4), (4, 0), (0, 4), (2, 1), (1, 2), (2, 1)]

@[expose] def wY1 : List (Fin 6 × Fin 6) :=
  [(4, 0), (1, 2)] ++ [(0, 2), (2, 0), (4, 1), (1, 4), (4, 1), (1, 4)]

@[expose] def wX2 : List (Fin 6 × Fin 6) :=
  [(0, 3), (3, 0), (0, 3), (2, 5), (5, 2), (2, 5)]

@[expose] def wY2 : List (Fin 6 × Fin 6) :=
  [(3, 0), (5, 2)] ++ [(0, 2), (2, 0), (3, 5), (5, 3), (3, 5), (5, 3)]

@[expose] def wa : List Bool := [false, false]

@[expose] def wb : List Bool :=
  [true, false, true, false, false, true, false, true, false, false, true]

@[expose] def wc : List Bool := [false, true, false, true, false, false]

@[expose] def wd : List Bool := [true, false, false, true, false, true, false]

theorem mask_x1 :
    wordMask (expand wX1 wY1 [true]) =
      wordMask (expand wX1 wY1 (wc ++ wd ++ invWord wc ++ invWord wd)) := by
  decide +kernel

theorem mask_y1 :
    wordMask (expand wX1 wY1 [false]) =
      wordMask (expand wX1 wY1 (wa ++ wb ++ invWord wa ++ invWord wb)) := by
  decide +kernel

theorem mask_x2 :
    wordMask (expand wX2 wY2 [true]) =
      wordMask (expand wX2 wY2 (wc ++ wd ++ invWord wc ++ invWord wd)) := by
  decide +kernel

theorem mask_y2 :
    wordMask (expand wX2 wY2 [false]) =
      wordMask (expand wX2 wY2 (wa ++ wb ++ invWord wa ++ invWord wb)) := by
  decide +kernel

theorem tvSLWord_wX1_pow_two : (tvSLWord (K := K) wX1) ^ 2 = 1 := by
  rw [pow_two, ← tvSLWord_append]
  simpa [tvSLWord] using
    tvSLWord_eq_of_mask (K := K) (w := wX1 ++ wX1) (w' := []) (by decide +kernel)

theorem tvSLWord_wY1_pow_three : (tvSLWord (K := K) wY1) ^ 3 = 1 := by
  rw [show (tvSLWord (K := K) wY1) ^ 3 =
      tvSLWord (K := K) (wY1 ++ wY1 ++ wY1) by
    rw [pow_succ, pow_two, tvSLWord_append, tvSLWord_append]]
  simpa [tvSLWord] using
    tvSLWord_eq_of_mask (K := K) (w := wY1 ++ wY1 ++ wY1) (w' := [])
      (by decide +kernel)

theorem tvSLWord_wX2_pow_two : (tvSLWord (K := K) wX2) ^ 2 = 1 := by
  rw [pow_two, ← tvSLWord_append]
  simpa [tvSLWord] using
    tvSLWord_eq_of_mask (K := K) (w := wX2 ++ wX2) (w' := []) (by decide +kernel)

theorem tvSLWord_wY2_pow_three : (tvSLWord (K := K) wY2) ^ 3 = 1 := by
  rw [show (tvSLWord (K := K) wY2) ^ 3 =
      tvSLWord (K := K) (wY2 ++ wY2 ++ wY2) by
    rw [pow_succ, pow_two, tvSLWord_append, tvSLWord_append]]
  simpa [tvSLWord] using
    tvSLWord_eq_of_mask (K := K) (w := wY2 ++ wY2 ++ wY2) (w' := [])
      (by decide +kernel)

theorem tvSLWord_ne_one_of_tvMatWord_ne_one {w : List (Fin 6 × Fin 6)}
    (h : tvMatWord (R := ZMod 2) w ≠ 1) : tvSLWord (K := K) w ≠ 1 := by
  intro h1
  apply h
  have hmat : (tvMatWord (R := K) w) = 1 := by
    simpa [coe_tvSLWord] using
      congrArg (fun x : SL(6, K) => (x : Matrix (Fin 6) (Fin 6) K)) h1
  rw [tvMatWord_eq_map] at hmat
  have hmap1 : (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)).map
      (ZMod.castHom (dvd_refl 2) K) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [← hmap1] at hmat
  ext i j
  have e := congrArg (fun M : Matrix (Fin 6) (Fin 6) K => M i j) hmat
  exact (ZMod.castHom (dvd_refl 2) K).injective
    (by simpa only [Matrix.map_apply] using e)

theorem tvSLWord_wY1_ne_one : tvSLWord (K := K) wY1 ≠ 1 := by
  apply tvSLWord_ne_one_of_tvMatWord_ne_one
  decide +kernel

theorem tvSLWord_wY2_ne_one : tvSLWord (K := K) wY2 ≠ 1 := by
  apply tvSLWord_ne_one_of_tvMatWord_ne_one
  decide +kernel

@[expose] noncomputable def x1 : SL(6, K) := tvSLWord (K := K) wX1

@[expose] noncomputable def y1 : SL(6, K) := tvSLWord (K := K) wY1

@[expose] noncomputable def S1 : Subgroup (SL(6, K)) :=
  Subgroup.closure ({x1, y1} : Set (SL(6, K)))

@[expose] noncomputable def x2 : SL(6, K) := tvSLWord (K := K) wX2

@[expose] noncomputable def y2 : SL(6, K) := tvSLWord (K := K) wY2

@[expose] noncomputable def S2 : Subgroup (SL(6, K)) :=
  Subgroup.closure ({x2, y2} : Set (SL(6, K)))

theorem commutator_S1 : ⁅(S1 (K := K)), (S1 (K := K))⁆ = (S1 (K := K)) := by
  change ⁅(Subgroup.closure ({tvSLWord (K := K) wX1, tvSLWord (K := K) wY1} :
      Set (SL(6, K)))), (Subgroup.closure ({tvSLWord (K := K) wX1,
      tvSLWord (K := K) wY1} : Set (SL(6, K))))⁆ =
    Subgroup.closure ({tvSLWord (K := K) wX1, tvSLWord (K := K) wY1} :
      Set (SL(6, K)))
  refine perfect_closure_of_word_identities (wa := wc) (wb := wd) (wc := wa)
    (wd := wb) tvSLWord_wX1_pow_two tvSLWord_wY1_pow_three ?_ ?_
  · rw [← tvSLWord_expand (K := K) (wx := wX1) (wy := wY1) (w := [true]),
      ← tvSLWord_expand (K := K) (wx := wX1) (wy := wY1)
        (w := wc ++ wd ++ invWord wc ++ invWord wd)]
    exact tvSLWord_eq_of_mask mask_x1
  · rw [← tvSLWord_expand (K := K) (wx := wX1) (wy := wY1) (w := [false]),
      ← tvSLWord_expand (K := K) (wx := wX1) (wy := wY1)
        (w := wa ++ wb ++ invWord wa ++ invWord wb)]
    exact tvSLWord_eq_of_mask mask_y1

theorem commutator_S2 : ⁅(S2 (K := K)), (S2 (K := K))⁆ = (S2 (K := K)) := by
  change ⁅(Subgroup.closure ({tvSLWord (K := K) wX2, tvSLWord (K := K) wY2} :
      Set (SL(6, K)))), (Subgroup.closure ({tvSLWord (K := K) wX2,
      tvSLWord (K := K) wY2} : Set (SL(6, K))))⁆ =
    Subgroup.closure ({tvSLWord (K := K) wX2, tvSLWord (K := K) wY2} :
      Set (SL(6, K)))
  refine perfect_closure_of_word_identities (wa := wc) (wb := wd) (wc := wa)
    (wd := wb) tvSLWord_wX2_pow_two tvSLWord_wY2_pow_three ?_ ?_
  · rw [← tvSLWord_expand (K := K) (wx := wX2) (wy := wY2) (w := [true]),
      ← tvSLWord_expand (K := K) (wx := wX2) (wy := wY2)
        (w := wc ++ wd ++ invWord wc ++ invWord wd)]
    exact tvSLWord_eq_of_mask mask_x2
  · rw [← tvSLWord_expand (K := K) (wx := wX2) (wy := wY2) (w := [false]),
      ← tvSLWord_expand (K := K) (wx := wX2) (wy := wY2)
        (w := wa ++ wb ++ invWord wa ++ invWord wb)]
    exact tvSLWord_eq_of_mask mask_y2

theorem le_centralizer_e2e3 :
    S1 ≤ Subgroup.centralizer ({zSL ![0, 1, 1]} : Set (SL(6, K))) := by
  change Subgroup.closure ({x1, y1} : Set (SL(6, K))) ≤
    Subgroup.centralizer ({zSL ![0, 1, 1]} : Set (SL(6, K)))
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  have hz : zSL ![0, 1, 1] = tvSLWord (K := K) (zword ![0, 1, 1]) := rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hz]
    exact tvSLWord_comm_of_mask (K := K) (by decide +kernel)
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hz]
    exact tvSLWord_comm_of_mask (K := K) (by decide +kernel)

theorem le_centralizer_e3 :
    S2 ≤ Subgroup.centralizer ({zSL ![0, 0, 1]} : Set (SL(6, K))) := by
  change Subgroup.closure ({x2, y2} : Set (SL(6, K))) ≤
    Subgroup.centralizer ({zSL ![0, 0, 1]} : Set (SL(6, K)))
  refine (Subgroup.closure_le _).mpr ?_
  intro g hg
  have hz : zSL ![0, 0, 1] = tvSLWord (K := K) (zword ![0, 0, 1]) := rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hz]
    exact tvSLWord_comm_of_mask (K := K) (by decide +kernel)
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, hz]
    exact tvSLWord_comm_of_mask (K := K) (by decide +kernel)

theorem exists_perfect_centralizing_e3 :
    ∃ S : Subgroup (SL(6, K)),
      S ≤ Subgroup.centralizer ({zSL ![0, 0, 1]} : Set (SL(6, K))) ∧
      ⁅S, S⁆ = S ∧ 3 ∣ Nat.card S := by
  refine ⟨S2, le_centralizer_e3, commutator_S2, ?_⟩
  have hy2S : y2 (K := K) ∈ S2 (K := K) := Subgroup.subset_closure (by simp)
  have hord : orderOf (⟨y2, hy2S⟩ : S2 (K := K)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime tvSLWord_wY2_pow_three tvSLWord_wY2_ne_one
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem exists_perfect_centralizing_e2e3 :
    ∃ S : Subgroup (SL(6, K)),
      S ≤ Subgroup.centralizer ({zSL ![0, 1, 1]} : Set (SL(6, K))) ∧
      ⁅S, S⁆ = S ∧ 3 ∣ Nat.card S := by
  refine ⟨S1, le_centralizer_e2e3, commutator_S1, ?_⟩
  have hy1S : y1 (K := K) ∈ S1 (K := K) := Subgroup.subset_closure (by simp)
  have hord : orderOf (⟨y1, hy1S⟩ : S1 (K := K)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime tvSLWord_wY1_pow_three tvSLWord_wY1_ne_one
  rw [← hord]
  exact orderOf_dvd_natCard _

end CFSG.LocalAnalysis.GLTheoremA.S262.E6TwoLin

end
