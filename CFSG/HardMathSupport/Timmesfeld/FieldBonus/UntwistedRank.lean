module

public import CFSG.LieType.Chevalley.CharTwoRank
public import CFSG.LieType.Steinberg.G2.RankOne

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus.Untw

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section SL2

variable {K : Type} [Field K]

theorem coe_sl2_c :
    ((sl2Upper (-1 : K) * sl2Lower (1 : K) * sl2Upper (-2 : K) :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper,
    coe_sl2Lower, coe_sl2Upper]
  simp only [Matrix.mul_fin_two]
  congr 1; ring_nf

theorem sl2_c_pow_three :
    (sl2Upper (-1 : K) * sl2Lower (1 : K) * sl2Upper (-2 : K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2_c, pow_succ, pow_succ, pow_one]
  simp only [Matrix.mul_fin_two]
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  congr 1; ring_nf

theorem sl2_c_not_commute :
    ¬ Commute (sl2Upper (-1 : K) * sl2Lower (1 : K) * sl2Upper (-2 : K)) (sl2Upper (1 : K)) := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul] at this
  change ((!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1] * !![1, 1; 0, 1] :
      Matrix (Fin 2) (Fin 2) K) 0 0) =
    ((!![1, 1; 0, 1] * (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1]) :
      Matrix (Fin 2) (Fin 2) K) 0 0) at this
  simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at this
  ring_nf at this
  simp at this

theorem sl2_c_sq_not_commute :
    ¬ Commute ((sl2Upper (-1 : K) * sl2Lower (1 : K) * sl2Upper (-2 : K)) ^ 2)
      (sl2Upper (1 : K)) := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 1 1) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, pow_two] at this
  change ((!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1] *
      (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1]) * !![1, 1; 0, 1] :
      Matrix (Fin 2) (Fin 2) K) 1 1) =
    ((!![1, 1; 0, 1] * (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1] *
      (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1])) :
      Matrix (Fin 2) (Fin 2) K) 1 1) at this
  simp only [Matrix.mul_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at this
  ring_nf at this
  simp at this

end SL2

section RankOne

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def rankOneC
    (i : Fin τ.rank) : adjointGroup τ K :=
  (rootOperatorFamily τ).eltElement (simpleRoot τ i) (-1) *
    (rootOperatorFamily τ).eltElement (-simpleRoot τ i) 1 *
    (rootOperatorFamily τ).eltElement (simpleRoot τ i) (-2)

theorem rankOneC_facts
    {i : Fin τ.rank}
    (hφ : ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = (rootOperatorFamily τ).eltElement (simpleRoot τ i) c) ∧
        ∀ c, φ (sl2Lower c) = (rootOperatorFamily τ).eltElement (-simpleRoot τ i) c) :
    rankOneC (K := K) i ^ 3 = 1 ∧
      ¬ Commute (rankOneC (K := K) i) ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1) ∧
      ¬ Commute (rankOneC (K := K) i ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1) := by
  obtain ⟨φ, hφ, hu, hl⟩ := hφ
  have hc : rankOneC (K := K) i = φ (sl2Upper (-1) * sl2Lower 1 * sl2Upper (-2)) := by
    rw [map_mul, map_mul, hu, hl, hu]
    rfl
  rw [hc, ← hu]
  refine ⟨by rw [← map_pow, sl2_c_pow_three, map_one], fun h => ?_, fun h => ?_⟩
  · exact sl2_c_not_commute (by
      have := h.eq
      rw [← map_mul, ← map_mul] at this
      exact hφ this)
  · exact sl2_c_sq_not_commute (by
      have := h.eq
      rw [← map_pow, ← map_mul, ← map_mul] at this
      exact hφ this)

end RankOne

section Witness

variable {τ : Tag} {n : ℕ}

variable (W : RootWitness τ n) in
@[expose] noncomputable def elemC
    (K : Type) [Field K] (i : Fin n) : adjointGroup τ K :=
  nrep τ K ((coxeterSystem τ).wordProd (W.word i)) * rankOneC (W.simple i) *
    (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹

variable (W : RootWitness τ n) in
theorem conj_x_mem
    (K : Type) [Field K] (i : Fin n) (c : K) :
    nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
        (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) c *
        (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹ ∈
      (rootOperatorFamily τ).rootSubgroup K (W.root i) := by
  rw [W.root_eq_smul i]
  exact nrep_conj_mem_X _ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)

variable (W : RootWitness τ n) in
theorem conj_y_mem
    (K : Type) [Field K] (i : Fin n) (c : K) :
    nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
        (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) c *
        (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹ ∈
      (rootOperatorFamily τ).rootSubgroup K (-W.root i) := by
  have := nrep_conj_mem_X (K := K) ((coxeterSystem τ).wordProd (W.word i))
    ((rootOperatorFamily τ).eltElement_mem_rootSubgroup (-simpleRoot τ (W.simple i)) c)
  rwa [smul_neg_root, ← W.root_eq_smul i] at this

variable (W : RootWitness τ n) in
theorem elemC_eq
    (K : Type) [Field K] (i : Fin n) :
    elemC W K i =
      nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
          (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) (-1) *
          (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹ *
        (nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
          (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) 1 *
          (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹) *
        (nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
          (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) (-2) *
          (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹) := by
  simp only [elemC, rankOneC]
  group

variable {W : RootWitness τ n}

theorem facts_of_rankOne
    (hW : W.check = true) (hO : W.orthoCheck = true) {K : Type} [Field K]
    (hrk : ∀ i, rankOneC (K := K) (W.simple i) ^ 3 = 1 ∧
      ¬ Commute (rankOneC (K := K) (W.simple i))
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1) ∧
      ¬ Commute (rankOneC (K := K) (W.simple i) ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1)) :
    (∀ i, elemC W K i ^ 3 = 1 ∧ ¬ Commute (elemC W K i) (W.elemA K i) ∧
      ¬ Commute (elemC W K i ^ 2) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (elemC W K j) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (elemC W K i) (elemC W K j)) := by
  simp only [RootWitness.check, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hW
  simp only [RootWitness.orthoCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hO
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => by
    rw [RootWitness.root_val]; exact (hW i).1.1.1
  have hnn : ∀ i k, 0 ≤ (W.root i).1 k := fun i k => by
    rw [RootWitness.root_val]; exact (hW i).1.1.2 k
  have hne0 : ∀ i, (W.root i).1 ≠ 0 := fun i h => by
    have := hpos i
    rw [h] at this
    simp [height] at this
  set s : Fin n → WeylGroup τ := fun i => (coxeterSystem τ).wordProd (W.sepWord i)
  have hact : ∀ i j, (s i) • (W.root j).1 = (W.sepWord i).foldr (reflect τ) (W.vec j) :=
    fun i j => by rw [RootWitness.root_val, wordProd_smul]
  have hfix : ∀ i j, i ≠ j → s i • W.root j = W.root j := fun i j hij => Subtype.ext (by
    rw [coe_smul_root, hact, RootWitness.root_val]
    rcases (hO i).2 j with h | h
    · exact absurd h hij
    · exact h)
  have hflip : ∀ i, s i • W.root i = -W.root i := fun i => Subtype.ext (by
    rw [coe_smul_root, hact, coe_neg_root, RootWitness.root_val]
    exact (hO i).1)
  have hroot_ne : ∀ i j, i ≠ j → W.root i ≠ W.root j := fun i j hij h => by
    have h1 := hflip i
    rw [h, hfix i j hij] at h1
    have h3 := congrArg (fun r : Root τ => height r.1) h1
    simp only [coe_neg_root, height_neg] at h3
    have := hpos j
    omega
  have hXX : ∀ i j, i ≠ j → ∀ x ∈ (rootOperatorFamily τ).rootSubgroup K (W.root i),
      ∀ y ∈ (rootOperatorFamily τ).rootSubgroup K (W.root j), Commute x y := by
    intro i j hij x hx y hy
    obtain ⟨c, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hx
    obtain ⟨d, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hy
    have hpf : pairFree τ (W.root i).1 (W.root j).1 = true := by
      rw [RootWitness.root_val, RootWitness.root_val]
      rcases (hW i).2 j with h | h
      · exact absurd h hij
      · exact h.1
    exact commute_rootHom_of_not_isRoot (hpos i) (hpos j) (hroot_ne i j hij)
      (fun a b ha hb => not_isRoot_of_pairFree (hnn i) (hne0 i) (hnn j) (hne0 j) hpf ha hb)
      (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)
  have hXX' : ∀ i j, i ≠ j → ∀ (εi εj : Bool),
      ∀ x ∈ (rootOperatorFamily τ).rootSubgroup K (if εi then W.root i else -W.root i),
      ∀ y ∈ (rootOperatorFamily τ).rootSubgroup K (if εj then W.root j else -W.root j),
      Commute x y := by
    intro i j hij εi εj x hx y hy
    cases εi <;> cases εj <;> simp only [Bool.false_eq_true, ↓reduceIte] at hx hy
    · refine commute_X_of_smul (s i * s j) ?_ ?_ (hXX i j hij) hx hy
      · rw [mul_smul, smul_neg_root, hfix j i (Ne.symm hij), smul_neg_root, hflip, neg_neg]
      · rw [mul_smul, smul_neg_root, hflip, neg_neg, hfix i j hij]
    · refine commute_X_of_smul (s i) ?_ ?_ (hXX i j hij) hx hy
      · rw [smul_neg_root, hflip, neg_neg]
      · exact hfix i j hij
    · refine commute_X_of_smul (s j) ?_ ?_ (hXX i j hij) hx hy
      · exact hfix j i (Ne.symm hij)
      · rw [smul_neg_root, hflip, neg_neg]
    · exact hXX i j hij x hx y hy
  have hA := W.elemA_mem K
  have hx : ∀ i c, nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
      (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) c *
      (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹ ∈
        (rootOperatorFamily τ).rootSubgroup K (if true then W.root i else -W.root i) :=
    fun i c => by simpa using conj_x_mem W K i c
  have hy : ∀ i c, nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
      (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) c *
      (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹ ∈
        (rootOperatorFamily τ).rootSubgroup K (if false then W.root i else -W.root i) :=
    fun i c => by simpa using conj_y_mem W K i c
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · set nn := nrep τ K ((coxeterSystem τ).wordProd (W.word i))
    obtain ⟨h3, h1, h2'⟩ := hrk i
    have hconj : ∀ (g : adjointGroup τ K) (m : ℕ), (nn * g * nn⁻¹) ^ m = nn * g ^ m * nn⁻¹ :=
      fun g m => by
        induction m with
        | zero => simp
        | succ m ih => rw [pow_succ, ih, pow_succ]; group
    have hcomm : ∀ g h : adjointGroup τ K, Commute (nn * g * nn⁻¹) (nn * h * nn⁻¹) →
        Commute g h := fun g h hc => by
      have e := hc.eq
      have : nn * (g * h) * nn⁻¹ = nn * (h * g) * nn⁻¹ := by
        calc _ = nn * g * nn⁻¹ * (nn * h * nn⁻¹) := by group
          _ = nn * h * nn⁻¹ * (nn * g * nn⁻¹) := e
          _ = _ := by group
      exact mul_right_cancel (mul_left_cancel this)
    refine ⟨?_, fun hc => h1 (hcomm _ _ hc), fun hc => h2' (hcomm _ _ ?_)⟩
    · change (nn * rankOneC (W.simple i) * nn⁻¹) ^ 3 = 1
      rw [hconj, h3, mul_one, mul_inv_cancel]
    · change Commute ((nn * rankOneC (W.simple i) * nn⁻¹) ^ 2) _ at hc
      rw [← hconj]; exact hc
  · have hAi : W.elemA K i ∈ (rootOperatorFamily τ).rootSubgroup K
        (if true then W.root i else -W.root i) := by simpa using hA i
    rw [elemC_eq]
    exact ((hXX' j i (Ne.symm hij) true true _ (hx j (-1)) _ hAi).mul_left
      (hXX' j i (Ne.symm hij) false true _ (hy j 1) _ hAi)).mul_left
      (hXX' j i (Ne.symm hij) true true _ (hx j (-2)) _ hAi)
  · rw [elemC_eq, elemC_eq]
    have key : ∀ (εi : Bool) (a : adjointGroup τ K),
        a ∈ (rootOperatorFamily τ).rootSubgroup K (if εi then W.root i else -W.root i) →
        Commute a (nrep τ K ((coxeterSystem τ).wordProd (W.word j)) *
            (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple j)) (-1) *
            (nrep τ K ((coxeterSystem τ).wordProd (W.word j)))⁻¹ *
          (nrep τ K ((coxeterSystem τ).wordProd (W.word j)) *
            (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple j)) 1 *
            (nrep τ K ((coxeterSystem τ).wordProd (W.word j)))⁻¹) *
          (nrep τ K ((coxeterSystem τ).wordProd (W.word j)) *
            (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple j)) (-2) *
            (nrep τ K ((coxeterSystem τ).wordProd (W.word j)))⁻¹)) := fun εi a ha =>
      ((hXX' i j hij εi true a ha _ (hx j (-1))).mul_right
        (hXX' i j hij εi false a ha _ (hy j 1))).mul_right
        (hXX' i j hij εi true a ha _ (hx j (-2)))
    exact ((key true _ (hx i (-1))).mul_left (key false _ (hy i 1))).mul_left
      (key true _ (hx i (-2)))

theorem le_pRank_three_adjointQuotient_of_rankOne
    (hW : W.check = true) (hO : W.orthoCheck = true) {K : Type} [Field K] [Finite K]
    (hrk : ∀ i, rankOneC (K := K) (W.simple i) ^ 3 = 1 ∧
      ¬ Commute (rankOneC (K := K) (W.simple i))
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1) ∧
      ¬ Commute (rankOneC (K := K) (W.simple i) ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1)) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  obtain ⟨hf, hZA, hZZ⟩ := facts_of_rankOne hW hO hrk
  exact le_pRank_three_center_quotient (elemC W K) (W.elemA K) (fun i => (hf i).1)
    (fun i => (hf i).2.1) (fun i => (hf i).2.2) hZA hZZ

end Witness

@[expose] def witnessG2 : RootWitness .G2 2 where
  word := ![([] : List (Fin 2)), ([1, 0] : List (Fin 2))]
  simple := ![(0 : Fin 2), (1 : Fin 2)]

theorem witnessG2_check : witnessG2.check = true := by decide +kernel

theorem witnessG2_orthoCheck : witnessG2.orthoCheck = true := by decide +kernel

theorem two_le_pRank_three_adjointQuotient
    {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  · exact le_pRank_three_adjointQuotient_of_rankOne witnessG2_check witnessG2_orthoCheck
      fun i => rankOneC_facts (g2_exists_sl2_hom _)
  · have hn : ∀ i, Tag.cartan .F4 (witnessF4.simple i)
        (![(0 : Fin 4), (0 : Fin 4), (0 : Fin 4), (1 : Fin 4)] i) = -1 := by decide
    exact le_trans (by norm_num) (le_pRank_three_adjointQuotient_of_rankOne witnessF4_check
      witnessF4_orthoCheck fun i => rankOneC_facts (exists_sl2_hom _ (hn i)))
  · have hn : ∀ i, Tag.cartan .E6 (witnessE6.simple i)
        (![(1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (2 : Fin 6)] i) = -1 := by decide
    exact le_trans (by norm_num) (le_pRank_three_adjointQuotient_of_rankOne witnessE6_check
      witnessE6_orthoCheck fun i => rankOneC_facts (exists_sl2_hom _ (hn i)))
  · have hn : ∀ i, Tag.cartan .E7 (witnessE7.simple i)
        (![(5 : Fin 7), (3 : Fin 7), (0 : Fin 7), (3 : Fin 7)] i) = -1 := by decide
    exact le_trans (by norm_num) (le_pRank_three_adjointQuotient_of_rankOne witnessE7_check
      witnessE7_orthoCheck fun i => rankOneC_facts (exists_sl2_hom _ (hn i)))
  · have hn : ∀ i, Tag.cartan .E8 (witnessE8.simple i)
        (![(6 : Fin 8), (4 : Fin 8), (1 : Fin 8), (3 : Fin 8)] i) = -1 := by decide
    exact le_trans (by norm_num) (le_pRank_three_adjointQuotient_of_rankOne witnessE8_check
      witnessE8_orthoCheck fun i => rankOneC_facts (exists_sl2_hom _ (hn i)))

end CFSG.HardMathSupport.Timmesfeld.FieldBonus.Untw
