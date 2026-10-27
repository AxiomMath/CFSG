module

public import CFSG.LieType.Chevalley.CharTwoRank
public import CFSG.LieType.Steinberg.G2.RankOne

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section SL2

variable {K : Type} [Field K]

@[expose] def sl2Three : Matrix.SpecialLinearGroup (Fin 2) K :=
  sl2Upper (-1) * sl2Lower 1 * sl2Upper (-2)

theorem coe_sl2Three :
    ((sl2Three : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, -1; 1, -1] := by
  unfold sl2Three
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, -1; 0, 1] * !![1, 0; 1, 1] * !![1, -2; 0, 1] : Matrix (Fin 2) (Fin 2) K) = _
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem sl2Three_pow_three : (sl2Three : Matrix.SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2Three, pow_succ, pow_succ, pow_one]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Three_not_commute :
    ¬ Commute (sl2Three : Matrix.SpecialLinearGroup (Fin 2) K) (sl2Upper (1 : K)) := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 1) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Three] at this
  change ((!![0, -1; 1, -1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 1) =
    ((!![1, 1; 0, 1] * !![0, -1; 1, -1] : Matrix (Fin 2) (Fin 2) K) 0 1) at this
  simp only [Matrix.mul_fin_two] at this
  simp at this

theorem sl2Three_sq_not_commute :
    ¬ Commute ((sl2Three : Matrix.SpecialLinearGroup (Fin 2) K) ^ 2) (sl2Upper (1 : K)) := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    coe_sl2Three] at this
  change ((!![0, -1; 1, -1] ^ 2 * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0) =
    ((!![1, 1; 0, 1] * !![0, -1; 1, -1] ^ 2 : Matrix (Fin 2) (Fin 2) K) 0 0) at this
  simp only [pow_two, Matrix.mul_fin_two] at this
  simp at this

end SL2

set_option linter.unusedSectionVars false


section RankOne

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def rankOneG (i : Fin τ.rank) : adjointGroup τ K :=
  (rootOperatorFamily τ).eltElement (simpleRoot τ i) (-1) *
    (rootOperatorFamily τ).eltElement (-simpleRoot τ i) 1 *
    (rootOperatorFamily τ).eltElement (simpleRoot τ i) (-2)

@[expose] def HasRankOneHom (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) : Prop :=
  ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
    (∀ c, φ (sl2Upper c) = (rootOperatorFamily τ).eltElement (simpleRoot τ i) c) ∧
      ∀ c, φ (sl2Lower c) = (rootOperatorFamily τ).eltElement (-simpleRoot τ i) c

theorem hasRankOneHom_of_cartan {i k : Fin τ.rank} (hk : τ.cartan i k = -1) :
    HasRankOneHom τ K i := exists_sl2_hom (K := K) (rootOperatorFamily τ) hk

theorem rankOneG_facts {i : Fin τ.rank} (h : HasRankOneHom τ K i) :
    rankOneG (K := K) i ^ 3 = 1 ∧
      ¬ Commute (rankOneG (K := K) i) ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1) ∧
      ¬ Commute (rankOneG (K := K) i ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1) := by
  obtain ⟨φ, hφ, hu, hl⟩ := h
  have hz : rankOneG (K := K) i = φ sl2Three := by
    unfold sl2Three rankOneG
    rw [map_mul, map_mul, hu, hl, hu]
  rw [hz, ← hu]
  refine ⟨by rw [← map_pow, sl2Three_pow_three, map_one], fun h => ?_, fun h => ?_⟩
  · exact sl2Three_not_commute (by
      have := h.eq
      rw [← map_mul, ← map_mul] at this
      exact hφ this)
  · exact sl2Three_sq_not_commute (by
      have := h.eq
      rw [← map_pow, ← map_mul, ← map_mul] at this
      exact hφ this)

end RankOne

namespace RootWitness

variable {τ : Tag} {n : ℕ} {W : RootWitness τ n}

variable (W) in
@[expose] noncomputable def elemAc (K : Type) [Field K] (i : Fin n) (c : K) : adjointGroup τ K :=
  nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
    (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) c *
    (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹

variable (W) in
@[expose] noncomputable def elemBc (K : Type) [Field K] (i : Fin n) (c : K) : adjointGroup τ K :=
  nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
    (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) c *
    (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹

variable (W) in
@[expose] noncomputable def elemG (K : Type) [Field K] (i : Fin n) : adjointGroup τ K :=
  W.elemAc K i (-1) * W.elemBc K i 1 * W.elemAc K i (-2)

theorem elemG_eq (K : Type) [Field K] (i : Fin n) :
    W.elemG K i = nrep τ K ((coxeterSystem τ).wordProd (W.word i)) * rankOneG (W.simple i) *
      (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹ := by
  simp only [elemG, elemAc, elemBc, rankOneG]
  group

theorem elemAc_mem (K : Type) [Field K] (i : Fin n) (c : K) :
    W.elemAc K i c ∈ (rootOperatorFamily τ).rootSubgroup K (W.root i) := by
  rw [W.root_eq_smul i]
  exact nrep_conj_mem_X _ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)

theorem elemBc_mem (K : Type) [Field K] (i : Fin n) (c : K) :
    W.elemBc K i c ∈ (rootOperatorFamily τ).rootSubgroup K (-W.root i) := by
  have := nrep_conj_mem_X (K := K) ((coxeterSystem τ).wordProd (W.word i))
    ((rootOperatorFamily τ).eltElement_mem_rootSubgroup (-simpleRoot τ (W.simple i)) c)
  rwa [smul_neg_root, ← W.root_eq_smul i] at this

theorem anyChar_facts
    (hW : W.check = true) (hO : W.orthoCheck = true)
    (K : Type) [Field K] (hsl : ∀ i, HasRankOneHom τ K (W.simple i)) :
    (∀ i, W.elemG K i ^ 3 = 1 ∧ ¬ Commute (W.elemG K i) (W.elemAc K i 1) ∧
      ¬ Commute (W.elemG K i ^ 2) (W.elemAc K i 1)) ∧
    (∀ i j, i ≠ j → Commute (W.elemG K j) (W.elemAc K i 1)) ∧
    (∀ i j, i ≠ j → Commute (W.elemG K i) (W.elemG K j)) := by
  simp only [check, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hW
  simp only [orthoCheck, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq] at hO
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => by rw [root_val]; exact (hW i).1.1.1
  have hnn : ∀ i k, 0 ≤ (W.root i).1 k := fun i k => by rw [root_val]; exact (hW i).1.1.2 k
  have hne0 : ∀ i, (W.root i).1 ≠ 0 := fun i h => by
    have := hpos i
    rw [h] at this
    simp [height] at this
  set s : Fin n → WeylGroup τ := fun i => (coxeterSystem τ).wordProd (W.sepWord i)
  have hact : ∀ i j, (s i) • (W.root j).1 = (W.sepWord i).foldr (reflect τ) (W.vec j) :=
    fun i j => by rw [root_val, wordProd_smul]
  have hfix : ∀ i j, i ≠ j → s i • W.root j = W.root j := fun i j hij => Subtype.ext (by
    rw [coe_smul_root, hact, root_val]
    rcases (hO i).2 j with h | h
    · exact absurd h hij
    · exact h)
  have hflip : ∀ i, s i • W.root i = -W.root i := fun i => Subtype.ext (by
    rw [coe_smul_root, hact, coe_neg_root, root_val]
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
      rw [root_val, root_val]
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
  have hA := W.elemAc_mem K
  have hB := W.elemBc_mem K
  have hG : ∀ i, W.elemG K i = W.elemAc K i (-1) * W.elemBc K i 1 * W.elemAc K i (-2) :=
    fun i => rfl
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · set nn := nrep τ K ((coxeterSystem τ).wordProd (W.word i))
    obtain ⟨h3, h1, h2'⟩ := rankOneG_facts (hsl i)
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
    rw [elemG_eq]
    refine ⟨?_, fun hc => h1 (hcomm _ _ hc), fun hc => h2' (hcomm _ _ ?_)⟩
    · rw [hconj, h3, mul_one, mul_inv_cancel]
    · change Commute ((nn * rankOneG (W.simple i) * nn⁻¹) ^ 2) _ at hc
      rw [← hconj]; exact hc
  · have hAj := hXX' j i (Ne.symm hij) true true _ (by simpa using hA j (-1)) _
      (by simpa using hA i 1)
    have hBj := hXX' j i (Ne.symm hij) false true _ (by simpa using hB j 1) _
      (by simpa using hA i 1)
    have hAj2 := hXX' j i (Ne.symm hij) true true _ (by simpa using hA j (-2)) _
      (by simpa using hA i 1)
    rw [hG]
    exact (hAj.mul_left hBj).mul_left hAj2
  · rw [hG, hG]
    have e : ∀ (εi εj : Bool) (x y : adjointGroup τ K), x ∈ (rootOperatorFamily τ).rootSubgroup K
        (if εi then W.root i else -W.root i) →
        y ∈ (rootOperatorFamily τ).rootSubgroup K (if εj then W.root j else -W.root j) →
        Commute x y := fun εi εj x y hx hy => hXX' i j hij εi εj x hx y hy
    have hAA : ∀ a b : K, Commute (W.elemAc K i a) (W.elemAc K j b) := fun a b =>
      e true true _ _ (by simpa using hA i a) (by simpa using hA j b)
    have hAB : ∀ a b : K, Commute (W.elemAc K i a) (W.elemBc K j b) := fun a b =>
      e true false _ _ (by simpa using hA i a) (by simpa using hB j b)
    have hBA : ∀ a b : K, Commute (W.elemBc K i a) (W.elemAc K j b) := fun a b =>
      e false true _ _ (by simpa using hB i a) (by simpa using hA j b)
    have hBB : ∀ a b : K, Commute (W.elemBc K i a) (W.elemBc K j b) := fun a b =>
      e false false _ _ (by simpa using hB i a) (by simpa using hB j b)
    have h1 : ∀ (a : K) (c : K) (d : K), Commute (W.elemAc K i a)
        (W.elemAc K j c * W.elemBc K j d * W.elemAc K j (-2)) := fun a c d =>
      ((hAA a c).mul_right (hAB a d)).mul_right (hAA a (-2))
    have h2 : ∀ (a : K) (c : K) (d : K), Commute (W.elemBc K i a)
        (W.elemAc K j c * W.elemBc K j d * W.elemAc K j (-2)) := fun a c d =>
      ((hBA a c).mul_right (hBB a d)).mul_right (hBA a (-2))
    exact ((h1 (-1) (-1) 1).mul_left (h2 1 (-1) 1)).mul_left (h1 (-2) (-1) 1)

theorem le_pRank_three_adjointQuotient_any
    (hW : W.check = true) (hO : W.orthoCheck = true)
    {K : Type} [Field K] [Finite K] (hsl : ∀ i, HasRankOneHom τ K (W.simple i)) :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  obtain ⟨hf, hZA, hZZ⟩ := W.anyChar_facts hW hO K hsl
  exact le_pRank_three_center_quotient (W.elemG K) (fun i => W.elemAc K i 1)
    (fun i => (hf i).1) (fun i => (hf i).2.1) (fun i => (hf i).2.2) hZA hZZ

end RootWitness

theorem four_le_pRank_three_adjointQuotient_any {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · have hn : ∀ i, Tag.cartan .F4 (witnessF4.simple i)
        (![(0 : Fin 4), (0 : Fin 4), (0 : Fin 4), (1 : Fin 4)] i) = -1 := by decide
    exact RootWitness.le_pRank_three_adjointQuotient_any witnessF4_check witnessF4_orthoCheck
      (fun i => hasRankOneHom_of_cartan (hn i))
  · have hn : ∀ i, Tag.cartan .E6 (witnessE6.simple i)
        (![(1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (2 : Fin 6)] i) = -1 := by decide
    exact RootWitness.le_pRank_three_adjointQuotient_any witnessE6_check witnessE6_orthoCheck
      (fun i => hasRankOneHom_of_cartan (hn i))
  · have hn : ∀ i, Tag.cartan .E7 (witnessE7.simple i)
        (![(5 : Fin 7), (3 : Fin 7), (0 : Fin 7), (3 : Fin 7)] i) = -1 := by decide
    exact RootWitness.le_pRank_three_adjointQuotient_any witnessE7_check witnessE7_orthoCheck
      (fun i => hasRankOneHom_of_cartan (hn i))
  · have hn : ∀ i, Tag.cartan .E8 (witnessE8.simple i)
        (![(6 : Fin 8), (4 : Fin 8), (1 : Fin 8), (3 : Fin 8)] i) = -1 := by decide
    exact RootWitness.le_pRank_three_adjointQuotient_any witnessE8_check witnessE8_orthoCheck
      (fun i => hasRankOneHom_of_cartan (hn i))

@[expose] def witnessG2 : RootWitness .G2 2 where
  word := ![([] : List (Fin 2)), ([1, 0] : List (Fin 2))]
  simple := ![(0 : Fin 2), (1 : Fin 2)]

theorem witnessG2_check : witnessG2.check = true := by decide +kernel

theorem witnessG2_orthoCheck : witnessG2.orthoCheck = true := by decide +kernel

theorem two_le_pRank_three_adjointQuotient_G2 {K : Type} [Field K] [Finite K] :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient .G2 K)) :=
  RootWitness.le_pRank_three_adjointQuotient_any witnessG2_check witnessG2_orthoCheck
    (fun i => g2_exists_sl2_hom (K := K) (witnessG2.simple i))
