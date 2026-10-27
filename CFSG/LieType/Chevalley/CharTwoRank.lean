module

public import CFSG.LieType.Chevalley.RootWitness
public import CFSG.LieType.Chevalley.TwistRank
public import CFSG.LieType.Steinberg.Adjoint.RankOne
public import CFSG.Blueprint.Catalog
public import CFSG.LocalAnalysis.SectionRank.OrderThreeCenter

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section SL2

variable {K : Type} [Field K]

theorem coe_sl2_ul (h2 : (1 : K) + 1 = 0) :
    ((sl2Upper (1 : K) * sl2Lower (1 : K) : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K) = _
  simp only [Matrix.mul_fin_two]
  simp [h2]

theorem sl2_ul_pow_three (h2 : (1 : K) + 1 = 0) :
    (sl2Upper (1 : K) * sl2Lower (1 : K)) ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl2_ul h2, pow_succ, pow_succ, pow_one]
  simp only [Matrix.mul_fin_two]
  simp only [h2, mul_zero, add_zero, zero_add, mul_one]
  exact Matrix.one_fin_two.symm

theorem sl2_ul_not_commute (h2 : (1 : K) + 1 = 0) :
    ¬ Commute (sl2Upper (1 : K) * sl2Lower (1 : K)) (sl2Upper (1 : K)) := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2_ul h2] at this
  change ((!![0, 1; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0) =
    ((!![1, 1; 0, 1] * !![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K) 0 0) at this
  simp only [Matrix.mul_fin_two] at this
  simp at this

theorem sl2_ul_sq_not_commute (h2 : (1 : K) + 1 = 0) :
    ¬ Commute ((sl2Upper (1 : K) * sl2Lower (1 : K)) ^ 2) (sl2Upper (1 : K)) := by
  intro h
  have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
    (g : Matrix (Fin 2) (Fin 2) K) 0 0) h.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    coe_sl2_ul h2] at this
  change ((!![0, 1; 1, 1] ^ 2 * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K) 0 0) =
    ((!![1, 1; 0, 1] * !![0, 1; 1, 1] ^ 2 : Matrix (Fin 2) (Fin 2) K) 0 0) at this
  simp only [pow_two, Matrix.mul_fin_two] at this
  simp [h2] at this

end SL2

section RankOne

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def rankOneZ
    (i : Fin τ.rank) : adjointGroup τ K :=
  (rootOperatorFamily τ).eltElement (simpleRoot τ i) 1 *
    (rootOperatorFamily τ).eltElement (-simpleRoot τ i) 1

theorem rankOneZ_facts
    {i k : Fin τ.rank} (hk : τ.cartan i k = -1) (h2 : (1 : K) + 1 = 0) :
    rankOneZ (K := K) i ^ 3 = 1 ∧
      ¬ Commute (rankOneZ (K := K) i) ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1) ∧
      ¬ Commute (rankOneZ (K := K) i ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ i) 1) := by
  obtain ⟨φ, hφ, hu, hl⟩ := exists_sl2_hom (K := K) (rootOperatorFamily τ) hk
  have hz : rankOneZ (K := K) i = φ (sl2Upper 1 * sl2Lower 1) := by
    rw [map_mul, hu, hl]
    rfl
  rw [hz, ← hu]
  refine ⟨by rw [← map_pow, sl2_ul_pow_three h2, map_one], fun h => ?_, fun h => ?_⟩
  · exact sl2_ul_not_commute h2 (by
      have := h.eq
      rw [← map_mul, ← map_mul] at this
      exact hφ this)
  · exact sl2_ul_sq_not_commute h2 (by
      have := h.eq
      rw [← map_pow, ← map_mul, ← map_mul] at this
      exact hφ this)

end RankOne

section Conj

variable {τ : Tag} {K : Type} [Field K]

theorem commute_X_of_smul
    {β γ β' γ' : Root τ} (v : WeylGroup τ) (hβ : v • β' = β)
    (hγ : v • γ' = γ)
    (hc : ∀ x ∈ (rootOperatorFamily τ).rootSubgroup K β,
      ∀ y ∈ (rootOperatorFamily τ).rootSubgroup K γ, Commute x y)
    {x y : adjointGroup τ K} (hx : x ∈ (rootOperatorFamily τ).rootSubgroup K β')
    (hy : y ∈ (rootOperatorFamily τ).rootSubgroup K γ') : Commute x y := by
  have h1 := nrep_conj_mem_X v hx
  have h2 := nrep_conj_mem_X v hy
  rw [hβ] at h1
  rw [hγ] at h2
  have h := (hc _ h1 _ h2).eq
  have e : nrep τ K v * (x * y) * (nrep τ K v)⁻¹ = nrep τ K v * (y * x) * (nrep τ K v)⁻¹ := by
    calc _ = nrep τ K v * x * (nrep τ K v)⁻¹ * (nrep τ K v * y * (nrep τ K v)⁻¹) := by group
      _ = nrep τ K v * y * (nrep τ K v)⁻¹ * (nrep τ K v * x * (nrep τ K v)⁻¹) := h
      _ = _ := by group
  exact mul_right_cancel (mul_left_cancel e)

end Conj

namespace RootWitness

variable
    {τ : Tag} {n : ℕ} (W : RootWitness τ n)

@[expose] def orthoCheck : Bool :=
  (List.finRange n).all fun i =>
    decide ((W.sepWord i).foldr (reflect τ) (W.vec i) = -W.vec i) &&
    (List.finRange n).all fun j =>
      decide (i = j) || decide ((W.sepWord i).foldr (reflect τ) (W.vec j) = W.vec j)

theorem root_eq_smul (i : Fin n) :
    W.root i = (coxeterSystem τ).wordProd (W.word i) • simpleRoot τ (W.simple i) :=
  Subtype.ext (by rw [coe_smul_root]; rfl)

variable {W}

variable (W) in
@[expose] noncomputable def elemA
    (K : Type) [Field K] (i : Fin n) : adjointGroup τ K :=
  nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
    (rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1 *
    (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹

variable (W) in
@[expose] noncomputable def elemB
    (K : Type) [Field K] (i : Fin n) : adjointGroup τ K :=
  nrep τ K ((coxeterSystem τ).wordProd (W.word i)) *
    (rootOperatorFamily τ).eltElement (-simpleRoot τ (W.simple i)) 1 *
    (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹

variable (W) in
@[expose] noncomputable def elemZ
    (K : Type) [Field K] (i : Fin n) : adjointGroup τ K :=
  nrep τ K ((coxeterSystem τ).wordProd (W.word i)) * rankOneZ (W.simple i) *
    (nrep τ K ((coxeterSystem τ).wordProd (W.word i)))⁻¹

theorem elemZ_eq
    (K : Type) [Field K] (i : Fin n) : W.elemZ K i = W.elemA K i * W.elemB K i := by
  simp only [elemZ, elemA, elemB, rankOneZ]
  group

theorem elemA_mem
    (K : Type) [Field K] (i : Fin n) :
    W.elemA K i ∈ (rootOperatorFamily τ).rootSubgroup K (W.root i) := by
  rw [W.root_eq_smul i]
  exact nrep_conj_mem_X _ ((rootOperatorFamily τ).eltElement_mem_rootSubgroup _ _)

theorem elemB_mem
    (K : Type) [Field K] (i : Fin n) :
    W.elemB K i ∈ (rootOperatorFamily τ).rootSubgroup K (-W.root i) := by
  have := nrep_conj_mem_X (K := K) ((coxeterSystem τ).wordProd (W.word i))
    ((rootOperatorFamily τ).eltElement_mem_rootSubgroup (-simpleRoot τ (W.simple i)) 1)
  rwa [smul_neg_root, ← W.root_eq_smul i] at this

theorem charTwo_facts
    (hW : W.check = true) (hO : W.orthoCheck = true)
    (nbr : Fin n → Fin τ.rank) (hnbr : ∀ i, τ.cartan (W.simple i) (nbr i) = -1) {K : Type}
    [Field K] [CharP K 2] :
    (∀ i, W.elemZ K i ^ 3 = 1 ∧ ¬ Commute (W.elemZ K i) (W.elemA K i) ∧
      ¬ Commute (W.elemZ K i ^ 2) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K j) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K i) (W.elemZ K j)) := by
  have h2 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
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
  have hA := W.elemA_mem K
  have hB := W.elemB_mem K
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · set nn := nrep τ K ((coxeterSystem τ).wordProd (W.word i))
    obtain ⟨h3, h1, h2'⟩ := rankOneZ_facts (K := K) (hnbr i) h2
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
    · change (nn * rankOneZ (W.simple i) * nn⁻¹) ^ 3 = 1
      rw [hconj, h3, mul_one, mul_inv_cancel]
    · change Commute ((nn * rankOneZ (W.simple i) * nn⁻¹) ^ 2) _ at hc
      rw [← hconj]; exact hc
  · rw [elemZ_eq]
    exact (hXX' j i (Ne.symm hij) true true _ (by simpa using hA j) _
      (by simpa using hA i)).mul_left
      (hXX' j i (Ne.symm hij) false true _ (by simpa using hB j) _ (by simpa using hA i))
  · rw [elemZ_eq, elemZ_eq]
    have hAA := hXX' i j hij true true _ (by simpa using hA i) _ (by simpa using hA j)
    have hAB := hXX' i j hij true false _ (by simpa using hA i) _ (by simpa using hB j)
    have hBA := hXX' i j hij false true _ (by simpa using hB i) _ (by simpa using hA j)
    have hBB := hXX' i j hij false false _ (by simpa using hB i) _ (by simpa using hB j)
    exact (hAA.mul_right hAB).mul_left (hBA.mul_right hBB)

theorem le_pRank_three_adjointQuotient
    (hW : W.check = true) (hO : W.orthoCheck = true)
    (nbr : Fin n → Fin τ.rank) (hnbr : ∀ i, τ.cartan (W.simple i) (nbr i) = -1) {K : Type}
    [Field K] [Finite K] [CharP K 2] :
    n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  obtain ⟨hf, hZA, hZZ⟩ := W.charTwo_facts hW hO nbr hnbr (K := K)
  exact le_pRank_three_center_quotient (W.elemZ K) (W.elemA K) (fun i => (hf i).1)
    (fun i => (hf i).2.1) (fun i => (hf i).2.2) hZA hZZ

end RootWitness

theorem witnessF4_orthoCheck
    : witnessF4.orthoCheck = true := by decide +kernel
theorem witnessE6_orthoCheck
    : witnessE6.orthoCheck = true := by decide +kernel
theorem witnessE7_orthoCheck
    : witnessE7.orthoCheck = true := by decide +kernel
theorem witnessE8_orthoCheck
    : witnessE8.orthoCheck = true := by decide +kernel

theorem four_le_pRank_three_adjointQuotient
    {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K] [CharP K 2] :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact RootWitness.le_pRank_three_adjointQuotient witnessF4_check witnessF4_orthoCheck
      ![(0 : Fin 4), (0 : Fin 4), (0 : Fin 4), (1 : Fin 4)] (by decide)
  · exact RootWitness.le_pRank_three_adjointQuotient witnessE6_check witnessE6_orthoCheck
      ![(1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (2 : Fin 6)] (by decide)
  · exact RootWitness.le_pRank_three_adjointQuotient witnessE7_check witnessE7_orthoCheck
      ![(5 : Fin 7), (3 : Fin 7), (0 : Fin 7), (3 : Fin 7)] (by decide)
  · exact RootWitness.le_pRank_three_adjointQuotient witnessE8_check witnessE8_orthoCheck
      ![(6 : Fin 8), (4 : Fin 8), (1 : Fin 8), (3 : Fin 8)] (by decide)

end CFSG.LieType.Chevalley
