module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycLie
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrG2

public section

namespace CFSG.LieType.Chevalley.RootWitness

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

section Facts

variable {τ : Tag} {n : ℕ} {W : RootWitness τ n}

theorem charTwo_facts_of_rankOne
    (hW : W.check = true) (hO : W.orthoCheck = true) {K : Type} [Field K]
    (hrk : ∀ i, rankOneZ (K := K) (W.simple i) ^ 3 = 1 ∧
      ¬ Commute (rankOneZ (K := K) (W.simple i))
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1) ∧
      ¬ Commute (rankOneZ (K := K) (W.simple i) ^ 2)
        ((rootOperatorFamily τ).eltElement (simpleRoot τ (W.simple i)) 1)) :
    (∀ i, W.elemZ K i ^ 3 = 1 ∧ ¬ Commute (W.elemZ K i) (W.elemA K i) ∧
      ¬ Commute (W.elemZ K i ^ 2) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K j) (W.elemA K i)) ∧
    (∀ i j, i ≠ j → Commute (W.elemZ K i) (W.elemZ K j)) := by
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

end Facts

end CFSG.LieType.Chevalley.RootWitness

namespace CFSG.AGLEmbedding.BlockCyc

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.Open CFSG.AGLEmbedding.ParabAutIrr

def witnessG2 : RootWitness .G2 2 where
  word := ![([] : List (Fin 2)), ([1, 0] : List (Fin 2))]
  simple := ![(0 : Fin 2), (1 : Fin 2)]

theorem witnessG2_check : witnessG2.check = true := by decide +kernel

theorem witnessG2_orthoCheck : witnessG2.orthoCheck = true := by decide +kernel

section G2


theorem g2_rankOneZ_facts {K : Type} [Field K] (h2 : (1 : K) + 1 = 0)
    (i : Fin (Tag.rank .G2)) :
    rankOneZ (τ := .G2) (K := K) i ^ 3 = 1 ∧
      ¬ Commute (rankOneZ (τ := .G2) (K := K) i)
        ((rootOperatorFamily .G2).eltElement (simpleRoot .G2 i) 1) ∧
      ¬ Commute (rankOneZ (τ := .G2) (K := K) i ^ 2)
        ((rootOperatorFamily .G2).eltElement (simpleRoot .G2 i) 1) := by
  obtain ⟨φ, hφ, hu, hl⟩ := g2_exists_sl2_hom (K := K) i
  have hz : rankOneZ (τ := .G2) (K := K) i = φ (sl2Upper 1 * sl2Lower 1) := by
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

theorem hasE9_adjoint_g2 {K : Type} [Field K] [CharP K 2] : HasE9 (adjointGroup .G2 K) := by
  have h2 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact CharP.cast_eq_zero K 2
  obtain ⟨hf, hZA, hZZ⟩ := RootWitness.charTwo_facts_of_rankOne (W := witnessG2) witnessG2_check
    witnessG2_orthoCheck (K := K) (fun i => g2_rankOneZ_facts h2 _)
  refine hasE9_of_commuting_orders (MonoidHom.id (adjointGroup .G2 K)) (fun z hz => ?_)
    (hf 0).1 (hf 1).1 (hZZ 0 1 (by decide)).eq (hZA 1 0 (by decide)).symm
    (fun h => (hf 1).2.1 h.symm) (fun h => (hf 0).2.1 h.symm)
  rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
  rw [hz]
  exact Subgroup.one_mem _

theorem lieCyclicG2 : LieCyclicG2 := by
  rintro Y _ ⟨q, hv, hq, ⟨e⟩⟩
  obtain ⟨K, _, _, _, -, -, -, ⟨e'⟩⟩ := exists_g2_field q hv hq e
  exact hasE9_of_mulEquiv e'.symm hasE9_adjoint_g2

end G2

end CFSG.AGLEmbedding.BlockCyc
