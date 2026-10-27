module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer

section Rigid

theorem coe_sl2Upper' {K : Type*} [Field K] (c : K) :
    ((CFSG.LieType.Steinberg.sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

theorem coe_sl2Lower' {K : Type*} [Field K] (c : K) :
    ((CFSG.LieType.Steinberg.sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

theorem coe_uSL' {K : Type*} [Field K] (c : K) :
    ((uSL c : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, c; 0, 1] := rfl

theorem coe_vSL' {K : Type*} [Field K] (c : K) :
    ((vSL c : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; c, 1] := rfl

theorem sl2_rigid {K L G : Type*} [Field K] [Field L] [Group G] {R : SL2 L →* G}
    (hR : Function.Injective R) (φ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (f : K →+* L)
    {a b : L} (ha : a ≠ 0)
    (hu : ∀ c, φ (CFSG.LieType.Steinberg.sl2Upper c) = R (uSL (a * f c)))
    (hl : ∀ c, φ (CFSG.LieType.Steinberg.sl2Lower c) = R (vSL (b * f c))) : a * b = 1 := by
  have hw : CFSG.LieType.Steinberg.sl2Upper (1 : K) * CFSG.LieType.Steinberg.sl2Lower (-1) *
      CFSG.LieType.Steinberg.sl2Upper 1 * CFSG.LieType.Steinberg.sl2Upper 1 =
      CFSG.LieType.Steinberg.sl2Lower (-1) * (CFSG.LieType.Steinberg.sl2Upper 1 *
        CFSG.LieType.Steinberg.sl2Lower (-1) * CFSG.LieType.Steinberg.sl2Upper 1) := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper', coe_sl2Lower']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have e1 : R (uSL a * vSL (-b) * uSL a * uSL a) = R (vSL (-b) * (uSL a * vSL (-b) * uSL a)) := by
    simpa only [map_mul, hu, hl, map_one, map_neg, mul_one, mul_neg] using congrArg φ hw
  have hLm : ((uSL a * vSL (-b) * uSL a * uSL a : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      !![1 - a * b, 3 * a - 2 * a ^ 2 * b; -b, 1 - 2 * a * b] := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL', coe_vSL']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hRm : ((vSL (-b) * (uSL a * vSL (-b) * uSL a) : SL2 L) : Matrix (Fin 2) (Fin 2) L) =
      !![1 - a * b, 2 * a - a ^ 2 * b; -b * (1 - a * b) - b, -b * (2 * a - a ^ 2 * b) + 1 - a * b] := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uSL', coe_vSL']
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have e2 := congrArg (fun X : SL2 L => (X : Matrix (Fin 2) (Fin 2) L) 0 1) (hR e1)
  simp only [hLm, hRm] at e2
  have e3 : 3 * a - 2 * a ^ 2 * b = 2 * a - a ^ 2 * b := e2
  have h5 : a * (1 - a * b) = 0 := by linear_combination e3
  rcases mul_eq_zero.1 h5 with h | h
  · exact absurd h ha
  · linear_combination -h

end Rigid


theorem simpleRootSL2_injective_E8 (L : Type) [Field L] (i : Fin Tag.E8.rank) :
    Function.Injective (simpleRootSL2 Tag.E8 L i) := by
  by_cases h : ringChar L = 2
  · haveI : CharP L 2 := ringChar.of_eq h
    exact CFSG.RankThree.Chevalley.simpleRootSL2_injective_of_charTwo i
  · exact simpleRootSL2_injective h i

@[expose] def e6W0E8Word : List (Fin Tag.E8.rank) :=
  [0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1,
    5, 4, 3, 2, 0]

@[expose] def tw8W : WeylGroup Tag.E8 :=
  qplusW Tag.E8 * (coxeterSystem Tag.E8).wordProd e6W0E8Word

@[expose] def a2W : WeylGroup Tag.E8 := (coxeterSystem Tag.E8).wordProd wordL

theorem e6W0E8_foldr_single : ∀ k : Fin 6,
    e6W0E8Word.foldr (reflect .E8) (Pi.single (e8E6Node k) 1) =
      -Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1 := by
  decide +kernel

theorem e6W0E8_foldr_a2 : ∀ i j : Fin 3,
    e6W0E8Word.foldr (reflect .E8)
        (wordL.foldr (reflect .E8) (e8a2Weight i) - wordL.foldr (reflect .E8) (e8a2Weight j)) =
      wordL.foldr (reflect .E8) (e8a2Weight i) - wordL.foldr (reflect .E8) (e8a2Weight j) := by
  decide +kernel

theorem tw8W_smul_e6 (k : Fin 6) :
    tw8W • (Pi.single (e8E6Node k) 1 : Fin Tag.E8.rank → ℤ) =
      Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1 := by
  rw [tw8W, mul_smul, wordProd_smul, e6W0E8_foldr_single, qplusW_smul (Or.inr rfl), neg_neg]

theorem tw8W_smul_neg_e6 (k : Fin 6) :
    tw8W • (-Pi.single (e8E6Node k) 1 : Fin Tag.E8.rank → ℤ) =
      -Pi.single (e8E6Node (CFSG.LieType.Steinberg.TwistedE6.rhoPerm k)) 1 := by
  rw [smul_neg, tw8W_smul_e6]

theorem tw8W_smul_sigmaRoot (i j : Fin 3) :
    tw8W • sigmaRootE8 a2W i j = sigmaRootE8 a2W j i := by
  have hv : ∀ k, wbE8 a2W k = wordL.foldr (reflect .E8) (e8a2Weight k) := fun k => by
    rw [wbE8, a2W]
    exact wordProd_smul (τ := Tag.E8) wordL _
  rw [sigmaRootE8, sigmaRootE8, hv i, hv j, tw8W, mul_smul]
  rw [wordProd_smul (τ := Tag.E8), e6W0E8_foldr_a2, qplusW_smul (Or.inr rfl), neg_sub]

end CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw
