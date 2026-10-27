module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E6HeisenbergAux.PairAuxSc
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

set_option linter.unusedSectionVars false

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
open CFSG.LieType.Steinberg.Minuscule.MinData (toWeight reflectWeight)
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis.PairAux
  (eq_of_e6RootParams_eq_of_wtEval rootChar_e6Shift_inv_eq_one)

theorem exists_cube_params {L : Type} [Field L] {ω : L} (hω : IsPrimitiveRoot ω 3)
    {a : Fin Tag.E6.rank → Lˣ} (ha : ∀ i, a i ^ 3 = 1) (hc : ∏ i, a i ^ e6c i = 1) :
    ∃ u : Fin Tag.E6.rank → Lˣ, (∀ l, u l ^ 3 = 1) ∧ e6RootParams u = a := by
  have hsymm : ∀ l j : Fin Tag.E6.rank, Tag.cartan Tag.E6 l j = Tag.cartan Tag.E6 j l := by
    intro l j
    fin_cases l <;> fin_cases j <;> decide
  have hωu : IsUnit ω := hω.isUnit (by norm_num)
  set ω' : Lˣ := hωu.unit with hω'
  have hω'prim : IsPrimitiveRoot ω' 3 := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [hω'] using hω
  have hω'3 : ω' ^ 3 = 1 := hω'prim.pow_eq_one
  have hk : ∀ i, ∃ k : ℕ, a i = ω' ^ k := fun i => by
    have h3 : ((a i : Lˣ) : L) ^ 3 = 1 := by
      have := congrArg Units.val (ha i)
      simpa using this
    obtain ⟨m, -, hm⟩ := hω.eq_pow_of_pow_eq_one h3
    exact ⟨m, Units.ext (by simp [hω', hm])⟩
  choose k hk using hk
  have hsum : ω' ^ (∑ i, e6c i * (k i : ℤ)) = 1 := by
    have h1 : ∏ i, a i ^ e6c i = ω' ^ (∑ i, e6c i * (k i : ℤ)) := by
      rw [CFSG.LieType.Steinberg.CentralExt.AdjointClosed.zpow_sum_eq_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hk i, ← zpow_natCast, ← zpow_mul, mul_comm]
    rw [← h1]
    exact hc
  set m : Fin Tag.E6.rank → ℤ := fun l => ∑ i, e6C l i * (k i : ℤ) with hm
  have hS : ∀ j : Fin Tag.E6.rank, ∑ l, m l * Tag.cartan Tag.E6 l j =
      (k j : ℤ) - (if j = ⟨0, by decide⟩ then ∑ i, e6c i * (k i : ℤ) else 0) := by
    intro j
    have e1 : ∑ l, m l * Tag.cartan Tag.E6 l j =
        ∑ i, (k i : ℤ) * ∑ l, Tag.cartan Tag.E6 j l * e6C l i := by
      simp only [hm, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hsymm l j]
      ring
    have e2 : ∀ i : Fin Tag.E6.rank, ∑ l, Tag.cartan Tag.E6 j l * e6C l i =
        (if j = i then 1 else 0) - (if j = ⟨0, by decide⟩ then e6c i else 0) := by
      intro i
      have := e6C_spec j i
      linarith
    have e3 : ∑ i, (k i : ℤ) * (if j = i then (1 : ℤ) else 0) = k j := by
      simp [mul_ite]
    have e4 : ∑ i, (k i : ℤ) * (if j = (⟨0, by decide⟩ : Fin Tag.E6.rank) then e6c i else 0) =
        if j = (⟨0, by decide⟩ : Fin Tag.E6.rank) then ∑ i, e6c i * (k i : ℤ) else 0 := by
      split_ifs
      · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      · simp
    rw [e1]
    calc ∑ i, (k i : ℤ) * ∑ l, Tag.cartan Tag.E6 j l * e6C l i
        = ∑ i, ((k i : ℤ) * (if j = i then 1 else 0) -
            (k i : ℤ) * (if j = (⟨0, by decide⟩ : Fin Tag.E6.rank) then e6c i else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [e2 i]
          ring
      _ = _ := by rw [Finset.sum_sub_distrib, e3, e4]
  refine ⟨fun l => ω' ^ m l, fun l => ?_, funext fun j => ?_⟩
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω'3, one_zpow]
  · change ∏ l, (ω' ^ m l) ^ Tag.cartan Tag.E6 l j = a j
    simp_rw [← zpow_mul]
    rw [← CFSG.LieType.Steinberg.CentralExt.AdjointClosed.zpow_sum_eq_prod, hS j, hk j,
      ← zpow_natCast]
    split_ifs
    · rw [zpow_sub, hsum, inv_one, mul_one]
    · rw [sub_zero]

theorem e6RootParams_mul {K : Type} [Field K] (u u' : Fin Tag.E6.rank → Kˣ) :
    e6RootParams (u * u') = e6RootParams u * e6RootParams u' := by
  funext j
  simp only [e6RootParams, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem e6RootParams_map {K k : Type} [Field K] [Field k] (ι : K →+* k)
    (u : Fin Tag.E6.rank → Kˣ) :
    e6RootParams (fun l => Units.map ι.toMonoidHom (u l)) =
      fun j => Units.map ι.toMonoidHom (e6RootParams u j) := by
  funext j
  simp only [e6RootParams, map_prod, map_zpow]

section Lift

attribute [local instance] CFSG.HardMathSupport.Timmesfeld.CrossChar.e6ScLiftNeZeroRank

theorem e6Isogeny_ker_central {k : Type} [Field k] [Finite k] {g g' : e6Data_valid.minGroup k}
    (h : ((e6Isogeny k g : adjointGroup Tag.E6 k) : ModGL Tag.E6 k) =
      ((e6Isogeny k g' : adjointGroup Tag.E6 k) : ModGL Tag.E6 k)) :
    g'⁻¹ * g ∈ Subgroup.center (e6Data_valid.minGroup k) := by
  refine ker_e6IsogenyT_le_center k ?_
  rw [MonoidHom.mem_ker]
  change e6Isogeny k (g'⁻¹ * g) = 1
  rw [map_mul, map_inv, inv_mul_eq_one]
  exact Subtype.ext h.symm

theorem e6NWord_conj_minTorus_eq {k : Type} [Field k] (u : Fin Tag.E6.rank → kˣ)
    (ω : List (Fin Tag.E6.rank))
    (hw : (coxeterSystem Tag.E6).wordProd ω ∈ rootCharStabilizer (e6RootParams u))
    (hs : rootChar (e6RootParams u) (e6Shift ((coxeterSystem Tag.E6).wordProd ω)) = 1) :
    e6NWord k ω * minTorus e6Data_valid k u * (e6NWord k ω)⁻¹ = minTorus e6Data_valid k u := by
  rw [nWord_conj_minTorus]
  congr 1
  set w := (coxeterSystem Tag.E6).wordProd ω with hwdef
  set u' := ω.foldr e6StarS u with hu'
  have hwinv : w⁻¹ ∈ rootCharStabilizer (e6RootParams u) := by
    intro v
    have h := hw (w⁻¹ • v)
    rw [smul_inv_smul] at h
    exact h.symm
  refine eq_of_e6RootParams_eq_of_wtEval ?_ ?_
  ·
    funext j
    have h : rootChar (e6RootParams u') (Pi.single j 1) = rootChar (e6RootParams u) (Pi.single j 1) := by
      rw [← e6WtEval_toWeight, hu', e6WtEval_foldr, ← toWeight_foldl_reflect,
        ← wordProd_inv_smul_E6, e6WtEval_toWeight, hwinv]
    simpa [rootChar, Pi.single_apply] using h
  ·
    have e3 := toWeight_e6Shift_inv ω
    rw [← hwdef] at e3
    have e4 : ω.foldl (fun ν j => reflectWeight j ν) (Pi.single 0 1) =
        toWeight (e6Shift w⁻¹) + Pi.single 0 1 := by
      rw [e3, sub_add_cancel]
    rw [hu', e6WtEval_foldr, e4, e6WtEval_add, e6WtEval_toWeight,
      rootChar_e6Shift_inv_eq_one hw hs, one_mul]

end Lift

end CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

