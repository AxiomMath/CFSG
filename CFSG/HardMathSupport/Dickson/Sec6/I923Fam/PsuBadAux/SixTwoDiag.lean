module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuBadAux.SixTwoEmb
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.FieldLayer

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne.Sec66T
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremB CFSG.ComponentClassification.CatLeaf
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.PSUTwo
open scoped commutatorElement

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem noL2Layer_diag_sixTwo (hO : LieOrderFormulasInput) (i₀ : Fin 6) {ν μ : K} (hνμ : ν ≠ μ)
    {D : primeFormUnitary h (idGram K 6)}
    (hD : ((D : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = dmat i₀ ν μ) :
    NoL2Layer (primeFormConjHom h (idGram K 6) D) := by
  classical
  have hfin := h.finite
  have hq : 2 ^ 1 = 2 := by norm_num
  have hn5 : 3 ≤ 5 := by norm_num
  have hq5 : ¬(5 = 3 ∧ 2 ^ 1 = 2) := fun hh => by omega
  set ξ := xi6 h hq i₀ with hξ
  have hinj : Function.Injective ξ := xi6_injective h hq i₀
  let eB : primeFormP h (idGram K 5) ≃* ↥ξ.range := MonoidHom.ofInjective hinj
  have hs₀ := isSimpleGroup_primeFormP_one h hn5 hq5
  have hnc₀ := not_commute_primeFormP_one h hn5 hq5
  haveI : IsSimpleGroup (primeFormP h (idGram K 5)) := hs₀
  haveI : IsSimpleGroup ↥ξ.range := eB.symm.isSimpleGroup
  have hnab : ∃ a b : ↥ξ.range, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hnc₀
    intro x y
    apply eB.injective
    rw [map_mul, map_mul]
    exact hcon _ _
  have hperf₀ : Group.IsPerfect (primeFormP h (idGram K 5)) := by
    have := isPerfect_gramSU_one h hn5 hq5
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hBC : ξ.range ≤ fixSubgroup (primeFormConjHom h (idGram K 6) D) :=
    range_xi6_le_fix h hq i₀ hD
  have hCC := commutator_fix_le_range_xi6 h hq i₀ hνμ hD
  have hJCC : ξ.range ≤ ⁅fixSubgroup (primeFormConjHom h (idGram K 6) D),
      fixSubgroup (primeFormConjHom h (idGram K 6) D)⁆ := by
    haveI := hperf₀
    calc ξ.range = ⁅ξ.range, ξ.range⁆ := range_eq_commutator_of_perfect ξ
      _ ≤ _ := Subgroup.commutator_mono hBC hBC
  have hadm : StatedLieAdmissible .PSU 5 2 1 :=
    ⟨Nat.prime_two, le_refl 1, hn5, fun hc => absurd (Prod.mk.inj hc).1 (by norm_num)⟩
  have hcard : Nat.card K = (2 ^ 1) ^ 2 := by rw [h.card]; norm_num
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 5) (K := K))
  have hmodel : LieModel ↥ξ.range .PSU 5 2 1 :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨hadm, K, inferInstance, inferInstance, hcard,
        ⟨(eB.symm.trans eP).trans (unitaryPSUEquiv h (by norm_num))⟩⟩
  exact noL2_of_simple_commutator_fixed _ ξ.range (le_antisymm hJCC hCC) inferInstance hnab
    fun r hr hT => not_typeL2_of_lieModel hO hadm hmodel (by decide) (by simp)
      (center_eq_bot_of_simple hnab) hr hT

end CFSG.HardMathSupport.Dickson.Sec6.I923
