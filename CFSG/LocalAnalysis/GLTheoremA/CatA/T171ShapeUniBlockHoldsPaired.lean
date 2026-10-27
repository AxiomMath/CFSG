module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockJ2
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedRecipe
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.Models.Blueprint
import CFSG.Adapters.TauCetiLieModels
import CFSG.Blueprint.LieModelAPI
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Split
import CFSG.HardMathSupport.Lang.UnitaryAutomorphisms.OuterFixedPSL
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLinTwoFam
import CFSG.LieType.SeitzGeneration.OuterLinearCat
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
import CFSG.Models.Transport
import CFSG.Sporadic.Schreier.Fi22Schreier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement


theorem innDiagOn_of_uniJPairedModel {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ} {b : Γ}
    (hbJ : b ∈ Subgroup.normalizer (J : Set Γ))
    (hq : CFSG.IsQuasisimple (PQuot p J)) (hbp : b ^ p = 1)
    (hM : UniJPairedModel p J b hbJ) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  classical
  obtain ⟨m, E, instE, finE, k, hk, B₁, e₀, hm2, hk2, he₀⟩ := hM
  letI : Field E := instE
  letI : Finite E := finE
  have hIndPow : (MI.indAut p J b hbJ) ^ p = 1 := by
    have hbp' : (b⁻¹) ^ p = 1 := by rw [inv_pow, hbp, inv_one]
    exact chevAut_pow_eq_one p J (Subgroup.inv_mem _ hbJ) hbp'
  let B₁n : Subgroup.normalizer (StatedSL m E : Set (GL (Fin m) E)) :=
    ⟨B₁, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top B₁⟩
  have hconj_eq : MulAut.congr e₀ (MI.indAut p J b hbJ) =
      TableB.projConj (StatedSL m E) B₁n := by
    ext x
    obtain ⟨M, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin m) E).subgroupOf (StatedSL m E)) x
    change MulAut.congr e₀ (MI.indAut p J b hbJ)
        (LargeEvenProjMk (StatedSL m E) M) =
      TableB.projConj (StatedSL m E) B₁n (LargeEvenProjMk (StatedSL m E) M)
    rw [he₀ M, show LargeEvenProjMk (StatedSL m E) M =
        ((M : StatedSL m E) : LargeEvenProj (StatedSL m E)) from rfl, TableB.projConj_mk]
    congr 1
  have hPCpow : (TableB.projConj (StatedSL m E) B₁n) ^ p = 1 := by
    rw [← hconj_eq, ← map_pow, hIndPow, map_one]
  have hrecipe := statedProjConj_recipe (N := m) (K := E) B₁ B₁n.2
  have hconjpow : (LinearFlag.conjAut m E B₁) ^ p = 1 := by
    rw [← hrecipe, ← map_pow, hPCpow, map_one]
  have hmem_conj : LinearFlag.conjAut m E B₁ ∈
      innAutDerived (LinearFlag.projectiveSL m E) :=
    mem_innAutDerived_of_mem_linearAutGroup hp hp2 hconjpow
      (LinearFlag.conjAut_mem_linearAutGroup B₁)
  have hmem_PC : TableB.projConj (StatedSL m E) B₁n ∈
      innAutDerived (LargeEvenProj (StatedSL m E)) := by
    refine (mem_innAutDerived_congr (statedRecipeEquiv m E).symm).1 ?_
    rwa [hrecipe]
  have hmem_ind : MI.indAut p J b hbJ ∈ innAutDerived (PSimple p J) :=
    (mem_innAutDerived_congr e₀).1 (by rw [hconj_eq]; exact hmem_PC)
  have hadm : StatedLieAdmissible .PSL m 2 k := by
    refine ⟨Nat.prime_two, by omega, hm2, ?_, ?_⟩
    · intro h
      have h2 : 2 ^ k = 2 := congrArg Prod.snd h
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    · intro h
      have h2 : 2 ^ k = 3 := congrArg Prod.snd h
      have h4 : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
  have hLM : CFSG.Blueprint.LieModel (PSimple p J) .PSL m 2 k :=
    CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_of_statedClassicalModel
        ⟨hadm, E, inferInstance, inferInstance, hk, ⟨e₀⟩⟩)
  exact innDiagOn_of_lieModel hbJ hq hLM
    (by rintro ⟨h, -⟩; exact StatedLieTag.noConfusion h) (by decide) hmem_ind

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
