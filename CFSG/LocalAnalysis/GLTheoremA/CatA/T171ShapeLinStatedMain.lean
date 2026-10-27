module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedRecipe
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.Models.Blueprint
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
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

private theorem one_le_of_faithful {G : Type} [Group G] [Finite G] {p N n : ℕ}
    {L J A : Subgroup G} {d b : G} {K : Type} [Field K] [Finite K]
    (hS : WSetup p L J A d b) (hcard : Nat.card K = 2 ^ n)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (StatedSL N K))
    (D : GL (Fin N) K) (hD : D ∈ Subgroup.normalizer (StatedSL N K : Set (GL (Fin N) K)))
    (hDind : LargeEvenInduces θ (conjRel d)
      (TableB.projConj (StatedSL N K) ⟨D, hD⟩)) :
    1 ≤ N := by
  by_contra hN
  have hN0 : N = 0 := by omega
  subst hN0
  have hmat : Subsingleton (Matrix (Fin 0) (Fin 0) K) := by
    constructor
    intro X Y
    ext i
    exact i.elim0
  have hD1 : D = 1 := by
    apply Units.ext
    exact Subsingleton.elim _ _
  have hproj : TableB.projConj (StatedSL 0 K) ⟨D, hD⟩ = 1 := by
    rw [hD1]
    exact map_one _
  have hind : LargeEvenInduces θ (conjRel d) (1 : MulAut (LargeEvenProj (StatedSL 0 K))) := by
    rwa [hproj] at hDind
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hperf : Group.IsPerfect ↥L := ⟨hS.qs.1⟩
  have hcent : d ∈ Subgroup.centralizer (L : Set G) :=
    centralizes_of_conjRel_center hdN
      (exists_center_of_largeEvenInduces_one hdN hind) hperf
  have hbot : d ∈ (⊥ : Subgroup G) := by
    have hinf : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcent⟩
    rwa [hS.faithful] at hinf
  exact hS.d_ne (Subgroup.mem_bot.mp hbot)

theorem linBlockInnDiagStated_holds :
    LinBlockInnDiagStated := by
  intro G _ _ p L J A d b N n K _ _ hcard hS θ D B hD hB hDp hcomm hDind hBind
  have hp := hS.prime
  have hp2 := hS.odd
  have hdp : d ^ p = 1 := hS.elem.2 d hS.d_mem
  have hbp : b ^ p = 1 := hS.elem.2 b hS.b_mem
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.d_mem
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hS.b_mem
  letI : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by
      rw [Nat.card_eq_fintype_card] at hcard
      exact hcard)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hNpos : 1 ≤ N :=
    one_le_of_faithful hS hcard θ D hD hDind
  obtain ⟨d₁, D₁, instD, finD, B₁, e₀, h2D, hd₁, h22, h23, hact⟩ :=
    linJ_equiv_comm hp hp2 hdp hdN hbN hS.pcomp hS.b_norm h2 hNpos θ D B hcomm
      (TableB.projConj (StatedSL N K) ⟨D, hD⟩)
      (TableB.projConj (StatedSL N K) ⟨B, hB⟩)
      (fun h h' hh => projConj_apply_mk D hD hh)
      (fun g g' hg => projConj_apply_mk B hB hg) hDind hBind
  letI : Field D₁ := instD
  letI : Finite D₁ := finD
  letI : Fintype D₁ := Fintype.ofFinite D₁
  let B₁n : Subgroup.normalizer (StatedSL d₁ D₁ : Set (GL (Fin d₁) D₁)) :=
    ⟨B₁, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top B₁⟩
  have hIndPow : (MI.indAut p J b hS.b_norm) ^ p = 1 := by
    have hbp' : (b⁻¹) ^ p = 1 := by rw [inv_pow, hbp, inv_one]
    exact chevAut_pow_eq_one p J (Subgroup.inv_mem _ hS.b_norm) hbp'
  have hconj_eq : MulAut.congr e₀ (MI.indAut p J b hS.b_norm) =
      TableB.projConj (StatedSL d₁ D₁) B₁n := by
    ext x
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin d₁) D₁).subgroupOf (StatedSL d₁ D₁)) x
    change MulAut.congr e₀ (MI.indAut p J b hS.b_norm)
        (LargeEvenProjMk (StatedSL d₁ D₁) m) =
      TableB.projConj (StatedSL d₁ D₁) B₁n (LargeEvenProjMk (StatedSL d₁ D₁) m)
    rw [hact m,
      show LargeEvenProjMk (StatedSL d₁ D₁) m =
        ((m : StatedSL d₁ D₁) : LargeEvenProj (StatedSL d₁ D₁)) from rfl,
      TableB.projConj_mk]
    congr 1
  have hPCpow : (TableB.projConj (StatedSL d₁ D₁) B₁n) ^ p = 1 := by
    rw [← hconj_eq, ← map_pow, hIndPow, map_one]
  have hrecipe := statedProjConj_recipe (N := d₁) (K := D₁) B₁ B₁n.2
  have hconjpow : (LinearFlag.conjAut d₁ D₁ B₁) ^ p = 1 := by
    rw [← hrecipe, ← map_pow, hPCpow, map_one]
  have hmem_conj : LinearFlag.conjAut d₁ D₁ B₁ ∈
      innAutDerived (LinearFlag.projectiveSL d₁ D₁) :=
    mem_innAutDerived_of_mem_linearAutGroup hp hp2 hconjpow
      (LinearFlag.conjAut_mem_linearAutGroup B₁)
  have hmem_PC : TableB.projConj (StatedSL d₁ D₁) B₁n ∈
      innAutDerived (LargeEvenProj (StatedSL d₁ D₁)) := by
    refine (mem_innAutDerived_congr (statedRecipeEquiv d₁ D₁).symm).1 ?_
    rwa [hrecipe]
  have hmem_ind : MI.indAut p J b hS.b_norm ∈ innAutDerived (PSimple p J) :=
    (mem_innAutDerived_congr e₀).1 (by rw [hconj_eq]; exact hmem_PC)
  have hq : CFSG.IsQuasisimple (PQuot p J) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff (PQuot p J)).2.2.1.mpr
      (isQuasisimple_pQuot_of_glaPComponent hS.prime hS.pcomp)
  obtain ⟨q, hcharq, f, hqprime, hfcard⟩ := FiniteField.card' D₁
  have hq2 : q = 2 := by
    have hdvd : q ∣ 2 := (CharP.cast_eq_zero_iff D₁ q 2).mp h2D
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hqprime.ne_one
    · exact h
  have hcardD₁ : Nat.card D₁ = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hfcard, hq2]
  have hfpos : 1 ≤ (f : ℕ) := f.pos
  have hadm : StatedLieAdmissible .PSL d₁ 2 (f : ℕ) := by
    refine ⟨Nat.prime_two, hfpos, hd₁, ?_, ?_⟩
    · intro h
      have h1 : d₁ = 2 := congrArg Prod.fst h
      have h2f : Nat.card D₁ = 2 := by
        rw [hcardD₁]
        exact congrArg Prod.snd h
      rcases h22 with h' | h'
      · exact h' h1
      · exact h' h2f
    · intro h
      have h1 : d₁ = 2 := congrArg Prod.fst h
      have h2f : Nat.card D₁ = 3 := by
        rw [hcardD₁]
        exact congrArg Prod.snd h
      rcases h23 with h' | h'
      · exact h' h1
      · exact h' h2f
  have hLM : CFSG.Blueprint.LieModel (PSimple p J) .PSL d₁ 2 (f : ℕ) :=
    CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_of_statedClassicalModel
        ⟨hadm, D₁, inferInstance, inferInstance, hcardD₁, ⟨e₀⟩⟩)
  exact innDiagOn_of_lieModel hS.b_norm hq hLM
    (by rintro ⟨h, -⟩; exact StatedLieTag.noConfusion h) (by decide) hmem_ind

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
