module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniBlockJ2
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeInnAutCore
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.Models.Blueprint
import CFSG.Adapters.TauCetiLieModels
import CFSG.Blueprint.LieModelAPI
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
import CFSG.Models.Transport
import CFSG.Sporadic.Schreier.Fi22Schreier

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.LocalAnalysis.GLTheoremA.K155X
open CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement MatrixGroups


theorem innDiagOn_of_uniJSelfDualModel_three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Γ : Type} [Group Γ] [Finite Γ] {J : Subgroup Γ} {b : Γ}
    (hbJ : b ∈ Subgroup.normalizer (J : Set Γ))
    (hq : CFSG.IsQuasisimple (PQuot p J)) (hbp : b ^ p = 1)
    {m : ℕ} {E : Type} [Field E] [Finite E] {k : ℕ} (hE : UnitaryFieldData 2 k E)
    (B₁ : GL (Fin m) E) (hB₁ : B₁ ∈ primeFormUnitary hE (idGram E m))
    (hconj : ∀ P : ↥(StatedSU m (2 ^ k) E),
      B₁ * (P : GL (Fin m) E) * B₁⁻¹ ∈ StatedSU m (2 ^ k) E)
    (e₀ : PSimple p J ≃* LargeEvenProj (StatedSU m (2 ^ k) E))
    (he₀ : ∀ P : ↥(StatedSU m (2 ^ k) E),
      MulAut.congr e₀ (MI.indAut p J b hbJ) (LargeEvenProjMk (StatedSU m (2 ^ k) E) P) =
        LargeEvenProjMk (StatedSU m (2 ^ k) E)
          ⟨B₁ * (P : GL (Fin m) E) * B₁⁻¹, hconj P⟩)
    (hm3 : 3 ≤ m) (hm3k : m = 3 → 2 ≤ k) :
    InnDiagOn p (Subgroup.zpowers b) J := by
  classical
  have hm1 : 1 ≤ m := by omega
  have hIndPow : (MI.indAut p J b hbJ) ^ p = 1 := by
    have hbp' : (b⁻¹) ^ p = 1 := by rw [inv_pow, hbp, inv_one]
    exact chevAut_pow_eq_one p J (Subgroup.inv_mem _ hbJ) hbp'
  let M : primeFormUnitary hE (idGram E m) := ⟨B₁, hB₁⟩
  have hB₁N : B₁ ∈ Subgroup.normalizer (StatedSU m (2 ^ k) E : Set (GL (Fin m) E)) :=
    CFSG.StandardType.SUTorus.mem_normalizer_of_mem_primeFormUnitary hE hB₁
  let B₁n : Subgroup.normalizer (StatedSU m (2 ^ k) E : Set (GL (Fin m) E)) :=
    ⟨B₁, hB₁N⟩
  have hconj_eq : MulAut.congr e₀ (MI.indAut p J b hbJ) =
      TableB.projConj (StatedSU m (2 ^ k) E) B₁n := by
    ext x
    obtain ⟨P, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin m) E).subgroupOf (StatedSU m (2 ^ k) E)) x
    change MulAut.congr e₀ (MI.indAut p J b hbJ)
        (LargeEvenProjMk (StatedSU m (2 ^ k) E) P) =
      TableB.projConj (StatedSU m (2 ^ k) E) B₁n
        (LargeEvenProjMk (StatedSU m (2 ^ k) E) P)
    rw [he₀ P, show LargeEvenProjMk (StatedSU m (2 ^ k) E) P =
        ((P : StatedSU m (2 ^ k) E) : LargeEvenProj (StatedSU m (2 ^ k) E)) from rfl,
      TableB.projConj_mk]
    congr 1
  have hPCpow : (TableB.projConj (StatedSU m (2 ^ k) E) B₁n) ^ p = 1 := by
    rw [← hconj_eq, ← map_pow, hIndPow, map_one]
  have hlink : uConjAut hE hm1 M =
      TableB.projConj (StatedSU m (2 ^ k) E) B₁n := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      ((StatedScalars (Fin m) E).subgroupOf (StatedSU m (2 ^ k) E)) z
    rw [uConjAut_proj hE hm1 M g]
    show LargeEvenProjMk (StatedSU m (2 ^ k) E)
        ⟨B₁ * (g : GL (Fin m) E) * B₁⁻¹, _⟩ =
      TableB.projConj (StatedSU m (2 ^ k) E) B₁n
        ((g : ↥(StatedSU m (2 ^ k) E)) : LargeEvenProj (StatedSU m (2 ^ k) E))
    rw [TableB.projConj_mk]
    congr 1
  have hUCpow : (uConjAut hE hm1 M) ^ p = 1 := by
    rw [hlink]; exact hPCpow
  have hpfp : (primeFormConjHom hE (idGram E m) M) ^ p = 1 := by
    have h1 : primeFormConjHom hE (idGram E m) M =
        MulAut.congr (uTransport hE hm1) (uConjAut hE hm1 M) :=
      (MulEquiv.apply_symm_apply _ _).symm
    rw [h1, ← map_pow, hUCpow, map_one]
  have hmemPF : primeFormConjHom hE (idGram E m) M ∈
      innAutDerived (primeFormP hE (idGram E m)) :=
    mem_innAutDerived_of_mem_primeFormD hE hp hp2 ⟨M, rfl⟩ hpfp
  have hmemQ : uConjAut hE hm1 M ∈
      innAutDerived (StatedProj (StatedSU m (2 ^ k) E)) := by
    refine (mem_innAutDerived_congr (uTransport hE hm1)).1 ?_
    have h1 : MulAut.congr (uTransport hE hm1) (uConjAut hE hm1 M) =
        primeFormConjHom hE (idGram E m) M := by
      rw [show uConjAut hE hm1 M = (MulAut.congr (uTransport hE hm1)).symm
          (primeFormConjHom hE (idGram E m) M) from rfl]
      exact MulEquiv.apply_symm_apply _ _
    rwa [h1]
  have hmemT : TableB.projConj (StatedSU m (2 ^ k) E) B₁n ∈
      innAutDerived (LargeEvenProj (StatedSU m (2 ^ k) E)) := by
    rw [← hlink]
    exact hmemQ
  have hmem_ind : MI.indAut p J b hbJ ∈ innAutDerived (PSimple p J) :=
    (mem_innAutDerived_congr e₀).1 (by rw [hconj_eq]; exact hmemT)
  have hEcard : Nat.card E = (2 ^ k) ^ 2 := by
    calc Nat.card E = 2 ^ (2 * k) := hE.card
      _ = 2 ^ (k * 2) := by rw [Nat.mul_comm]
      _ = (2 ^ k) ^ 2 := by rw [pow_mul]
  have hk1 : 1 ≤ k := hE.one_le
  have hne : (m, 2 ^ k) ≠ (3, 2) := by
    intro h
    have hm3' : m = 3 := congrArg Prod.fst h
    have h2 : 2 ^ k = 2 := congrArg Prod.snd h
    have hk2 : 2 ≤ k := hm3k hm3'
    have h4 : 4 ≤ 2 ^ k := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hk2
    omega
  have hadm : StatedLieAdmissible .PSU m 2 k := ⟨Nat.prime_two, hk1, hm3, hne⟩
  have hLM : CFSG.Blueprint.LieModel (PSimple p J) .PSU m 2 k :=
    CFSG.Models.LieModel.toBlueprint (by simp [CFSG.Blueprint.classicalTags])
      (CFSG.Models.lieModel_of_statedClassicalModel
        ⟨hadm, E, inferInstance, inferInstance, hEcard, ⟨e₀⟩⟩)
  exact innDiagOn_of_lieModel hbJ hq hLM
    (by rintro ⟨h, -⟩; exact StatedLieTag.noConfusion h) (by decide) hmem_ind

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
