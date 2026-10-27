module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.KFactOddAutParabolicReduce
public import CFSG.Open.StatedDefs
import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUOrder
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSp
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

private lemma projUnipotent_map_fieldAut {n : ℕ} {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) :
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent n K).map
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ).toMonoidHom =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent n K := by
  have hU : (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent n K).map
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ).toMonoidHom =
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.unipotent n K := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨u, hu, rfl⟩
      exact CFSG.AGLEmbedding.ParabAutIrr.fieldSp_mem_unipotent σ hu
    · exact le_of_eq (Subgroup.card_map_of_injective
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ).injective).symm
  have hcomp :
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ).toMonoidHom.comp
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K) =
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj n K).comp
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldSp n K σ).toMonoidHom := by
    ext g
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut_proj σ g
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.projUnipotent, Subgroup.map_map,
    hcomp, ← Subgroup.map_map, hU]

private lemma exists_sylow_two_projUnipotent_fieldAut_fixed {n : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    ∃ S : Sylow 2 (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)), ∀ σ : K ≃+* K,
      (S : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).map
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ).toMonoidHom =
        S := by
  obtain ⟨S, hS⟩ := CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_projUnipotent
    (K := K) 2 hn
  exact ⟨S, fun σ => by rw [hS]; exact projUnipotent_map_fieldAut σ⟩

private lemma mem_inner_of_pow_mem_of_mem_spLinearAutGroup {n f r : ℕ} {K : Type} [Field K]
    [Finite K] (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).relIndex
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K) ∣
      Nat.gcd 2 (2 ^ f - 1))
    {δ : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))}
    (hδ : δ ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K)
    (j : ℕ)
    (hδj : δ ^ (r ^ j) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))) :
    δ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) := by
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  have hle : ((CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).subgroupOf
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K)).index ≤ 2 :=
    Nat.le_of_dvd (by norm_num) (hrel.trans (Nat.gcd_dvd_left 2 _))
  refine Subgroup.mem_subgroupOf.mp
    (CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two
      ((CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).subgroupOf
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K)) hle
      (hodd.pow) (α := (⟨δ, hδ⟩ :
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K))
      (N := r ^ j) ?_)
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
  change δ ^ (r ^ j) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
    (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))
  exact hδj

private lemma eq_one_of_mem_spLinearAutGroup {n f r k : ℕ} {K : Type} [Field K] [Finite K]
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).relIndex
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K) ∣
      Nat.gcd 2 (2 ^ f - 1))
    {α : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))}
    (hD : α ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K)
    (hαp : α ^ (r ^ k) = 1)
    (hinn : Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) = ⊥) :
    α = 1 := by
  have hmem : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) := by
    refine mem_inner_of_pow_mem_of_mem_spLinearAutGroup hr hr5 hrel hD k ?_
    rw [hαp]
    exact Subgroup.one_mem _
  have hmem' : α ∈ Subgroup.zpowers α ⊓
      CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers α, hmem⟩
  rw [hinn] at hmem'
  exact Subgroup.mem_bot.mp hmem'

private lemma exists_conjAut_fieldAut_of_mem_semilinear {n f r k : ℕ} {K : Type} [Field K]
    [Finite K] (hn : 1 ≤ n) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hDn : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K).Normal)
    (hinj : Function.Injective
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K))
    (hrel : (CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).relIndex
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K) ∣
      Nat.gcd 2 (2 ^ f - 1))
    {α : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))}
    (hE : α ∈ CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup n K)
    (hαp : α ^ (r ^ k) = 1)
    (hinn : Subgroup.zpowers α ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) = ⊥) :
    ∃ (H : CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.gsp n K) (σ : K ≃+* K),
      α = CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut n K H *
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ *
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut n K H)⁻¹ := by
  obtain ⟨A, σ, hαeq⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.mem_spSemilinearAutGroup_iff.mp hE
  have hpow : (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut n K A *
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ) ^
      orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ) = 1 := by
    refine pow_orderOf_eq_one_of_mul
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)))
      (D := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K)
      (r := r) (k := k)
      (d := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut n K A)
      (f := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ)
      (fun δ hδ j hδj => mem_inner_of_pow_mem_of_mem_spLinearAutGroup hr hr5 hrel hδ j hδj)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut_mem_spLinearAutGroup A)
      (fun g hg => hDn.conj_mem g hg
        (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ)) ?_ ?_
    · rwa [hαeq] at hαp
    · rwa [hαeq] at hinn
  have hfσ : orderOf (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ) =
      orderOf σ :=
    orderOf_injective (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K) hinj σ
  rw [hfσ] at hpow
  obtain ⟨H, hH⟩ :=
    CFSG.StandardType.RecipeFieldSpU.conjAut_mul_fieldAut_conj_of_pow_orderOf
      (r := n) hn A σ hpow
  exact ⟨H, σ, by rw [hαeq, hH]⟩

private lemma oddAutSylowFixAt_statedProjStatedSp {n f r : ℕ} {K : Type} [Field K] [Finite K]
    (hcard : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hn : 2 ≤ n) (hr : r.Prime) (hr5 : 5 ≤ r) :
    OddAutSylowFixAt r (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K)) := by
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨-, hinj, -, -, -, hDn, -, -, hrel, -⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      (ℓ := 2) (f := f) (r := n) Nat.prime_two hf hn hcard
  obtain ⟨S₀, hS₀⟩ := exists_sylow_two_projUnipotent_fieldAut_fixed (K := K) (n := n) (by omega)
  refine OddAutSylowFixAt.of_conj S₀ ?_
  intro α k hα hinn
  have hαp : α ^ (r ^ k) = 1 := hα ▸ pow_orderOf_eq_one α
  have hodd : Odd r := hr.odd_of_ne_two (by omega)
  have hEmem : α ∈
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spSemilinearAutGroup n K :=
    CFSG.AGLEmbedding.ParabAutIrr.mem_spSemilinearAutGroup_of_pow hn (e := r ^ k)
      (hodd.pow) (by
        rw [hαp]
        exact Subgroup.one_mem _)
  by_cases hD : α ∈
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spLinearAutGroup n K
  · have hα1 : α = 1 := eq_one_of_mem_spLinearAutGroup hr hr5 hrel hD hαp hinn
    refine ⟨1, 1, by simp [hα1], ?_⟩
    rw [show (1 : MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp n K))).toMonoidHom =
        MonoidHom.id _ from rfl, Subgroup.map_id]
  · obtain ⟨H, σ, hαeq⟩ :=
      exists_conjAut_fieldAut_of_mem_semilinear (by omega) hr hr5 hDn hinj hrel hEmem hαp hinn
    exact ⟨CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.conjAut n K H,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut n K σ,
      hαeq, hS₀ σ⟩

theorem oddAutSylowFixAt_psp {Y : Type} [Group Y] [Finite Y] {n f r : ℕ}
    (hC : CFSG.Open.StatedClassicalModel Y .PSp n 2 f) (hr : r.Prime) (hr5 : 5 ≤ r) :
    OddAutSylowFixAt r Y := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.AGLEmbedding.ParabAutIrr.exists_equiv_projSp hC
  have hn : 2 ≤ n := hC.1.2.2.1
  have hf : 1 ≤ f := hC.1.2.1
  exact OddAutSylowFixAt.of_mulEquiv e.symm
    (oddAutSylowFixAt_statedProjStatedSp hcard hf hn hr hr5)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
