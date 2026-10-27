module

public import CFSG.Blueprint.Catalog

import CFSG.Adapters.LieModelOrders
import CFSG.ClassicalInvolution.RouteD.TWRExoticArith
import CFSG.GH74.GLS.Stage4.T2NumGtIvkExp
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.GH74.BNPair.Defs
import CFSG.GH74.GLS.IVK.L2.F1
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.RootCommutator
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import Certificates.Certificate1
import Certificates.Certificate2
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Blueprint

open CFSG.Open

variable {X : Type} [Group X]

private theorem matrix_pow_p_eq_one_of_pow_prime_pow {K : Type} [Field K] {p : ℕ} [Fact p.Prime]
    [CharP K p] (hp3 : 3 ≤ p) (M : Matrix (Fin 3) (Fin 3) K) (k : ℕ)
    (hMk : M ^ (p ^ k) = 1) : M ^ p = 1 := by
  have hN : (M - 1) ^ (p ^ k) = 0 := by
    rw [sub_pow_char_pow_of_commute p k (Commute.one_right M), hMk, one_pow, sub_self]
  have hnil : IsNilpotent (M - 1) := ⟨p ^ k, hN⟩
  have hnil' : IsNilpotent (Matrix.toLin' (M - 1)) := (Matrix.isNilpotent_toLin'_iff _).2 hnil
  have hch := IsNilpotent.charpoly_eq_X_pow_finrank hnil'
  have hca := LinearMap.aeval_self_charpoly (Matrix.toLin' (M - 1))
  rw [hch] at hca
  have hfr : Module.finrank K (Fin 3 → K) = 3 := by simp
  rw [hfr] at hca
  simp only [map_pow, Polynomial.aeval_X] at hca
  have h3 : (M - 1) ^ 3 = 0 := by
    have h1 : Matrix.toLinAlgEquiv' (R := K) ((M - 1) ^ 3) = 0 := by
      rw [map_pow]
      exact hca
    exact (map_eq_zero_iff _ (Matrix.toLinAlgEquiv' (R := K)).injective).1 h1
  have hNp : (M - 1) ^ p = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hp3
    rw [pow_add, h3, zero_mul]
  have hMp : M ^ p = 1 := by
    have h1 : (M - 1 + 1) ^ p = (M - 1) ^ p + 1 ^ p :=
      add_pow_char_of_commute p (Commute.one_right _)
    rw [sub_add_cancel, hNp, one_pow, zero_add] at h1
    exact h1
  exact hMp

private theorem statedSU_pow_p_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hp3 : 3 ≤ p) (x : StatedSU 3 (p ^ f) K) (k : ℕ)
    (hx : x ^ p ^ k = 1) : x ^ p = 1 := by
  apply Subtype.ext
  apply Units.ext
  have hmat : (((x : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) ^ (p ^ k) = 1 := by
    have h := congrArg (fun g : StatedSU 3 (p ^ f) K =>
      (((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)) hx
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h
  have hpow : (((x : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) ^ p = 1 :=
    matrix_pow_p_eq_one_of_pow_prime_pow hp3 _ k hmat
  simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using hpow

theorem LieModel.pow_eq_one_of_psl3 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSL 3 p f)
    (hp2 : p ≠ 2) {x : X} (hx : ∃ k : ℕ, x ^ p ^ k = 1) : x ^ p = 1 := by
  have hp : p.Prime := h.admissible.1
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite X := Finite.of_equiv (StatedProj (StatedSL 3 K)) e.toEquiv.symm
  have hLn : CFSG.GH74.GLS.IVK.IsLnEps 3 X 1 (p ^ f) :=
    Or.inl ⟨rfl, K, hfield, hfinite, hK, ⟨e⟩⟩
  obtain ⟨k, hk⟩ := hx
  exact CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.exp_p_of_isSLnEps_or_isLnEps hp hp2 (Or.inr hLn) x k hk

theorem LieModel.pow_eq_one_of_psu3 {X : Type} [Group X] {p f : ℕ} (h : LieModel X .PSU 3 p f)
    (hp2 : p ≠ 2) {x : X} (hx : ∃ k : ℕ, x ^ p ^ k = 1) : x ^ p = 1 := by
  have hp : p.Prime := h.admissible.1
  have hf : 1 ≤ f := h.admissible.2.1
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK' : Nat.card K = p ^ (2 * f) := by
    rw [hK, ← pow_mul, Nat.mul_comm]
  have hchar : CharP K p :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.charP_of_natCard_eq_pow hp hK'
  haveI : CharP K p := hchar
  let H := StatedSU 3 (p ^ f) K
  let N := (StatedScalars (Fin 3) K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hS : ∀ y : H, ∀ k : ℕ, y ^ p ^ k = 1 → y ^ p = 1 :=
    fun y k hy => statedSU_pow_p_eq_one hp3 y k hy
  have hker : Nat.Coprime (Nat.card π.ker) p := by
    rw [show π.ker = N from QuotientGroup.ker_mk' N]
    have hcardN : Nat.card N = Nat.gcd 3 (p ^ f + 1) :=
      (CFSG.LinearGroups.unitary_scalar_kernel hp hK (n := 3) (by norm_num)).2.2
    rw [hcardN]
    by_cases hp3' : p = 3
    · subst hp3'
      have hnot : ¬ (3 : ℕ) ∣ 3 ^ f + 1 := by
        intro hd
        have hdiv : (3 : ℕ) ∣ 3 ^ f := dvd_pow_self 3 (by omega)
        have h1 : (3 : ℕ) ∣ 1 := by
          have h := Nat.dvd_sub hd hdiv
          rwa [show 3 ^ f + 1 - 3 ^ f = 1 by omega] at h
        exact Nat.prime_three.not_dvd_one h1
      have hc : Nat.Coprime 3 (3 ^ f + 1) :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnot
      rw [hc.gcd_eq_one]
      exact Nat.coprime_one_left 3
    · have h3p : Nat.Coprime 3 p :=
        (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3')
      have h := h3p.gcd_left (p ^ f + 1)
      rwa [Nat.gcd_comm] at h
  obtain ⟨k, hk⟩ := hx
  have hy : (e x) ^ (p ^ k) = 1 := by rw [← map_pow, hk, map_one]
  have hres : (e x) ^ p = 1 :=
    CFSG.GH74.GLS.IVK.Proofs2.Ivk41R.pow_p_of_surjective_coprime π hπ hker hS (e x) k hy
  apply e.injective
  rw [map_pow, hres, map_one]

theorem LieModel.factorization_card_psl3 {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSL 3 p f) : (Nat.card X).factorization p = 3 * f := by
  have hp : p.Prime := h.admissible.1
  have hf : 1 ≤ f := h.admissible.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, h.card_eq_lieOrd (by norm_num)]
  change padicValNat p (ordA 2 (p ^ f)) = 3 * f
  rw [CFSG.ClassicalInvolution.RouteD.TWR.v_ordA2 (by omega)]
  omega

theorem LieModel.factorization_card_psu3 {X : Type} [Group X] {p f : ℕ}
    (h : LieModel X .PSU 3 p f) : (Nat.card X).factorization p = 3 * f := by
  have hp : p.Prime := h.admissible.1
  have hf : 1 ≤ f := h.admissible.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, h.card_eq_lieOrd (by norm_num)]
  change padicValNat p (ordTwistedA 2 (p ^ f)) = 3 * f
  rw [CFSG.ClassicalInvolution.RouteD.TWR.v_ordTA2 (by omega)]
  omega

end CFSG.Blueprint
