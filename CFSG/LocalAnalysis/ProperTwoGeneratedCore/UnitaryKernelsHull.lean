module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairCentralizerModel

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryKernels

open CFSG.Open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.RankOnePair

universe u

variable {G : Type u} [Group G]

structure UnitaryKernelHullData (H : Subgroup G) (z w : G) (U : Subgroup G) (q : ℕ) : Prop where
  root_set : (U : Set G) = {1} ∪
    (involutionPointClass z ∩ (Subgroup.centralizer ({w} : Set G) : Set G) ∩ (H : Set G))
  le_hull : U ≤ localInvolutionPointHull z w
  sq_eq_one : ∀ x ∈ U, x ^ 2 = 1
  card : Nat.card U = q
  core_central : CFSG.oddCore (localInvolutionPointHull z w) ≤
    Subgroup.center (localInvolutionPointHull z w)
  core_odd : Odd (Nat.card (CFSG.oddCore (localInvolutionPointHull z w)))
  ker : ∀ x : Subgroup.centralizer ({w} : Set G),
    originalCentralizerHullQuotientConjugation z w x = 1 ↔
      (x : G) ∈ Subgroup.centralizer (localInvolutionPointHull z w : Set G)
  involutions : {x : G | x ∈ Subgroup.centralizer ({w} : Set G) ∧
    x ∈ Subgroup.centralizer (localInvolutionPointHull z w : Set G) ∧ orderOf x = 2} = {w}
  not_mem : w ∉ localInvolutionPointHull z w
  sylow : ∀ R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H),
    UnitaryKernelRootData H z w U
      ((R : Subgroup _).map (localInvolutionPointHull z w ⊓ H).subtype) q

variable [Finite G]

theorem unitaryKernelHullData_of_pair
    {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (K : Type u) [Group K] [Finite K], Nat.card K < Nat.card G →
      2 ≤ twoRank K → (∃ A : Subgroup K, fusionStronglyEmbedded A) → R1Full K)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (hpairRank : twoRank (pairPointStabilizer H beta) = 1)
    {w : G} (hwE : w ∈ pairPointStabilizer H beta) (hw : orderOf w = 2) (hwz : Commute w z)
    (hescape : ¬ Subgroup.centralizer ({w} : Set G) ≤ H)
    (hfix : Nat.card (elementFixedSet H w) = Nat.card (originalPointRoot H z w) ^ 3 + 1) :
    UnitaryKernelHullData H z w (originalPointRoot H z w) (Nat.card (originalPointRoot H z w)) := by
  classical
  obtain ⟨R₀⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w ⊓ H)) := inferInstance
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))) := inferInstance
  obtain ⟨-, -, hrank, -⟩ := rank_one_pair_centralizer_model_and_two_global_involution_classes
    h hcomm hsmallerR1 beta hbeta hpairRank hwE hw hwz hescape R₀ T₀
  obtain ⟨hker, hroot, -, -, -⟩ := unique_rank_two_centralizer_hull_involutions_and_local_orbits
    h hcomm hsmallerR1 beta hbeta hpairRank w hwE hw hwz hescape hrank
  dsimp only [rankTwoCentralizerKernelData] at hker
  dsimp only [rankTwoCentralizerRootData] at hroot
  obtain ⟨hcentral, hodd, -, hinv, hkerEq, -, hnot, -⟩ := hker
  obtain ⟨-, hUL, -, -, hUset, hUset', hU4, -, -, -, -, hborel, -, hfixL, -, -,
    a, i', ha, -, hUa, -, -, hfix', -, hmodel⟩ := hroot
  have hii : i' = 3 := by
    have h2 : 2 ≤ Nat.card (originalPointRoot H z w) := by omega
    exact Nat.pow_right_injective h2 (by simp only; omega)
  subst hii
  have hUsq : ∀ x ∈ originalPointRoot H z w, x ^ 2 = 1 := by
    intro x hx
    rw [← SetLike.mem_coe, hUset'] at hx
    rcases hx with hx | ⟨-, -, hx2⟩
    · rw [Set.mem_singleton_iff.mp hx, one_pow]
    · rw [← hx2]
      exact pow_orderOf_eq_one x
  have hqeven : Even (Nat.card (originalPointRoot H z w)) := by
    rw [hUa]
    exact (Nat.even_pow' (by omega)).mpr even_two
  have horbit : Odd (Nat.card (numeratorRightOrbit H (localInvolutionPointHull z w)
      (rightCosetMk H 1))) := by
    rw [← hfixL, hfix]
    exact (hqeven.pow_of_ne_zero (by norm_num)).add_one
  have hrootJ : ∀ S : Sylow 2 (hullQuotient (localInvolutionPointHull z w)),
      Nat.card (S : Subgroup (hullQuotient (localInvolutionPointHull z w))) =
          Nat.card (originalPointRoot H z w) ^ 3 ∧
        UnitaryRootCenterData (S : Subgroup (hullQuotient (localInvolutionPointHull z w)))
          ((CFSG.omega₁ (G := (S : Subgroup (hullQuotient (localInvolutionPointHull z w))))
            (p := 2)).map
            (S : Subgroup (hullQuotient (localInvolutionPointHull z w))).subtype) := by
    intro S
    rcases hmodel with ⟨hi1, -⟩ | ⟨hi2, -⟩ | ⟨-, E, hE, hEfin, A, hA, hEcard, hfixedE, ⟨e⟩⟩
    · omega
    · omega
    · rw [hUa]
      exact unitaryRootCenterData_of_mulEquiv A a ha hEcard hfixedE hA e S
  refine ⟨hUset, hUL, hUsq, rfl, hcentral, hodd, fun x => ?_, hinv, hnot, fun R => ?_⟩
  · rw [← MonoidHom.mem_ker, hkerEq]
    rfl
  · exact unitaryKernelRootData_of_borel hcentral hodd hborel horbit hUL hUset' hrootJ R

end CFSG.ProperTwoGeneratedCore.UnitaryKernels
