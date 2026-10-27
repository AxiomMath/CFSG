module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniAmbient
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankLocalCommutator

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
open CFSG.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem ambient_odd_inversion_subgroup_eq_right_commutator
    (C J : Subgroup G) (hodd : Odd (Nat.card C))
    (t : G) (ht : orderOf t = 2)
    (htC : t ∈ Subgroup.normalizer (C : Set G))
    (hJset : (J : Set G) = {x : G | x ∈ C ∧ rightConjugateElem x t = x⁻¹}) :
    J = rightInvolutionCommutatorSubgroup t C ∧ (J.subgroupOf C).Normal := by
  let := normalizerFrattiniBaseAction C
  let A := Subgroup.normalizer (C : Set G)
  let b : A := ⟨t, htC⟩
  let K := J.subgroupOf C
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two ht
  have hb : b * b = 1 := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using
      (orderOf_eq_prime_iff.mp ht).1
  let : IsInvariant A C (⊤ : Subgroup C) :=
    ⟨fun _ _ => by simp⟩
  have hK : ∀ x : C, x ∈ K ↔ x ∈ (⊤ : Subgroup C) ∧ b • x = x⁻¹ := by
    intro x
    change (x : G) ∈ J ↔ x ∈ (⊤ : Subgroup C) ∧ b • x = x⁻¹
    rw [show (x : G) ∈ J ↔ (x : G) ∈ C ∧
      rightConjugateElem (x : G) t = (x : G)⁻¹ from Set.ext_iff.mp hJset (x : G)]
    constructor
    · intro hx
      refine ⟨Subgroup.mem_top _, Subtype.ext ?_⟩
      change t * (x : G) * t⁻¹ = (x : G)⁻¹
      simpa only [rightConjugateElem, htinv] using hx.2
    · intro hx
      refine ⟨x.property, ?_⟩
      have hact := congrArg Subtype.val hx.2
      change t * (x : G) * t⁻¹ = (x : G)⁻¹ at hact
      simpa only [rightConjugateElem, htinv] using hact
  obtain ⟨heq, hnormal⟩ := odd_local_inversion_subgroup_eq_commutator hodd b hb ⊤ K hK
  have hKn : K.Normal := by
    have hN : (⊤ : Subgroup C) ≤ Subgroup.normalizer (K : Set C) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hnormal
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique hN)
  have hfixed : actorFixedSubgroup (I := C) (1 : A) = ⊤ := by
    ext x
    simp only [mem_actorFixedSubgroup, one_smul, Subgroup.mem_top]
  have hcent : Subgroup.centralizer ({(1 : G)} : Set G) = ⊤ := by
    ext x
    simp only [Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul,
      Subgroup.mem_top]
  have hmap := ambient_fixed_commutator_map C 1 t
    (Subgroup.normalizer (C : Set G)).one_mem htC ht
  change (actorCommutatorSubgroup b (actorFixedSubgroup (I := C) (1 : A))).map
    C.subtype = rightInvolutionCommutatorSubgroup t
      (C ⊓ Subgroup.centralizer ({(1 : G)} : Set G)) at hmap
  rw [hfixed, hcent, inf_top_eq] at hmap
  have hJC : J ≤ C := fun x hx => ((Set.ext_iff.mp hJset x).mp hx).1
  have hJmap : K.map C.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJC
  exact ⟨hJmap.symm.trans ((congrArg (fun Q : Subgroup C => Q.map C.subtype) heq).trans hmap), hKn⟩

theorem original_rank_two_local_cyclic_commutator_and_normality
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (t : G) (ht : t ∈ rightPairFlipFiber H z beta)
    (w : G) (hw : orderOf w = 2) (hwz : Commute w z) (hwt : Commute w t)
    (hrank : 2 ≤ twoRank (localInvolutionPointHull z w)) :
    let C := pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)
    let J := rightInvolutionCommutatorSubgroup t C
    (J : Set G) = {x : G | x ∈ C ∧ rightConjugateElem x t = x⁻¹} ∧
      IsCyclic J ∧ Nat.card J = Nat.card ↥(conjugacyWithin H z ∩
        (Subgroup.centralizer ({w} : Set G) : Set G)) ∧ (J.subgroupOf C).Normal := by
  let C := pairOddCore H beta ⊓ Subgroup.centralizer ({w} : Set G)
  obtain ⟨J, hJset, hJcyclic, hJcard⟩ :=
    original_rank_two_entire_local_inversion_cyclic_of_fixed_root_card h hcomm hsmallerR1
      S hzS hzcenter beta hbeta t ht w hw hwz hwt hrank
  have hodd : Odd (Nat.card C) := (pairOddCore_odd H beta).of_dvd_nat
    (Subgroup.card_dvd_of_le (show C ≤ pairOddCore H beta from inf_le_left))
  have htC : t ∈ Subgroup.normalizer (C : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨pair_flip_normalizes_ambient_odd_core h.local_datum.distinguished_order hbeta ht,
        commute_normalizes_centralizer t w hwt.symm⟩
  have htorder := order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
  obtain ⟨heq, hnormal⟩ :=
    ambient_odd_inversion_subgroup_eq_right_commutator C J hodd t htorder htC hJset
  dsimp only
  rw [← heq]
  exact ⟨hJset, hJcyclic, hJcard, hnormal⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
