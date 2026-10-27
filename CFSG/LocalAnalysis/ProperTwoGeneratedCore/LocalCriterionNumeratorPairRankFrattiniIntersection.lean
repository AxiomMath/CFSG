module

import all CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionFourGroupCommutatorAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattiniAmbient

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini

open CFSG LocalCriterionGeometry LocalCriterionFourGroupCommutator
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

theorem ambient_local_commutator_le_centralizer (I : Subgroup G) (w t : G)
    (hwt : Commute w t) :
    rightInvolutionCommutatorSubgroup t (I ⊓ Subgroup.centralizer ({w} : Set G)) ≤
      Subgroup.centralizer ({w} : Set G) := by
  let C := Subgroup.centralizer ({w} : Set G)
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hwt.symm.eq
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨a, rfl⟩
  exact C.mul_mem (C.mul_mem (C.mul_mem (C.inv_mem htC)
    (C.inv_mem a.property.2)) htC) a.property.2

theorem cyclic_ambient_intersection (K P : Subgroup G) (hK : IsCyclic K) :
    IsCyclic (K.subgroupOf P) := by
  let := hK
  let : IsCyclic ((K.subgroupOf P).map P.subtype) := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact Subgroup.isCyclic_of_le inf_le_left
  exact isCyclic_of_injective (P.subtype.subgroupMap (K.subgroupOf P))
    (P.subtype.subgroupMap_injective (K.subgroupOf P) P.subtype_injective)

theorem ambient_frattini_fixed_eq_commutator_intersection [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (I P : Subgroup G) (hPI : P ≤ I) (hP : IsPGroup p P) (w t : G)
    (hwP : w ∈ Subgroup.normalizer (P : Set G))
    (htP : t ∈ Subgroup.normalizer (P : Set G))
    (hw : w ^ 2 = 1) (ht : orderOf t = 2) (hwt : Commute w t)
    (hinv : ambientFrattiniInversion P t htP) :
    let := normalizerFrattiniBaseAction P
    let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
    actorFixedSubgroup (I := P ⧸ frattini P)
        (⟨w, hwP⟩ : Subgroup.normalizer (P : Set G)) =
      ((rightInvolutionCommutatorSubgroup t
        (I ⊓ Subgroup.centralizer ({w} : Set G))).subgroupOf P).map
          (QuotientGroup.mk' (frattini P)) := by
  let := normalizerFrattiniBaseAction P
  let := frattiniQuotientAction (A := Subgroup.normalizer (P : Set G)) (P := P)
  let wN : Subgroup.normalizer (P : Set G) := ⟨w, hwP⟩
  let tN : Subgroup.normalizer (P : Set G) := ⟨t, htP⟩
  let K := rightInvolutionCommutatorSubgroup t (I ⊓ Subgroup.centralizer ({w} : Set G))
  have hwsq : wN ^ 2 = 1 := Subtype.ext hw
  have hcomm : Commute wN tN := Subtype.ext hwt.eq
  have hAP : actorCommutatorSubgroup tN (actorFixedSubgroup (I := P) wN) ≤
      K.subgroupOf P := by
    change actorCommutatorSubgroup tN (actorFixedSubgroup (I := P) wN) ≤
      K.comap P.subtype
    rw [← Subgroup.map_le_iff_le_comap]
    rw [ambient_fixed_commutator_map P w t hwP htP ht]
    exact right_involution_commutator_mono t (inf_le_inf hPI le_rfl)
  have hKP : K.subgroupOf P ≤ actorFixedSubgroup (I := P) wN := by
    intro a ha
    have haw : (a : G) ∈ Subgroup.centralizer ({w} : Set G) :=
      ambient_local_commutator_le_centralizer I w t hwt ha
    apply Subtype.ext
    change w * (a : G) * w⁻¹ = a
    rw [← Subgroup.mem_centralizer_singleton_iff.mp haw,
      mul_assoc, mul_inv_cancel, mul_one]
  apply le_antisymm
  · rw [frattini_fixed_eq_commutator_image hP hpodd wN tN hwsq hcomm hinv]
    exact Subgroup.map_mono hAP
  · rw [frattini_fixed_quotient_eq_image hP hpodd wN hwsq]
    exact Subgroup.map_mono hKP

end CFSG.ProperTwoGeneratedCore.LocalCriterionNumeratorPairRankFrattini
