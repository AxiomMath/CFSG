module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow

open CFSG.Open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem conjugacyWithin_card_eq_centralizer_index (J : Subgroup G) (t : G) :
    Nat.card (conjugacyWithin J t) =
      ((Subgroup.centralizer ({t} : Set G)).subgroupOf J).index := by
  let f : J →* ConjAct G := ConjAct.toConjAct.toMonoidHom.comp J.subtype
  let : MulAction J G := MulAction.compHom G f
  have hclass : conjugacyWithin J t = MulAction.orbit J t := by
    ext s
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨j⁻¹, ?_⟩
      change (j : G)⁻¹ * t * (j : G)⁻¹⁻¹ = s
      simpa only [inv_inv] using hj
    · rintro ⟨j, hj⟩
      refine ⟨j⁻¹, ?_⟩
      change (j : G) * t * (j : G)⁻¹ = s at hj
      change (j : G)⁻¹⁻¹ * t * (j : G)⁻¹ = s
      simpa only [inv_inv] using hj
  have hstab : MulAction.stabilizer J t =
      (Subgroup.centralizer ({t} : Set G)).subgroupOf J := by
    ext j
    rw [MulAction.mem_stabilizer_iff]
    change ((j : G) * t * (j : G)⁻¹ = t) ↔
      ((j : G) ∈ Subgroup.centralizer ({t} : Set G))
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hj
      have hh := congrArg (fun x : G => x * (j : G)) hj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
    · intro hj
      rw [hj, mul_assoc, mul_inv_cancel, mul_one]
  rw [hclass]
  have hc := Nat.card_congr (MulAction.orbitEquivQuotientStabilizer J t)
  rwa [hstab, ← Subgroup.index_eq_card] at hc

theorem conjugacyWithin_card_odd (J : Subgroup G) (hJodd : Odd (Nat.card J)) (t : G) :
    Odd (Nat.card (conjugacyWithin J t)) := by
  rw [conjugacyWithin_card_eq_centralizer_index]
  exact hJodd.of_dvd_nat (Subgroup.index_dvd_card _)

theorem local_embedding_index_odd [Finite G] {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) : Odd H.index := by
  let Z := Subgroup.zpowers z
  let : MulAction Z (conjugateCosetSpace H) :=
    MulAction.compHom (conjugateCosetSpace H) Z.subtype
  let base : conjugateCosetSpace H := QuotientGroup.mk 1
  have hzbase : z • base = base := (point_fixed_coset_unique h base).mpr rfl
  have hbase : base ∈ MulAction.fixedPoints Z (conjugateCosetSpace H) := by
    intro g
    have hZle : Z ≤ MulAction.stabilizer G base :=
      Subgroup.zpowers_le.mpr ((MulAction.mem_stabilizer_iff).mpr hzbase)
    exact (MulAction.mem_stabilizer_iff).mp (hZle g.property)
  have hpoint : ∀ omega ∈ MulAction.fixedPoints Z (conjugateCosetSpace H), omega = base := by
    intro omega homega
    apply (point_fixed_coset_unique h omega).mp
    exact homega ⟨z, Subgroup.mem_zpowers z⟩
  have hfixedcard : Nat.card (MulAction.fixedPoints Z (conjugateCosetSpace H)) = 1 := by
    let : Nonempty (MulAction.fixedPoints Z (conjugateCosetSpace H)) := ⟨⟨base, hbase⟩⟩
    let : Subsingleton (MulAction.fixedPoints Z (conjugateCosetSpace H)) :=
      ⟨fun a b => Subtype.ext ((hpoint a a.property).trans (hpoint b b.property).symm)⟩
    exact Nat.card_unique
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, h.distinguished_order, pow_one])
  have hmod := hZtwo.card_modEq_card_fixedPoints (conjugateCosetSpace H)
  rw [hfixedcard] at hmod
  rw [Subgroup.index_eq_card, Nat.odd_iff]
  exact hmod

theorem conjugacyWithin_nonempty (H : Subgroup G) (z : G) :
    (conjugacyWithin H z).Nonempty := by
  refine ⟨z, ⟨1, ?_⟩⟩
  simp only [Subgroup.coe_one, inv_one, one_mul, mul_one]

theorem subgroup_pair_flip_fiber_card_odd [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G))
    {beta : rightCosetSpace (H.subgroupOf A)}
    (hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1) {t : A}
    (ht : t ∈ rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) :
    Odd (Nat.card (rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta)) := by
  rw [subgroup_pair_flip_fiber_eq_odd_class h hzA S hzS hzcenter hbeta ht]
  exact conjugacyWithin_card_odd _
    (subgroup_pair_odd_intersection_normal_odd h hzA hbeta ht).2 t

theorem subgroup_point_class_card_odd [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (hescapeA : ¬ A ≤ H) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    Odd (Nat.card (conjugacyWithin (H.subgroupOf A) (⟨z, hzA⟩ : A))) := by
  classical
  have hA := local_datum_subgroup_inheritance h A hzA hescapeA
  obtain ⟨a, haA, haH⟩ : ∃ a : G, a ∈ A ∧ a ∉ H := by
    by_contra hnone
    apply hescapeA
    intro a haA
    by_contra haH
    exact hnone ⟨a, haA, haH⟩
  let aA : A := ⟨a, haA⟩
  let beta := rightCosetMk (H.subgroupOf A) aA
  have hbeta : beta ≠ rightCosetMk (H.subgroupOf A) 1 := by
    intro heq
    have hrel : QuotientGroup.rightRel (H.subgroupOf A) aA 1 := Quotient.exact heq
    rw [QuotientGroup.rightRel_apply] at hrel
    have ha : aA ∈ H.subgroupOf A := (H.subgroupOf A).inv_mem_iff.mp
      (by simpa only [one_mul] using hrel)
    exact haH ha
  have hcard := (involution_point_uniform_pair_flips hA beta hbeta).1
  have hpositive : 0 < Nat.card (rightPairFlipFiber (H.subgroupOf A) (⟨z, hzA⟩ : A) beta) := by
    rw [hcard]
    let : Nonempty (conjugacyWithin (H.subgroupOf A) (⟨z, hzA⟩ : A)) :=
      (conjugacyWithin_nonempty _ _).to_subtype
    exact Nat.card_pos
  obtain ⟨t, ht⟩ := (Nat.card_pos_iff.mp hpositive).1
  rw [← hcard]
  exact subgroup_pair_flip_fiber_card_odd h hzA S hzS hzcenter hbeta ht

theorem pointClass_card_factorization_with_conjugacyWithin [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) :
    Nat.card (involutionPointClass z) = H.index * Nat.card (conjugacyWithin H z) := by
  have hclass : {t : G | ∃ g : G, g ∈ H ∧ rightConjugateElem z g = t} =
      conjugacyWithin H z := by
    ext t
    constructor
    · rintro ⟨g, hg, hgt⟩
      exact ⟨⟨g, hg⟩, hgt⟩
    · rintro ⟨g, hgt⟩
      exact ⟨g, g.property, hgt⟩
  rw [pointClass_card_factorization h, hclass]

theorem subgroup_full_class_card_odd [Finite G]
    {H A : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z) (hzA : z ∈ A)
    (hescapeA : ¬ A ≤ H) (S : Sylow 2 G) (hzS : z ∈ (S : Subgroup G))
    (hzcenter : (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G)) :
    Odd (Nat.card (involutionPointClass (⟨z, hzA⟩ : A))) := by
  have hA := local_datum_subgroup_inheritance h A hzA hescapeA
  rw [pointClass_card_factorization_with_conjugacyWithin hA]
  exact (local_embedding_index_odd hA).mul
    (subgroup_point_class_card_odd h hzA hescapeA S hzS hzcenter)

end CFSG.ProperTwoGeneratedCore.LocalCriterionSubgroupSylow
