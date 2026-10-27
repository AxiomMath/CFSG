module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem point_class_eq_full_conjugacy (s : G) :
    involutionPointClass s = conjugacyWithin (⊤ : Subgroup G) s := by
  ext v
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨⟨g, trivial⟩, hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g.val, hg⟩

theorem generated_commuting_involutions_isKleinFour
    (u t : G) (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : u ≠ t) (hcomm : Commute u t) :
    IsKleinFour (Subgroup.zpowers u ⊔ Subgroup.zpowers t : Subgroup G) := by
  have huu : u * u = 1 := by simpa only [hu, pow_two] using pow_orderOf_eq_one u
  have htt : t * t = 1 := by simpa only [ht, pow_two] using pow_orderOf_eq_one t
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    norm_num at hu
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    norm_num at ht
  let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  let F := CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions u t huu htt hcomm
  have huF : u ∈ F := by change u ∈ ({u * t, u, t, 1} : Set G); simp
  have htF : t ∈ F := by change t ∈ ({u * t, u, t, 1} : Set G); simp
  have huV : u ∈ V := (show Subgroup.zpowers u ≤ V from le_sup_left)
    (Subgroup.mem_zpowers u)
  have htV : t ∈ V := (show Subgroup.zpowers t ≤ V from le_sup_right)
    (Subgroup.mem_zpowers t)
  have hVF : V = F := by
    apply le_antisymm
    · exact sup_le (Subgroup.zpowers_le.mpr huF) (Subgroup.zpowers_le.mpr htF)
    · intro x hx
      change x ∈ ({u * t, u, t, 1} : Set G) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact V.mul_mem huV htV
      · exact huV
      · exact htV
      · exact V.one_mem
  change IsKleinFour V
  rw [hVF]
  exact CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    u t huu htt hu1 ht1 hut hcomm

theorem generated_commuting_involutions_elementary
    (u t : G) (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hut : u ≠ t) (hcomm : Commute u t) :
    let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
    Nat.card V = 4 ∧ IsElementaryAbelian 2 V := by
  let V := Subgroup.zpowers u ⊔ Subgroup.zpowers t
  let : IsKleinFour V := generated_commuting_involutions_isKleinFour u t hu ht hut hcomm
  refine ⟨IsKleinFour.card_four, ?_⟩
  exact { toIsMulCommutative := IsKleinFour.isMulCommutative
          exponent_dvd_p := by rw [IsKleinFour.exponent_two] }

theorem pair_stabilizer_not_distinguished [Finite G]
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (u : G) (huD : u ∈ pairPointStabilizer H beta) :
    u ∉ involutionPointClass z := by
  intro huclass
  have huniq := ((involution_point_unique_containment_action
    h.distinguished_mem h.distinguished_order).2 h.unique_containment).2.1
  obtain ⟨gamma, _, hgamma⟩ := huniq u huclass
  have ha : pointRightCosetMul H (rightCosetMk H 1) u = rightCosetMk H 1 :=
    (mem_point_right_stabilizer_iff H _ u).mp huD.1
  have hb : pointRightCosetMul H beta u = beta :=
    (mem_point_right_stabilizer_iff H beta u).mp huD.2
  exact hbeta ((hgamma beta hb).trans (hgamma _ ha).symm)

theorem full_point_classes_disjoint
    (u z : G) (huz : u ∉ involutionPointClass z) :
    Disjoint (involutionPointClass u) (involutionPointClass z) := by
  apply Set.disjoint_left.mpr
  intro s hsU hsZ
  obtain ⟨g, hg⟩ := hsU
  have huZ := pointClass_right_conjugate_mem hsZ g⁻¹
  apply huz
  rw [← hg] at huZ
  simpa only [rightConjugateElem, mul_inv_rev, inv_inv, mul_assoc,
    mul_inv_cancel_left, mul_inv_cancel, mul_one] using huZ

theorem full_point_classes_ne
    (u z : G) (huz : u ∉ involutionPointClass z) :
    involutionPointClass u ≠ involutionPointClass z := by
  intro heq
  exact huz (heq ▸ distinguished_mem_pointClass u)

theorem pair_stabilizer_element_ne_flip
    {H : Subgroup G} {z t : G} (beta : rightCosetSpace H)
    (hbeta : beta ≠ rightCosetMk H 1) (ht : t ∈ rightPairFlipFiber H z beta)
    (u : G) (huD : u ∈ pairPointStabilizer H beta) : u ≠ t := by
  intro hut
  have htD : t ∈ pairPointStabilizer H beta := hut ▸ huD
  exact pair_flip_not_mem_point hbeta ht (pairPointStabilizer_le_point H beta htD)

end CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeIdentity
