module

public import CFSG.LocalAnalysis.ComponentClassification.TwoActionSylowResidual
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionZStarEscape
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFusionEscape
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionEqualDisplacement

public section

open CFSG.Open

namespace CFSG.ComponentClassification.TwoActionProperEmbedding

theorem embedding {G : Type*} [Group G] [Finite G] (ambient acting intersection : Subgroup G)
    (hintersection : intersection ≤ ambient) (htwo : IsPGroup 2 acting)
    (hdisjoint : Disjoint ambient acting)
    (hnormalizesAmbient : acting ≤ Subgroup.normalizer (ambient : Set G))
    (hnormalizesIntersection : acting ≤ Subgroup.normalizer (intersection : Set G))
    (hcentralizers : ∀ member ∈ acting, member ≠ 1 →
      Subgroup.centralizer {member} ⊓ ambient ≤ intersection)
    (hcommutator : ⁅acting, intersection⁆ ≤
      (componentClassificationOddCore intersection).map intersection.subtype)
    (hproper : intersection ⊔ (componentClassificationOddCore ambient).map ambient.subtype ≠ ambient) :
    IsMulCommutative acting ∧ ∃ homomorphism : acting →* intersection, Function.Injective homomorphism := by
  classical
  by_contra hfailure
  have hnontrivial : Nontrivial acting := by
    by_contra hnot
    have hsub : Subsingleton acting := not_nontrivial_iff_subsingleton.mp hnot
    apply hfailure
    refine ⟨isMulCommutative_iff.mpr (fun first second => hsub.elim _ _), 1, ?_⟩
    intro first second heq
    exact hsub.elim first second
  let : Nontrivial acting := hnontrivial
  obtain ⟨first, second, hequal, hcentral, hnormalizerLe⟩ :=
    TwoActionSylowResidual.residual ambient acting intersection hintersection htwo hdisjoint
      hnormalizesAmbient hnormalizesIntersection hcentralizers hcommutator (not_and_or.mp hfailure)
  let firstImage := (first : Subgroup intersection).map intersection.subtype
  let secondImage := (second : Subgroup ambient).map ambient.subtype
  have hcentralizes : acting ≤ Subgroup.centralizer (secondImage : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcentral
  have hfirstCentralizes : acting ≤ Subgroup.centralizer (firstImage : Set G) := by
    change firstImage = secondImage at hequal
    rw [hequal]
    exact hcentralizes
  have hcenterNontrivial := htwo.center_nontrivial
  let : Nontrivial (Subgroup.center acting) := hcenterNontrivial
  have hcenterTwo : IsPGroup 2 (Subgroup.center acting) := htwo.to_subgroup _
  have hcenterEven : 2 ∣ Nat.card (Subgroup.center acting) := by
    rcases hcenterTwo.card_eq_or_dvd with hone | hdivides
    · have hbot := (Subgroup.center acting).eq_bot_iff_card.mpr hone
      exact ((Subgroup.center acting).nontrivial_iff_ne_bot.mp hcenterNontrivial hbot).elim
    · exact hdivides
  obtain ⟨central, horder⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center acting) 2 hcenterEven
  have hcentralOrder : orderOf central.val = 2 :=
    (orderOf_injective (Subgroup.center acting).subtype (Subgroup.center acting).subtype_injective central).trans horder
  have hcentralNe : central.val ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hcentralOrder
    omega
  obtain ⟨actor, hactor, hfused, hchanged⟩ := TwoActionZStarEscape.escape ambient acting intersection hintersection htwo
    hdisjoint hnormalizesAmbient hnormalizesIntersection hcentralizers hproper second hcentralizes
      central.val central.property hcentralOrder
  have hfusedFirst : actor * central.val.val * actor⁻¹ ∈ firstImage ⊔ acting := by
    change firstImage = secondImage at hequal
    rw [hequal]
    exact hfused
  obtain ⟨transporter, htransporter, houtside, hcontained⟩ := TwoActionFusionEscape.escape ambient acting intersection
    hintersection htwo hdisjoint hnormalizesAmbient hnormalizesIntersection hcentralizers hcommutator first
      hfirstCentralizes central.val central.property hcentralNe actor hactor hfusedFirst hchanged
  have hfirstIntersection : firstImage ≤ intersection := by
    rintro member ⟨lift, hlift, rfl⟩
    exact lift.property
  exact hfailure (TwoActionEqualDisplacement.abelian_embedding ambient acting intersection firstImage
    hfirstIntersection hintersection htwo hdisjoint hnormalizesAmbient hfirstCentralizes hcentralizers hcommutator
      transporter htransporter houtside hcontained)

end CFSG.ComponentClassification.TwoActionProperEmbedding
