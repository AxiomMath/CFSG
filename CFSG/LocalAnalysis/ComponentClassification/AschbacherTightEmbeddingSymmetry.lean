module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingSylow
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

theorem complement_normalizer_factor_lower_bound {G : Type*} [Group G] [Finite G]
    (P Q T S : Subgroup G) (g : G) (hP : rightConjugate Q g = P)
    (htight : TightlyEmbedded P)
    (hodd : Odd (Nat.card ↥(P ⊓ Q)))
    (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G)) (hTP : T ≤ P)
    (hTS : T ≤ S) (hS : S ≤ Q ⊔ T) (htwoS : IsPGroup 2 S)
    (R : Sylow 2 Q) (hR : sylowImage Q R = S ⊓ Q) :
    Nat.card T ≤ Nat.card ↥(relativeNormalizer T S ⊓ Q) := by
  rcases complement_normalizer_alternative P Q T S htight hodd hnormalizes hTP hTS hS htwoS
    with hnormal | ⟨homomorphism, hinjective⟩
  · have hnormalizerEq : relativeNormalizer T S = S := inf_eq_right.mpr hnormal
    rw [hnormalizerEq, ← hR]
    exact two_subgroup_card_le_conjugate_sylow Q P T g hP (htwoS.to_le hTS) hTP R
  · exact (Nat.card_le_card_of_injective homomorphism hinjective).trans
      (Subgroup.card_le_card_group _)

theorem overlap_normalizer_factor_upper_bound {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hne : sylowImage _ T ≠ ⊥) :
    Nat.card ↥(relativeNormalizer (sylowImage _ T) (sylowImage _ S) ⊓ Q) ≤
      Nat.card (sylowImage _ T) := by
  classical
  let P : Subgroup G := rightConjugate Q g
  let A : Subgroup G := sylowImage (P ⊓ Subgroup.normalizer (Q : Set G)) T
  let X : Subgroup G := sylowImage (Q ⊔ A) S
  let C : Subgroup G := relativeNormalizer A X ⊓ Q
  have htwoA : IsPGroup 2 A := sylowImage_isPGroup _ T
  have htwoX : IsPGroup 2 X := sylowImage_isPGroup _ S
  have htwoC : IsPGroup 2 C := htwoX.to_le (inf_le_left.trans inf_le_right)
  change Nat.card C ≤ Nat.card A
  by_cases hCbot : C = ⊥
  · rw [hCbot, Subgroup.card_bot]
    exact Nat.card_pos
  have hAP : A ≤ P := overlap_sylow_le_conjugate Q g T
  have hAQnormal : A ≤ Subgroup.normalizer (Q : Set G) := overlap_sylow_le_normalizer Q g T
  have hCQ : C ≤ Q := inf_le_right
  have hCnormalA : C ≤ Subgroup.normalizer (A : Set G) := inf_le_left.trans inf_le_left
  have htightP : TightlyEmbedded P := rightConjugate_tightlyEmbedded Q htight g
  have hCnormalP : C ≤ Subgroup.normalizer (P : Set G) :=
    hCnormalA.trans (normalizer_two_subgroup_le P A htightP htwoA hAP hne)
  have hAnormalOpposite : A ≤ Subgroup.normalizer
      ((Q ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) := by
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAQnormal ha, Subgroup.le_normalizer (Subgroup.le_normalizer (hAP ha))⟩
  obtain ⟨D, hD⟩ := TwoActionInvariantSylow.subgroup
    (Q ⊓ Subgroup.normalizer (P : Set G)) A htwoA hAnormalOpposite
  let B : Subgroup G := sylowImage (Q ⊓ Subgroup.normalizer (P : Set G)) D
  have hBQ : B ≤ Q := (sylowImage_le _ D).trans inf_le_left
  have hBnormalP : B ≤ Subgroup.normalizer (P : Set G) := (sylowImage_le _ D).trans inf_le_right
  have hAnormalB : A ≤ Subgroup.normalizer (B : Set G) := hD
  have hCB : Nat.card C ≤ Nat.card B :=
    two_subgroup_card_le_sylowImage _ C htwoC (le_inf hCQ hCnormalP) D
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hCB
    exact hCbot (C.eq_bot_of_card_le hCB)
  have htwoAB : IsPGroup 2 ↥(A ⊔ B : Subgroup G) := by
    rw [sup_comm]
    exact (sylowImage_isPGroup _ D).to_sup_of_normal_left' htwoA hAnormalB
  obtain ⟨F, hF⟩ := exists_sylowImage_containing (P ⊔ B) (A ⊔ B) htwoAB
    (sup_le (hAP.trans le_sup_left) le_sup_right)
  obtain ⟨R, hR⟩ := sylow_product_base_intersection P B hBnormalP F
  have hodd : Odd (Nat.card ↥(Q ⊓ P)) := htight.2 g hg
  have hboundB := complement_normalizer_factor_lower_bound Q P B (sylowImage _ F)
    g⁻¹ (rightConjugate_inv_cancel Q g) htight hodd hBnormalP hBQ
      (le_sup_right.trans hF) (sylowImage_le _ F) (sylowImage_isPGroup _ F) R hR
  have hfactorLe : relativeNormalizer B (sylowImage _ F) ⊓ P ≤
      P ⊓ Subgroup.normalizer (Q : Set G) := by
    intro p hp
    exact ⟨hp.2, normalizer_two_subgroup_le Q B htight (sylowImage_isPGroup _ D) hBQ
      hBne hp.1.1⟩
  have hboundFactor := two_subgroup_card_le_sylowImage _
    (relativeNormalizer B (sylowImage _ F) ⊓ P)
      ((sylowImage_isPGroup _ F).to_le (inf_le_left.trans inf_le_right)) hfactorLe T
  exact hCB.trans (hboundB.trans hboundFactor)

theorem overlap_normalizer_factor_card {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hTS : sylowImage _ T ≤ sylowImage _ S) (hne : sylowImage _ T ≠ ⊥) :
    Nat.card ↥(relativeNormalizer (sylowImage _ T) (sylowImage _ S) ⊓ Q) =
      Nat.card (sylowImage _ T) := by
  apply le_antisymm (overlap_normalizer_factor_upper_bound Q htight g hg T S hne)
  obtain ⟨R, hR⟩ := sylow_product_base_intersection Q (sylowImage _ T)
    (overlap_sylow_le_normalizer Q g T) S
  have hodd : Odd (Nat.card ↥(rightConjugate Q g ⊓ Q)) := by
    rw [inf_comm]
    exact htight.2 g hg
  exact complement_normalizer_factor_lower_bound (rightConjugate Q g) Q
    (sylowImage _ T) (sylowImage _ S) g rfl (rightConjugate_tightlyEmbedded Q htight g)
      hodd (overlap_sylow_le_normalizer Q g T) (overlap_sylow_le_conjugate Q g T)
        hTS (sylowImage_le _ S) (sylowImage_isPGroup _ S) R hR

theorem overlap_normalizer_factor_equiv {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hTS : sylowImage _ T ≤ sylowImage _ S) (hne : sylowImage _ T ≠ ⊥) :
    Nonempty (sylowImage _ T ≃*
      ↥(relativeNormalizer (sylowImage _ T) (sylowImage _ S) ⊓ Q)) := by
  classical
  let A : Subgroup G := sylowImage
    (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) T
  let X : Subgroup G := sylowImage (Q ⊔ A) S
  let C : Subgroup G := relativeNormalizer A X ⊓ Q
  have hcard : Nat.card C = Nat.card A := overlap_normalizer_factor_card Q htight g hg T S hTS hne
  have hodd : Odd (Nat.card ↥(rightConjugate Q g ⊓ Q)) := by
    rw [inf_comm]
    exact htight.2 g hg
  rcases complement_normalizer_alternative (rightConjugate Q g) Q A X
    (rightConjugate_tightlyEmbedded Q htight g) hodd (overlap_sylow_le_normalizer Q g T)
      (overlap_sylow_le_conjugate Q g T) hTS (sylowImage_le _ S) (sylowImage_isPGroup _ S)
    with hnormal | ⟨homomorphism, hinjective⟩
  · have hrelativeEq : relativeNormalizer A X = X := inf_eq_right.mpr hnormal
    obtain ⟨R, hR⟩ := sylow_product_base_intersection Q A
      (overlap_sylow_le_normalizer Q g T) S
    have hCX : C = sylowImage Q R := by
      dsimp only [C]
      rw [hrelativeEq, hR]
    obtain ⟨D, hD⟩ := exists_sylowImage_containing (rightConjugate Q g) A
      (sylowImage_isPGroup _ T) (overlap_sylow_le_conjugate Q g T)
    have hsame := SubgroupSylowTransport.card_eq Q (rightConjugate Q g) (MulAut.conj g⁻¹) rfl R D
    have hAcard : Nat.card A = Nat.card (sylowImage (rightConjugate Q g) D) := by
      calc
        Nat.card A = Nat.card C := hcard.symm
        _ = Nat.card (sylowImage Q R) := congrArg (fun L : Subgroup G => Nat.card L) hCX
        _ = Nat.card (R : Subgroup Q) := sylowImage_card Q R
        _ = Nat.card (D : Subgroup (rightConjugate Q g)) := hsame
        _ = Nat.card (sylowImage (rightConjugate Q g) D) := (sylowImage_card _ D).symm
    have hAeq : A = sylowImage (rightConjugate Q g) D :=
      Subgroup.eq_of_le_of_card_ge hD hAcard.symm.le
    obtain ⟨e⟩ := sylowImage_equiv_conjugate Q (rightConjugate Q g) g rfl R D
    exact ⟨(MulEquiv.subgroupCongr hAeq).trans (e.symm.trans (MulEquiv.subgroupCongr hCX.symm))⟩
  · let f : A →* C := (Subgroup.center C).subtype.comp homomorphism
    have hf : Function.Injective f := (Subgroup.center C).subtype_injective.comp hinjective
    let := Fintype.ofFinite A
    let := Fintype.ofFinite C
    have hbijective : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, by simpa only [Nat.card_eq_fintype_card] using hcard.symm⟩
    exact ⟨MulEquiv.ofBijective f hbijective⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
