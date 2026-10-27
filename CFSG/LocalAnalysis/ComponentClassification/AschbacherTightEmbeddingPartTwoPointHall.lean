module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPointRoot
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingInheritance
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoRootCenter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperCommutingImagesCenter

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.BenderSuzuki CFSG.ShultStronglyClosedTI
open CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G] [Finite G]

theorem normal_sylow_two_ambient_image_data
    (H : Subgroup G) (P : Sylow 2 H) (hP : (P : Subgroup H).Normal)
    (heven : Even (Nat.card H)) :
    let R := (P : Subgroup H).map H.subtype
    R ≤ H ∧ IsPGroup 2 R ∧ R.subgroupOf H = (P : Subgroup H) ∧
      (R.subgroupOf H).Normal ∧ R ≠ ⊥ := by
  let R := (P : Subgroup H).map H.subtype
  have hRH : R ≤ H := Subgroup.map_subtype_le _
  have hR : IsPGroup 2 R := P.isPGroup'.map H.subtype
  have hRP : R.subgroupOf H = (P : Subgroup H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective (P : Subgroup H)
  have hRN : (R.subgroupOf H).Normal := hRP.symm ▸ hP
  have hRne : R ≠ ⊥ := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    intro hbot
    exact P.ne_bot_of_dvd_card heven.two_dvd
      ((Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective).mp hbot)
  exact ⟨hRH, hR, hRP, hRN, hRne⟩

theorem strongly_embedded_borel_root_hall_center_data
    (H : Subgroup G) (hH : CFSG.BenderSuzuki.IsStronglyEmbedded H)
    (hB : IsBorelSubgroup H) (a b : G)
    (haH : a ∈ H) (hbH : b ∈ H)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) :
    Group.IsSolvable H ∧ ∃ (P : Sylow 2 H) (D : Subgroup H),
      let R := (P : Subgroup H).map H.subtype
      (P : Subgroup H).Normal ∧ (P : Subgroup H).IsComplement' D ∧
        Odd (Nat.card D) ∧ CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} D ∧
        Subgroup.normalizer (R : Set G) = H ∧
        (∀ x : G, x ∈ H → orderOf x = 2 →
          x ∈ (Subgroup.center R).map R.subtype) ∧
        Disjoint ((Subgroup.center R).map R.subtype)
          (Subgroup.normalizer (D.map H.subtype : Set G)) := by
  obtain ⟨hsolv, P, hP, hnormalizer⟩ := borel_exists_normal_sylow_two_root H hB
  obtain ⟨D, hcompl, hodd, hHall⟩ := normal_sylow_two_exists_odd_hall_complement P hP
  let R := (P : Subgroup H).map H.subtype
  obtain ⟨hRH, hR, hRP, hRN, hRne⟩ :=
    normal_sylow_two_ambient_image_data H P hP hH.card_even
  have hcomplR : (R.subgroupOf H).IsComplement' D := hRP.symm ▸ hcompl
  have hcenter : ∀ x : G, x ∈ H → orderOf x = 2 →
      x ∈ (Subgroup.center R).map R.subtype :=
    properCommutingImages_involutions_in_normal_root_center H hH R hR hRH hRN hRne
  have horder : CFSG.IsStronglyEmbedded H :=
    show CFSG.Open.fusionStronglyEmbedded H from order_strong_embedding_of_native hH
  have hdisjoint := strongly_embedded_root_center_disjoint_complement_normalizer
    H horder R hR hRH hRN D hcomplR a b haH hbH ha hb hab
  exact ⟨hsolv, P, D, hP, hcompl, hodd, hHall, hnormalizer, hcenter, hdisjoint⟩

theorem corefree_strong_embedding_root_hall_center_data
    (H : Subgroup G) (hH : CFSG.BenderSuzuki.IsStronglyEmbedded H)
    (hrank : TwoRankAtLeastTwo G) (hgen : involutionCore G = ⊤)
    (hcore : CFSG.oddCore G = ⊥) (a b : G)
    (haH : a ∈ H) (hbH : b ∈ H)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) :
    IsSimpleBenderGroup G ∧ Group.IsSolvable H ∧
      ∃ (P : Sylow 2 H) (D : Subgroup H),
        let R := (P : Subgroup H).map H.subtype
        (P : Subgroup H).Normal ∧ (P : Subgroup H).IsComplement' D ∧
          Odd (Nat.card D) ∧ CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} D ∧
          Subgroup.normalizer (R : Set G) = H ∧
          (∀ x : G, x ∈ H → orderOf x = 2 →
            x ∈ (Subgroup.center R).map R.subtype) ∧
          Disjoint ((Subgroup.center R).map R.subtype)
            (Subgroup.normalizer (D.map H.subtype : Set G)) := by
  obtain ⟨hmodel, hB⟩ :=
    corefree_involution_generated_strong_embedding_borel H hH hrank hgen hcore
  exact ⟨hmodel, strongly_embedded_borel_root_hall_center_data
    H hH hB a b haH hbH ha hb hab⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
