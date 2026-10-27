module

public import CFSG.LocalAnalysis.ComponentClassification.SubgroupSylowTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalSylowIntersection
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

theorem rightConjugate_map_equiv {G K : Type*} [Group G] [Group K]
    (Q : Subgroup G) (e : G ≃* K) (g : K) :
    rightConjugate (Q.map e.toMonoidHom) g =
      (rightConjugate Q (e.symm g)).map e.toMonoidHom :=
  CFSG.StandardSubgroupAPI.rightConjugate_map_mulEquiv Q e g

theorem tightlyEmbedded_map_equiv {G K : Type*} [Group G] [Group K]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (e : G ≃* K) :
    TightlyEmbedded (Q.map e.toMonoidHom) :=
  CFSG.StandardSubgroupAPI.tightlyEmbedded_map_mulEquiv htight e

theorem rightConjugate_tightlyEmbedded {G : Type*} [Group G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G) :
    TightlyEmbedded (rightConjugate Q g) :=
  CFSG.StandardSubgroupAPI.tightlyEmbedded_rightConjugate htight g

theorem rightConjugate_inv_cancel {G : Type*} [Group G] (Q : Subgroup G) (g : G) :
    rightConjugate (rightConjugate Q g) g⁻¹ = Q := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem two_subgroup_card_le_sylowImage {G : Type*} [Group G] [Finite G]
    (M R : Subgroup G) (htwo : IsPGroup 2 R) (hR : R ≤ M) (P : Sylow 2 M) :
    Nat.card R ≤ Nat.card (sylowImage M P) := by
  obtain ⟨D, hD⟩ := (htwo.comap_subtype (K := M)).exists_le_sylow
  have hcard : Nat.card R = Nat.card (R.subgroupOf M) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv).symm
  rw [hcard, sylowImage_card, ← SubgroupSylowTransport.same_card D P]
  exact Subgroup.card_le_of_le hD

theorem exists_sylowImage_containing {G : Type*} [Group G]
    (M R : Subgroup G) (htwo : IsPGroup 2 R) (hR : R ≤ M) :
    ∃ P : Sylow 2 M, R ≤ sylowImage M P := by
  obtain ⟨P, hP⟩ := (htwo.comap_subtype (K := M)).exists_le_sylow
  refine ⟨P, ?_⟩
  have hmap := Subgroup.map_mono (f := M.subtype) hP
  change (R.subgroupOf M).map M.subtype ≤ sylowImage M P at hmap
  rwa [Subgroup.map_subgroupOf_eq_of_le hR] at hmap

theorem sylow_product_base_intersection {G : Type*} [Group G] [Finite G]
    (Q T : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (S : Sylow 2 ↥(Q ⊔ T)) :
    ∃ R : Sylow 2 Q, sylowImage Q R = sylowImage (Q ⊔ T) S ⊓ Q := by
  let J := Q ⊔ T
  let A := Q.subgroupOf J
  let : A.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le Subgroup.le_normalizer hnormalizes)
  let inside := CFSG.RankThreeEvenClassification.Helpers.sylowNormalIntersection
    2 Nat.prime_two S A
  let e : A ≃* Q := Subgroup.subgroupOfEquivOfLe (le_sup_left : Q ≤ J)
  have hsurjective : Function.Surjective e.toMonoidHom := e.surjective
  let R : Sylow 2 Q := inside.mapSurjective (f := e.toMonoidHom) hsurjective
  refine ⟨R, ?_⟩
  change ((inside.mapSurjective (f := e.toMonoidHom) hsurjective : Sylow 2 Q) :
    Subgroup Q).map Q.subtype = _
  rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) hsurjective inside, Subgroup.map_map]
  have hmaps : Q.subtype.comp e.toMonoidHom = J.subtype.comp A.subtype := by
    ext a
    rfl
  rw [hmaps, ← Subgroup.map_map,
    CFSG.RankThreeEvenClassification.Helpers.sylowNormalIntersection_coe,
    Subgroup.subgroupOf_map_subtype, Subgroup.map_inf _ _ _ J.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (le_sup_left : Q ≤ J)]
  rfl

theorem two_subgroup_card_le_conjugate_sylow {G : Type*} [Group G] [Finite G]
    (Q P T : Subgroup G) (g : G) (hP : rightConjugate Q g = P)
    (htwo : IsPGroup 2 T) (hT : T ≤ P) (R : Sylow 2 Q) :
    Nat.card T ≤ Nat.card (sylowImage Q R) := by
  obtain ⟨D, hD⟩ := exists_sylowImage_containing P T htwo hT
  have hcards := SubgroupSylowTransport.card_eq Q P (MulAut.conj g⁻¹) hP R D
  have hbound : Nat.card T ≤ Nat.card (sylowImage P D) := Subgroup.card_le_of_le hD
  rwa [sylowImage_card, ← hcards, ← sylowImage_card Q R] at hbound

theorem two_subgroup_equiv_sylowImage_of_card {G : Type*} [Group G] [Finite G]
    (M R : Subgroup G) (htwo : IsPGroup 2 R) (hR : R ≤ M) (P : Sylow 2 M)
    (hcard : Nat.card R = Nat.card (sylowImage M P)) :
    Nonempty (R ≃* sylowImage M P) := by
  obtain ⟨D, hD⟩ := exists_sylowImage_containing M R htwo hR
  have hsame : Nat.card (sylowImage M D) = Nat.card (sylowImage M P) := by
    rw [sylowImage_card, sylowImage_card, SubgroupSylowTransport.same_card D P]
  have heq : R = sylowImage M D := Subgroup.eq_of_le_of_card_ge hD (hsame.trans hcard.symm).le
  exact ⟨(MulEquiv.subgroupCongr heq).trans
    (((D : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective).symm.trans
      ((D.equiv P).trans ((P : Subgroup M).equivMapOfInjective M.subtype M.subtype_injective)))⟩

theorem sylowImage_equiv_conjugate {G : Type*} [Group G] [Finite G]
    (Q P : Subgroup G) (g : G) (hP : rightConjugate Q g = P)
    (R : Sylow 2 Q) (D : Sylow 2 P) :
    Nonempty (sylowImage Q R ≃* sylowImage P D) := by
  obtain ⟨transported, himage⟩ :=
    SubgroupSylowTransport.exists_image Q P (MulAut.conj g⁻¹) hP R
  let conjEquiv : sylowImage Q R ≃* sylowImage P transported :=
    ((sylowImage Q R).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).trans (MulEquiv.subgroupCongr himage.symm)
  exact ⟨conjEquiv.trans
    (((transported : Subgroup P).equivMapOfInjective P.subtype P.subtype_injective).symm.trans
      ((transported.equiv D).trans
        ((D : Subgroup P).equivMapOfInjective P.subtype P.subtype_injective)))⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
