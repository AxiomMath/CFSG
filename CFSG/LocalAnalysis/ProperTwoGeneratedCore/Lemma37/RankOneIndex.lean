module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneAlt
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneFour
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneNormal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

section General

variable {X : Type*} [Group X] {T Y : Subgroup X}

theorem commutator_mem_of_inv_mul_mem
    (hT : ∀ u ∈ Y, ∀ v ∈ Y, u ∉ T → v ∉ T → u⁻¹ * v ∈ T) {a b : X} (ha : a ∈ Y) (hb : b ∈ Y) :
    a * b * a⁻¹ * b⁻¹ ∈ T := by
  have hinv : ∀ {w : X}, w ∉ T → w⁻¹ ∉ T := fun hw h1 => hw (by
    have := T.inv_mem h1
    rwa [inv_inv] at this)
  by_cases haT : a ∈ T <;> by_cases hbT : b ∈ T
  · exact T.mul_mem (T.mul_mem (T.mul_mem haT hbT) (T.inv_mem haT)) (T.inv_mem hbT)
  · have hv : a⁻¹ * b⁻¹ ∉ T := fun h1 => hinv hbT (by
      have := T.mul_mem haT h1
      rwa [mul_inv_cancel_left] at this)
    have h1 := hT b⁻¹ (Y.inv_mem hb) (a⁻¹ * b⁻¹) (Y.mul_mem (Y.inv_mem ha) (Y.inv_mem hb))
      (hinv hbT) hv
    rw [inv_inv] at h1
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * (a⁻¹ * b⁻¹)) by group]
    exact T.mul_mem haT h1
  · have hv : b * a⁻¹ ∉ T := fun h1 => hinv haT (by
      have := T.mul_mem (T.inv_mem hbT) h1
      rwa [inv_mul_cancel_left] at this)
    have h1 := hT a⁻¹ (Y.inv_mem ha) (b * a⁻¹) (Y.mul_mem hb (Y.inv_mem ha)) (hinv haT) hv
    rw [inv_inv] at h1
    rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹) * b⁻¹ by group]
    exact T.mul_mem h1 (T.inv_mem hbT)
  · have h1 := hT a⁻¹ (Y.inv_mem ha) b hb (hinv haT) hbT
    have h2 := hT a ha b⁻¹ (Y.inv_mem hb) haT (hinv hbT)
    rw [inv_inv] at h1
    rw [show a * b * a⁻¹ * b⁻¹ = (a * b) * (a⁻¹ * b⁻¹) by group]
    exact T.mul_mem h1 h2

theorem conj_mem_of_inv_mul_mem (hTY : T ≤ Y)
    (hT : ∀ u ∈ Y, ∀ v ∈ Y, u ∉ T → v ∉ T → u⁻¹ * v ∈ T) {a t : X} (ha : a ∈ Y) (ht : t ∈ T) :
    a * t * a⁻¹ ∈ T := by
  have := T.mul_mem (commutator_mem_of_inv_mul_mem hT ha (hTY ht)) ht
  rwa [show a * t * a⁻¹ * t⁻¹ * t = a * t * a⁻¹ by group] at this

end General

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal]
include h

theorem inv_mul_mem_sup_of_not_mem
    {u v : EscapingQuotient z}
    (hu : u ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)))
    (hv : v ∉ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    u⁻¹ * v ∈ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_alternatingGroup_five
  have hcard := BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup_five e
  set o : EscapingQuotient z →* Outer (J ⧸ Subgroup.center J) :=
    (QuotientGroup.mk' (inner (J ⧸ Subgroup.center J))).comp (componentQuotientAction J) with ho
  have hmem : ∀ w, o w = 1 ↔ w ∈ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    fun w => by
      rw [ho, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h.action_mem_inner_iff
  rw [← hmem, map_mul, map_inv, inv_mul_eq_one]
  obtain ⟨p, q, hpq, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have hall : ∀ r : Outer (J ⧸ Subgroup.center J), r = p ∨ r = q := fun r => by
    have : r ∈ ({p, q} : Set _) := huniv ▸ Set.mem_univ r
    simpa using this
  have hu1 : o u ≠ 1 := fun h1 => hu ((hmem u).mp h1)
  have hv1 : o v ≠ 1 := fun h1 => hv ((hmem v).mp h1)
  rcases hall 1 with h1 | h1 <;> rcases hall (o u) with h2 | h2 <;>
    rcases hall (o v) with h3 | h3
  all_goals first
    | exact absurd (h2.trans h1.symm) hu1
    | exact absurd (h3.trans h1.symm) hv1
    | exact h2.trans h3.symm

omit [Finite G] h [J.Normal] in
theorem exists_quaternionElt_eq (P : Sylow 2 J)
    (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)
    (eP : (P : Subgroup J) ≃* QuaternionGroup 2) {q : EscapingQuotient z}
    (hqS : q ∈ escapingSylowImage S z) (hqJ : q ∈ J) : ∃ g, quaternionElt P eP g = q := by
  have hq : q ∈ (P : Subgroup J).map J.subtype := hP ▸ ⟨hqS, hqJ⟩
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hq
  exact ⟨eP ⟨p, hp⟩, by simp [quaternionElt]⟩

omit [Finite G] h [J.Normal] in
theorem quaternionElt_mem_sylowImage (P : Sylow 2 J)
    (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)
    (eP : (P : Subgroup J) ≃* QuaternionGroup 2) (g : QuaternionGroup 2) :
    quaternionElt P eP g ∈ escapingSylowImage S z := by
  have : quaternionElt P eP g ∈ (P : Subgroup J).map J.subtype :=
    Subgroup.mem_map_of_mem _ (eP.symm g).2
  rw [hP] at this
  exact this.1

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
