module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneBender

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

theorem quaternionTwo_cases : ∀ g : QuaternionGroup 2, ∃ ε : QuaternionGroup 2,
    (ε = 1 ∨ ε = .a 2) ∧ (g = ε ∨ g = ε * .a 1 ∨ g = ε * .xa 0 ∨ g = ε * (.a 1 * .xa 0)) := by
  decide

theorem quaternionTwo_sq : ∀ g : QuaternionGroup 2, g * g = 1 ∨ g * g = .a 2 := by decide

theorem quaternionTwo_comm : ∀ g g' : QuaternionGroup 2,
    g * g' * g⁻¹ * g'⁻¹ = 1 ∨ g * g' * g⁻¹ * g'⁻¹ = .a 2 := by decide

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) (P : Sylow 2 J) (eP : (P : Subgroup J) ≃* QuaternionGroup 2)

@[expose] noncomputable def quaternionMap : QuaternionGroup 2 →* J ⧸ Subgroup.center J :=
  ((QuotientGroup.mk' (Subgroup.center J)).comp (P : Subgroup J).subtype).comp
    eP.symm.toMonoidHom

@[expose] noncomputable def quaternionElt (g : QuaternionGroup 2) : EscapingQuotient z :=
  ((eP.symm g : (P : Subgroup J)) : J)

include h

omit [Finite G] h in
theorem quaternionElt_mem (g : QuaternionGroup 2) : quaternionElt P eP g ∈ J :=
  ((eP.symm g : (P : Subgroup J)) : J).2

theorem quaternionElt_a_two : quaternionElt P eP (.a 2) = escapingBar z := by
  have hne : eP.symm (.a 2) ≠ 1 := by
    rw [Ne, MulEquiv.map_eq_one_iff]
    decide
  have h2 : eP.symm (.a 2) * eP.symm (.a 2) = 1 := by
    rw [← map_mul]
    rw [show (QuaternionGroup.a 2 : QuaternionGroup 2) * .a 2 = 1 by decide, map_one]
  refine h.unique _ (quaternionElt_mem P eP _) ?_
  have : orderOf (eP.symm (.a 2)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2) hne
  rw [quaternionElt, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  exact this

theorem quaternionMap_eq_one_iff (g : QuaternionGroup 2) :
    quaternionMap P eP g = 1 ↔ g = 1 ∨ g = .a 2 := by
  constructor
  · intro hg
    have hc : ((eP.symm g : (P : Subgroup J)) : J) ∈ Subgroup.center J := by
      rw [← QuotientGroup.eq_one_iff]
      exact hg
    rcases h.eq_of_mem_center h.component hc with h1 | h1
    · left
      have : eP.symm g = 1 := Subtype.ext (Subtype.ext h1)
      rwa [MulEquiv.map_eq_one_iff] at this
    · right
      have h2 : eP.symm g = eP.symm (.a 2) := by
        apply Subtype.ext
        apply Subtype.ext
        change quaternionElt P eP g = quaternionElt P eP (.a 2)
        rw [h.quaternionElt_a_two P eP]
        exact h1
      exact eP.symm.injective h2
  · rintro (rfl | rfl)
    · exact map_one _
    · change QuotientGroup.mk' (Subgroup.center J) ((eP.symm (.a 2) : (P : Subgroup J)) : J) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      convert h.bar_mem_center using 1
      exact Subtype.ext (h.quaternionElt_a_two P eP)

theorem quaternionMap_mem (g : QuaternionGroup 2) :
    quaternionMap P eP g = 1 ∨ quaternionMap P eP g = quaternionMap P eP (.a 1) ∨
      quaternionMap P eP g = quaternionMap P eP (.xa 0) ∨
      quaternionMap P eP g = quaternionMap P eP (.a 1) * quaternionMap P eP (.xa 0) := by
  obtain ⟨ε, hε, hg⟩ := quaternionTwo_cases g
  have hε1 : quaternionMap P eP ε = 1 := (h.quaternionMap_eq_one_iff P eP ε).mpr hε
  rcases hg with rfl | rfl | rfl | rfl
  · exact Or.inl hε1
  · exact Or.inr (Or.inl (by rw [map_mul, hε1, one_mul]))
  · exact Or.inr (Or.inr (Or.inl (by rw [map_mul, hε1, one_mul])))
  · exact Or.inr (Or.inr (Or.inr (by rw [map_mul, map_mul, hε1, one_mul])))

theorem quaternionMap_sq (g : QuaternionGroup 2) :
    quaternionMap P eP g * quaternionMap P eP g = 1 := by
  rw [← map_mul]
  rcases quaternionTwo_sq g with h1 | h1 <;> rw [h1]
  · exact map_one _
  · exact (h.quaternionMap_eq_one_iff P eP _).mpr (Or.inr rfl)

theorem quaternionMap_commute (g g' : QuaternionGroup 2) :
    quaternionMap P eP g * quaternionMap P eP g' =
      quaternionMap P eP g' * quaternionMap P eP g := by
  have h1 : quaternionMap P eP (g * g' * g⁻¹ * g'⁻¹) = 1 :=
    (h.quaternionMap_eq_one_iff P eP _).mpr (quaternionTwo_comm g g')
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc quaternionMap P eP g * quaternionMap P eP g' =
      (quaternionMap P eP g * quaternionMap P eP g' * (quaternionMap P eP g)⁻¹ *
        (quaternionMap P eP g')⁻¹) * (quaternionMap P eP g' * quaternionMap P eP g) := by group
    _ = quaternionMap P eP g' * quaternionMap P eP g := by rw [h1, one_mul]

theorem quaternionMap_ne :
    quaternionMap P eP (.a 1) ≠ 1 ∧ quaternionMap P eP (.xa 0) ≠ 1 ∧
      quaternionMap P eP (.a 1) ≠ quaternionMap P eP (.xa 0) := by
  refine ⟨fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · rcases (h.quaternionMap_eq_one_iff P eP _).mp h1 with h2 | h2 <;> revert h2 <;> decide
  · rcases (h.quaternionMap_eq_one_iff P eP _).mp h1 with h2 | h2 <;> revert h2 <;> decide
  · have h2 : quaternionMap P eP (.a 1 * (.xa 0)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rcases (h.quaternionMap_eq_one_iff P eP _).mp h2 with h3 | h3 <;> revert h3 <;> decide

omit h in
theorem mem_sylowQuotient_iff (y : J ⧸ Subgroup.center J) :
    y ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J)) ↔ ∃ g, quaternionMap P eP g = y := by
  rw [Sylow.coe_mapSurjective]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨eP ⟨p, hp⟩, by simp [quaternionMap]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, (eP.symm g).2, rfl⟩

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
