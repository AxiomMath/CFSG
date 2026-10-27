module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneNormal

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

theorem exists_perm_of_mulEquiv {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 5))
    (α : MulAut K) : ∃ σ : Perm (Fin 5), ∀ y : K,
      ((e (α y) : alternatingGroup (Fin 5)) : Perm (Fin 5)) = σ * (e y : Perm (Fin 5)) * σ⁻¹ := by
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by norm_num) (by norm_num)).2 (e.symm.trans (α.trans e))
  refine ⟨σ, fun y => ?_⟩
  have h1 := congrArg (fun β : MulAut (alternatingGroup (Fin 5)) =>
    ((β (e y) : alternatingGroup (Fin 5)) : Perm (Fin 5))) hσ
  simp only [MulAut.conjNormal_apply] at h1
  rw [h1]
  simp

theorem card_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal] (P : Sylow 2 J)
  (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)
  (eP : (P : Subgroup J) ≃* QuaternionGroup 2)
include h

omit h in
include hP in
theorem action_mem_sylowQuotient {x : EscapingQuotient z} (hxS : x ∈ escapingSylowImage S z)
    {y : J ⧸ Subgroup.center J}
    (hy : y ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J))) :
    componentQuotientAction J x y ∈ (P.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center J)) : Subgroup (J ⧸ Subgroup.center J)) := by
  rw [Sylow.coe_mapSurjective] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  rw [componentQuotientAction_mk]
  refine Subgroup.mem_map_of_mem _ ?_
  have hpS : (p : EscapingQuotient z) ∈ escapingSylowImage S z ⊓ J :=
    hP ▸ Subgroup.mem_map_of_mem J.subtype hp
  have hxp : ((MulAut.conjNormal x p : J) : EscapingQuotient z) ∈ escapingSylowImage S z ⊓ J := by
    rw [MulAut.conjNormal_apply]
    exact ⟨(escapingSylowImage S z).mul_mem ((escapingSylowImage S z).mul_mem hxS hpS.1)
      ((escapingSylowImage S z).inv_mem hxS), (inferInstance : J.Normal).conj_mem _ hpS.2 x⟩
  rw [← hP] at hxp
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hxp
  rwa [show MulAut.conjNormal x p = q from Subtype.ext hqe.symm]

theorem exists_lift_of_fixed {x : EscapingQuotient z} {c : J ⧸ Subgroup.center J}
    (hc3 : c * c * c = 1) (hcx : componentQuotientAction J x c = c) :
    ∃ c₀ : J, QuotientGroup.mk' (Subgroup.center J) c₀ = c ∧
      (c₀ : EscapingQuotient z) * (c₀ : EscapingQuotient z) * c₀ = 1 ∧
      x * c₀ = c₀ * x := by
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) c
  have hj3 : j ^ 3 ∈ Subgroup.center J := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, pow_three, ← mul_assoc,
      hc3]
  have hj6 : j ^ 6 = 1 := by
    rcases h.eq_of_mem_center h.component hj3 with h1 | h1
    · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, show j ^ 3 = 1 from Subtype.ext h1, one_pow]
    · have h2 : j ^ 3 * j ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, h1, ← pow_two, h.bar_sq]
        rfl
      rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, h2]
  refine ⟨j ^ 4, ?_, ?_, ?_⟩
  · rw [map_pow, show (4 : ℕ) = 3 + 1 by norm_num, pow_add, pow_three, ← mul_assoc, hc3,
      one_mul, pow_one]
  · have h12 : (j ^ 4) * (j ^ 4) * (j ^ 4) = 1 := by
      rw [← pow_add, ← pow_add, show 4 + 4 + 4 = 6 * 2 by norm_num, pow_mul, hj6, one_pow]
    have := congrArg (fun w : J => (w : EscapingQuotient z)) h12
    simpa using this
  ·
    set c₀ : J := j ^ 4 with hc₀
    have h12 : c₀ * c₀ * c₀ = 1 := by
      rw [hc₀, ← pow_add, ← pow_add, show 4 + 4 + 4 = 6 * 2 by norm_num, pow_mul, hj6, one_pow]
    have hfix : QuotientGroup.mk' (Subgroup.center J) (MulAut.conjNormal x c₀) =
        QuotientGroup.mk' (Subgroup.center J) c₀ := by
      rw [← componentQuotientAction_mk, hc₀, map_pow, map_pow, hcx]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hfix
    rcases h.eq_of_mem_center h.component hfix with h1 | h1
    · have h2 : ((MulAut.conjNormal x c₀ : J) : EscapingQuotient z) = c₀ := by
        have h3 : ((MulAut.conjNormal x c₀ : J) : EscapingQuotient z)⁻¹ * c₀ = 1 := by
          simpa using h1
        exact inv_mul_eq_one.mp h3
      rw [MulAut.conjNormal_apply] at h2
      calc x * c₀ = x * c₀ * x⁻¹ * x := by group
        _ = c₀ * x := by rw [h2]
    · exfalso
      have hzz : escapingBar z * escapingBar z = 1 := by rw [← pow_two, h.bar_sq]
      have h3 : ((MulAut.conjNormal x c₀ : J) : EscapingQuotient z)⁻¹ * (c₀ : EscapingQuotient z) =
          escapingBar z := by simpa using h1
      have h2 : ((MulAut.conjNormal x c₀ : J) : EscapingQuotient z) =
          (c₀ : EscapingQuotient z) * escapingBar z := by
        calc ((MulAut.conjNormal x c₀ : J) : EscapingQuotient z)
            = ((MulAut.conjNormal x c₀ : J) : EscapingQuotient z) *
                (((MulAut.conjNormal x c₀ : J) : EscapingQuotient z)⁻¹ * c₀) * escapingBar z := by
              rw [h3, mul_assoc, hzz, mul_one]
          _ = c₀ * escapingBar z := by group
      have h4 : (MulAut.conjNormal x c₀) * (MulAut.conjNormal x c₀) * (MulAut.conjNormal x c₀) =
          (1 : J) := by rw [← map_mul, ← map_mul, h12, map_one]
      have h5 := congrArg (fun w : J => (w : EscapingQuotient z)) h4
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at h5
      rw [h2] at h5
      have h6 : ((c₀ : EscapingQuotient z) * escapingBar z) ^ 3 = 1 := by
        rw [pow_three, ← mul_assoc]
        exact h5
      have h7 : (c₀ : EscapingQuotient z) ^ 3 = 1 := by
        have := congrArg (fun w : J => (w : EscapingQuotient z)) h12
        simp only [Subgroup.coe_mul, Subgroup.coe_one] at this
        rw [pow_three, ← mul_assoc]
        exact this
      rw [(h.quotientData.commute_bar _).mul_pow, h7, one_mul, pow_succ, h.bar_sq,
        one_mul] at h6
      exact h.bar_ne_one h6

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
