module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneEmbed

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms

@[expose] noncomputable def componentNormalizerAction {X : Type*} [Group X] (J : Subgroup X) :
    Subgroup.normalizer (J : Set X) →* MulAut (J ⧸ Subgroup.center J) :=
  (PerfectAutomorphisms.centerQuotientHom J).comp J.normalizerMonoidHom

theorem componentNormalizerAction_mk {X : Type*} [Group X] (J : Subgroup X)
    (n : Subgroup.normalizer (J : Set X)) (j : J) :
    componentNormalizerAction J n (QuotientGroup.mk' (Subgroup.center J) j) =
      QuotientGroup.mk' (Subgroup.center J) (J.normalizerMonoidHom n j) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ _

theorem componentNormalizerAction_eq_one_of_mem_centralizer {X : Type*} [Group X]
    (J : Subgroup X) {n : Subgroup.normalizer (J : Set X)}
    (hn : (n : X) ∈ Subgroup.centralizer (J : Set X)) : componentNormalizerAction J n = 1 := by
  have hconj : J.normalizerMonoidHom n = 1 := by
    ext y
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
      (Subgroup.mem_centralizer_iff.mp hn y y.2).symm, mul_inv_cancel_right]
  change PerfectAutomorphisms.centerQuotientHom J (J.normalizerMonoidHom n) = 1
  rw [hconj, map_one]

theorem mem_centralizer_of_componentNormalizerAction_eq_one {X : Type*} [Group X]
    (J : Subgroup X) [Group.IsPerfect J] {n : Subgroup.normalizer (J : Set X)}
    (hn : componentNormalizerAction J n = 1) : (n : X) ∈ Subgroup.centralizer (J : Set X) := by
  have hconj : J.normalizerMonoidHom n = 1 := by
    apply PerfectAutomorphisms.centerQuotientHom_injective J
    rw [map_one]
    exact hn
  rw [Subgroup.mem_centralizer_iff]
  intro j hj
  have h1 := congrArg (fun α : MulAut J => ((α ⟨j, hj⟩ : J) : X)) hconj
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h1
  calc j * n = n * j * (n : X)⁻¹ * n := by rw [h1]
    _ = n * j := by group

theorem componentNormalizerAction_eq_conj {X : Type*} [Group X] (J : Subgroup X)
    {n : Subgroup.normalizer (J : Set X)} {j : J} (hnj : (n : X) = j) :
    componentNormalizerAction J n = MulAut.conj (QuotientGroup.mk' (Subgroup.center J) j) := by
  have hconj : J.normalizerMonoidHom n = MulAut.conj j := by
    ext y
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hnj, MulAut.conj_apply]
    rfl
  change PerfectAutomorphisms.centerQuotientHom J (J.normalizerMonoidHom n) = _
  rw [hconj, centerQuotient_conj]

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) (P : Sylow 2 J)
  (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)

include hP in
theorem normalizerAction_mem_sylowQuotient
    {x : Subgroup.normalizer (J : Set (EscapingQuotient z))}
    (hxS : (x : EscapingQuotient z) ∈ escapingSylowImage S z) {y : J ⧸ Subgroup.center J}
    (hy : y ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J))) :
    componentNormalizerAction J x y ∈ (P.mapSurjective
      (QuotientGroup.mk'_surjective (Subgroup.center J)) : Subgroup (J ⧸ Subgroup.center J)) := by
  rw [Sylow.coe_mapSurjective] at hy ⊢
  obtain ⟨p, hp, rfl⟩ := hy
  rw [componentNormalizerAction_mk]
  refine Subgroup.mem_map_of_mem _ ?_
  have hpS : (p : EscapingQuotient z) ∈ escapingSylowImage S z ⊓ J :=
    hP ▸ Subgroup.mem_map_of_mem J.subtype hp
  have hxp : ((J.normalizerMonoidHom x p : J) : EscapingQuotient z) ∈
      escapingSylowImage S z ⊓ J := by
    refine ⟨?_, (J.normalizerMonoidHom x p).2⟩
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).mul_mem hxS hpS.1)
      ((escapingSylowImage S z).inv_mem hxS)
  rw [← hP] at hxp
  obtain ⟨q, hq, hqe⟩ := Subgroup.mem_map.mp hxp
  rwa [show J.normalizerMonoidHom x p = q from Subtype.ext hqe.symm]

include h

theorem exists_lift_of_normalizerAction_fixed
    {x : Subgroup.normalizer (J : Set (EscapingQuotient z))} {c : J ⧸ Subgroup.center J}
    (hc3 : c * c * c = 1) (hcx : componentNormalizerAction J x c = c) :
    ∃ c₀ : J, QuotientGroup.mk' (Subgroup.center J) c₀ = c ∧
      (c₀ : EscapingQuotient z) * (c₀ : EscapingQuotient z) * c₀ = 1 ∧
      (x : EscapingQuotient z) * c₀ = c₀ * x := by
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
    set d : J := J.normalizerMonoidHom x c₀ with hd
    have hdc : (d : EscapingQuotient z) = x * c₀ * (x : EscapingQuotient z)⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe _ _ _
    have h12 : c₀ * c₀ * c₀ = 1 := by
      rw [hc₀, ← pow_add, ← pow_add, show 4 + 4 + 4 = 6 * 2 by norm_num, pow_mul, hj6, one_pow]
    have hfix : QuotientGroup.mk' (Subgroup.center J) d =
        QuotientGroup.mk' (Subgroup.center J) c₀ := by
      rw [hd, ← componentNormalizerAction_mk, hc₀, map_pow, map_pow, hcx]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hfix
    rcases h.eq_of_mem_center h.component hfix with h1 | h1
    · have h2 : (d : EscapingQuotient z) = c₀ := by
        have h3 : (d : EscapingQuotient z)⁻¹ * c₀ = 1 := by simpa using h1
        exact inv_mul_eq_one.mp h3
      rw [hdc] at h2
      calc (x : EscapingQuotient z) * c₀ = x * c₀ * (x : EscapingQuotient z)⁻¹ * x := by group
        _ = c₀ * x := by rw [h2]
    · exfalso
      have hzz : escapingBar z * escapingBar z = 1 := by rw [← pow_two, h.bar_sq]
      have h3 : (d : EscapingQuotient z)⁻¹ * (c₀ : EscapingQuotient z) = escapingBar z := by
        simpa using h1
      have h2 : (d : EscapingQuotient z) = (c₀ : EscapingQuotient z) * escapingBar z := by
        calc (d : EscapingQuotient z)
            = (d : EscapingQuotient z) * ((d : EscapingQuotient z)⁻¹ * c₀) * escapingBar z := by
              rw [h3, mul_assoc, hzz, mul_one]
          _ = c₀ * escapingBar z := by group
      have h4 : d * d * d = (1 : J) := by rw [hd, ← map_mul, ← map_mul, h12, map_one]
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
