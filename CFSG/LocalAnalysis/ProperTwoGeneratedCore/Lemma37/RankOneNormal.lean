module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseTwoComponent
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneEmbed

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise

theorem componentQuotientAction_mk {X : Type} [Group X] (J : Subgroup X) [J.Normal] (x : X)
    (j : J) :
    componentQuotientAction J x (QuotientGroup.mk' (Subgroup.center J) j) =
      QuotientGroup.mk' (Subgroup.center J) (MulAut.conjNormal x j) :=
  PerfectAutomorphisms.onCenterQuotient_apply_mk _ _

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal]
include h

theorem action_eq_one_iff {x : EscapingQuotient z} :
    componentQuotientAction J x = 1 ↔ x ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  have : Group.IsPerfect J := h.component.1.1
  refine ⟨mem_centralizer_of_componentQuotientAction_eq_one J, fun hx => ?_⟩
  have hconj : MulAut.conjNormal (H := J) x = 1 := by
    ext y
    simp only [MulAut.conjNormal_apply, MulAut.one_apply]
    rw [(Subgroup.mem_centralizer_iff.mp hx y y.2).symm, mul_inv_cancel_right]
  change PerfectAutomorphisms.centerQuotientHom J (MulAut.conjNormal (H := J) x) = 1
  rw [hconj, map_one]

theorem action_mem_inner_iff {x : EscapingQuotient z} :
    componentQuotientAction J x ∈ inner (J ⧸ Subgroup.center J) ↔
      x ∈ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) q
    have hj : componentQuotientAction J (j : EscapingQuotient z) = componentQuotientAction J x :=
      (componentQuotientAction_coe J j).trans hq
    have hc : (j : EscapingQuotient z)⁻¹ * x ∈
        Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
      rw [← h.action_eq_one_iff, map_mul, map_inv, hj, inv_mul_cancel]
    have := (J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))).mul_mem
      (Subgroup.mem_sup_left j.2) (Subgroup.mem_sup_right hc)
    rwa [mul_inv_cancel_left] at this
  · intro hx
    have hx' : x ∈ ((J : Set (EscapingQuotient z)) *
        (Subgroup.centralizer (J : Set (EscapingQuotient z)) : Set (EscapingQuotient z))) := by
      rw [← Subgroup.mul_normal]
      exact hx
    obtain ⟨j, hj, c, hc, rfl⟩ := hx'
    refine ⟨QuotientGroup.mk' (Subgroup.center J) ⟨j, hj⟩, ?_⟩
    rw [map_mul, (h.action_eq_one_iff).mpr hc, mul_one]
    exact (componentQuotientAction_coe J ⟨j, hj⟩).symm

omit [J.Normal] in
theorem card_le_card_sylowImage_inf {R : Subgroup (EscapingQuotient z)} (hRJ : R ≤ J)
    (hR : IsPGroup 2 R) : Nat.card R ≤ Nat.card (escapingSylowImage S z ⊓ J : Subgroup _) := by
  have h1 := card_le_card_sylow_inf_of_isSubnormal (sylowBarSylow h.square.central)
    h.component.2 hRJ hR
  rwa [h.coe_sylow] at h1

omit [J.Normal] in
theorem mem_sylowImage_of_mem_normalizer {q : EscapingQuotient z} (hqJ : q ∈ J) {n : ℕ}
    (hq : q ^ 2 ^ n = 1) (hqN : q ∈ Subgroup.normalizer
      ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) : Set (EscapingQuotient z))) :
    q ∈ escapingSylowImage S z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := escapingSylowImage S z ⊓ J with hQ
  have hQ2 : IsPGroup 2 Q := h.sylowImage_isPGroup.to_le inf_le_left
  have hq2 : IsPGroup 2 (Subgroup.zpowers q) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hq)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hR := IsPGroup.to_sup_of_normal_right' hq2 hQ2 (Subgroup.zpowers_le.mpr hqN)
  have hRJ : Subgroup.zpowers q ⊔ Q ≤ J := sup_le (Subgroup.zpowers_le.mpr hqJ) inf_le_right
  have heq : Q = Subgroup.zpowers q ⊔ Q :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (h.card_le_card_sylowImage_inf hRJ hR)
  have : q ∈ Q := heq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers q)
  exact this.1

theorem exists_mul_eq_of_mem_sup {t : EscapingQuotient z} (htS : t ∈ escapingSylowImage S z)
    (htJK : t ∈ J ⊔ Subgroup.centralizer (J : Set (EscapingQuotient z))) :
    ∃ q ∈ escapingSylowImage S z, q ∈ J ∧ ∃ c ∈ escapingSylowImage S z,
      c ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧ q * c = t := by
  have ht' : t ∈ ((J : Set (EscapingQuotient z)) *
      (Subgroup.centralizer (J : Set (EscapingQuotient z)) : Set (EscapingQuotient z))) := by
    rw [← Subgroup.mul_normal]
    exact htJK
  obtain ⟨q, hqJ, c, hcK, rfl⟩ := ht'
  have hqc : Commute q c := Subgroup.mem_centralizer_iff.mp hcK q hqJ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.sylowImage_isPGroup) ⟨q * c, htS⟩
  rw [Subgroup.orderOf_mk] at hn
  have hpow : (q * c) ^ 2 ^ n = 1 := by rw [← hn, pow_orderOf_eq_one]
  rw [hqc.mul_pow] at hpow
  have hqJK : q ^ 2 ^ n ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcK _)
  have hq2 : q ^ 2 ^ (n + 1) = 1 := by
    rcases h.eq_of_mem_centralizer_component h.component (J.pow_mem hqJ _) hqJK with h1 | h1
    · rw [pow_succ, pow_mul, h1, one_pow]
    · rw [pow_succ, pow_mul, h1, h.bar_sq]
  have hqN : q ∈ Subgroup.normalizer
      ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
        Set (EscapingQuotient z)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc : ∀ w ∈ J, c * w * c⁻¹ = w := fun w hw => by
      rw [(Subgroup.mem_centralizer_iff.mp hcK w hw).symm, mul_inv_cancel_right]
    constructor
    · rintro ⟨hyS, hyJ⟩
      have hy1 : (q * c) * y * (q * c)⁻¹ ∈ escapingSylowImage S z :=
        (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).mul_mem htS hyS)
          ((escapingSylowImage S z).inv_mem htS)
      have hy2 : (q * c) * y * (q * c)⁻¹ = q * y * q⁻¹ := by
        rw [mul_inv_rev, show q * c * y * (c⁻¹ * q⁻¹) = q * (c * y * c⁻¹) * q⁻¹ by group, hc y hyJ]
      refine ⟨hy2 ▸ hy1, ?_⟩
      exact (inferInstance : J.Normal).conj_mem y hyJ q
    · rintro ⟨hyS, hyJ⟩
      have hyJ' : y ∈ J := by
        have := (inferInstance : J.Normal).conj_mem _ hyJ q⁻¹
        simpa [mul_assoc] using this
      refine ⟨?_, hyJ'⟩
      have hy2 : (q * c)⁻¹ * (q * y * q⁻¹) * (q * c) = y := by
        rw [mul_inv_rev, show c⁻¹ * q⁻¹ * (q * y * q⁻¹) * (q * c) = c⁻¹ * y * c by group]
        rw [show c⁻¹ * y * c = c⁻¹ * y * c⁻¹⁻¹ by rw [inv_inv]]
        have := hc y hyJ'
        calc c⁻¹ * y * c⁻¹⁻¹ = c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ := by rw [this]
          _ = y := by group
      rw [← hy2]
      exact (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).mul_mem
        ((escapingSylowImage S z).inv_mem htS) hyS) htS
  have hqS := h.mem_sylowImage_of_mem_normalizer hqJ hq2 hqN
  refine ⟨q, hqS, hqJ, c, ?_, hcK, rfl⟩
  have := (escapingSylowImage S z).mul_mem ((escapingSylowImage S z).inv_mem hqS) htS
  rwa [inv_mul_cancel_left] at this

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
