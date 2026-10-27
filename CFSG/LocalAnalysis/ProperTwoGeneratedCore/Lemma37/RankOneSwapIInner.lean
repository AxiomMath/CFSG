module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneSwapIAction
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneT1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J)
include h

theorem normalizerAction_mem_inner_of_mul_self_eq_one
    {x : Subgroup.normalizer (J : Set (EscapingQuotient z))}
    (hxS : (x : EscapingQuotient z) ∈ escapingSylowImage S z)
    (hx2 : (x : EscapingQuotient z) * x = 1) :
    componentNormalizerAction J x ∈ inner (J ⧸ Subgroup.center J) := by
  have hq := h.quotientData
  obtain ⟨e⟩ := h.nonempty_mulEquiv_alternatingGroup_five
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  obtain ⟨eP⟩ := h.sylow_mulEquiv_quaternion_two P
  obtain ⟨σ, hσ'⟩ := exists_perm_of_mulEquiv e (componentNormalizerAction J x)
  have hσ : ∀ y, permOf e (componentNormalizerAction J x y) = σ * permOf e y * σ⁻¹ := hσ'
  by_cases hsign : Perm.sign σ = 1
  · refine ⟨e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩, ?_⟩
    ext y
    apply permOf_injective e
    rw [hσ y, MulAut.conj_apply, permOf_mul, permOf_mul, permOf_inv]
    simp [permOf]
  exfalso
  set φ := componentNormalizerAction J with hφ
  have hxx : x * x = 1 := Subtype.ext hx2
  have hσσ : σ * σ = 1 := by
    apply perm_eq_one_of_forall_conj
    intro a
    have h1 := hσ (φ x (e.symm a))
    rw [hσ (e.symm a)] at h1
    have h2 : φ x (φ x (e.symm a)) = e.symm a := by
      rw [← MulAut.mul_apply, ← map_mul, hxx, map_one, MulAut.one_apply]
    rw [h2] at h1
    simp only [permOf, MulEquiv.apply_symm_apply] at h1
    rw [mul_inv_rev]
    calc σ * σ * (a : Perm (Fin 5)) * (σ⁻¹ * σ⁻¹) = σ * (σ * a * σ⁻¹) * σ⁻¹ := by group
      _ = a := h1.symm
  have hφx : φ x ≠ 1 := fun h1 => hsign (by
    rw [perm_eq_one_of_forall_conj (τ := σ) fun a => by
      have := hσ (e.symm a)
      rw [h1, MulAut.one_apply] at this
      simpa [permOf] using this.symm]
    exact map_one _)
  have hx1 : (x : EscapingQuotient z) ≠ 1 := fun h1 => hφx (by
    rw [show x = 1 from Subtype.ext h1, map_one])
  have hxz : (x : EscapingQuotient z) ≠ escapingBar z := fun h1 => hφx (by
    apply componentNormalizerAction_eq_one_of_mem_centralizer
    rw [h1]
    exact hq.bar_mem_component_centralizer)
  have hxo : orderOf (x : EscapingQuotient z) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  obtain ⟨hA, hB⟩ := h.fourGroup P eP e
  have hmem : ∀ y, y ∈ (P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J)) ↔ InFour P eP y := fun y =>
    (mem_sylowQuotient_iff P eP y).trans (h.inFour_iff P eP y).symm
  have hgen : ∀ g : QuaternionGroup 2, quaternionMap P eP g ≠ 1 →
      permOf e (φ x (quaternionMap P eP g)) = permOf e (quaternionMap P eP (.a 1)) ∨
        permOf e (φ x (quaternionMap P eP g)) = permOf e (quaternionMap P eP (.xa 0)) ∨
        permOf e (φ x (quaternionMap P eP g)) =
          permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)) := by
    intro g hg
    refine permOf_of_inFour P eP e ((hmem _).mp (normalizerAction_mem_sylowQuotient P hP hxS
      ((hmem _).mpr ((h.inFour_iff P eP _).mpr ⟨g, rfl⟩)))) ?_
    intro h1
    exact hg ((φ x).injective (h1.trans (map_one _).symm))
  obtain ⟨hA1, hB1, -⟩ := h.quaternionMap_ne P eP
  have hσA := hgen _ hA1
  have hσB := hgen _ hB1
  rw [hσ] at hσA hσB
  obtain ⟨c, hc1, hc3, hc, hσc, hcnot⟩ := s5_exists_three_not_normalizing σ ⟨hσσ, hsign⟩ _ hA _
    ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hB.2.2.2.2, hσA, hσB⟩
  set c' : J ⧸ Subgroup.center J := e.symm ⟨c, Perm.mem_alternatingGroup.mpr hc1⟩ with hc'
  have hc'c : permOf e c' = c := by simp [hc', permOf]
  have hc'3 : c' * c' * c' = 1 := by
    apply permOf_injective e
    rw [permOf_mul, permOf_mul, hc'c, hc3, permOf_one]
  have hc'fix : φ x c' = c' := by
    apply permOf_injective e
    rw [hσ, hc'c, hσc, mul_inv_cancel_right]
  obtain ⟨c₀, hc₀, -, hc₀x⟩ := h.exists_lift_of_normalizerAction_fixed hc'3 hc'fix
  have hc₀H : (c₀ : EscapingQuotient z) ∈ escapingImage H z :=
    hq.involution_centralizer_le (h.sylowImage_le hxS) hxo hxz
      (Subgroup.mem_centralizer_singleton_iff.mpr hc₀x.symm)
  have hc'B : c' ∈ embedImage H z J := hc₀ ▸ Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr hc₀H)
  rw [← h.normalizer_eq_embedImage P hP, Subgroup.mem_normalizer_iff] at hc'B
  apply hcnot
  have hconj : ∀ g : QuaternionGroup 2, quaternionMap P eP g ≠ 1 →
      permOf e c' * permOf e (quaternionMap P eP g) * (permOf e c')⁻¹ =
          permOf e (quaternionMap P eP (.a 1)) ∨
        permOf e c' * permOf e (quaternionMap P eP g) * (permOf e c')⁻¹ =
          permOf e (quaternionMap P eP (.xa 0)) ∨
        permOf e c' * permOf e (quaternionMap P eP g) * (permOf e c')⁻¹ =
          permOf e (quaternionMap P eP (.a 1)) * permOf e (quaternionMap P eP (.xa 0)) := by
    intro g hg
    rw [← permOf_inv, ← permOf_mul, ← permOf_mul]
    refine permOf_of_inFour P eP e ((hmem _).mp ((hc'B _).mp
      ((hmem _).mpr ((h.inFour_iff P eP _).mpr ⟨g, rfl⟩)))) ?_
    intro h1
    apply hg
    have := congrArg (fun w => c'⁻¹ * w * c') h1
    simpa [mul_assoc] using this
  have h1 := hconj _ hA1
  have h2 := hconj _ hB1
  rw [hc'c] at h1 h2
  exact ⟨h1, h2⟩

theorem mem_sylowImage_of_mul_mem_normalizer {t j c : EscapingQuotient z}
    (htS : t ∈ escapingSylowImage S z)
    (htN : t ∈ Subgroup.normalizer (J : Set (EscapingQuotient z))) (hjJ : j ∈ J)
    (hcK : c ∈ Subgroup.centralizer (J : Set (EscapingQuotient z))) (hjc : j * c = t) :
    j ∈ escapingSylowImage S z := by
  subst hjc
  have hjc : Commute j c := Subgroup.mem_centralizer_iff.mp hcK j hjJ
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp h.sylowImage_isPGroup) ⟨j * c, htS⟩
  rw [Subgroup.orderOf_mk] at hn
  have hpow : (j * c) ^ 2 ^ n = 1 := by rw [← hn, pow_orderOf_eq_one]
  rw [hjc.mul_pow] at hpow
  have hjK : j ^ 2 ^ n ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    rw [eq_inv_of_mul_eq_one_left hpow]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcK _)
  have hj2 : j ^ 2 ^ (n + 1) = 1 := by
    rcases h.eq_of_mem_centralizer_component h.component (J.pow_mem hjJ _) hjK with h1 | h1
    · rw [pow_succ, pow_mul, h1, one_pow]
    · rw [pow_succ, pow_mul, h1, h.bar_sq]
  have hjN : j ∈ Subgroup.normalizer
      ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
        Set (EscapingQuotient z)) := by
    have htN' : j * c ∈ Subgroup.normalizer
        ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
          Set (EscapingQuotient z)) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer htS, htN⟩
    have hcN : c⁻¹ ∈ Subgroup.normalizer
        ((escapingSylowImage S z ⊓ J : Subgroup (EscapingQuotient z)) :
          Set (EscapingQuotient z)) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.inv_mem _ hcK) g hg.2
    have := Subgroup.mul_mem _ htN' hcN
    rwa [mul_inv_cancel_right] at this
  exact h.mem_sylowImage_of_mem_normalizer hjJ hj2 hjN

theorem exists_mul_eq_of_mul_self_eq_one
    {x : EscapingQuotient z}
    (hxS : x ∈ escapingSylowImage S z)
    (hxN : x ∈ Subgroup.normalizer (J : Set (EscapingQuotient z))) (hx2 : x * x = 1) :
    ∃ q ∈ escapingSylowImage S z, q ∈ J ∧ ∃ c ∈ escapingSylowImage S z,
      c ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) ∧ q * c = x := by
  have : Group.IsPerfect J := h.component.1.1
  set N := Subgroup.normalizer (J : Set (EscapingQuotient z)) with hN
  obtain ⟨q', hq'⟩ := h.normalizerAction_mem_inner_of_mul_self_eq_one (x := ⟨x, hxN⟩) hxS hx2
  obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) q'
  have hjN : (j : EscapingQuotient z) ∈ N := Subgroup.le_normalizer j.2
  have hφ : componentNormalizerAction J ((⟨j, hjN⟩ : N)⁻¹ * ⟨x, hxN⟩) = 1 := by
    rw [map_mul, map_inv, componentNormalizerAction_eq_conj J (n := ⟨j, hjN⟩) rfl, hq',
      inv_mul_cancel]
  have hcK : (j : EscapingQuotient z)⁻¹ * x ∈
      Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
    mem_centralizer_of_componentNormalizerAction_eq_one J hφ
  have hjS := h.mem_sylowImage_of_mul_mem_normalizer hxS hxN j.2 hcK (mul_inv_cancel_left _ _)
  exact ⟨j, hjS, j.2, _, (escapingSylowImage S z).mul_mem
    ((escapingSylowImage S z).inv_mem hjS) hxS, hcK, mul_inv_cancel_left _ _⟩

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
