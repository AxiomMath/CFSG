module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneInner
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneAlt
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneDecide
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneOuter
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open Equiv

theorem perm_eq_one_of_forall_conj {τ : Perm (Fin 5)}
    (hτ : ∀ a : alternatingGroup (Fin 5), τ * (a : Perm (Fin 5)) * τ⁻¹ = a) : τ = 1 := by
  apply (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
    (by norm_num)).1
  rw [map_one]
  ext a
  rw [MulAut.conjNormal_apply, hτ a]
  rfl

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) [J.Normal] (P : Sylow 2 J)
  (hP : (P : Subgroup J).map J.subtype = escapingSylowImage S z ⊓ J)
include h

omit [J.Normal] in
include hP in
theorem normalizer_eq_embedImage :
    Subgroup.normalizer ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Subgroup (J ⧸ Subgroup.center J)) : Set (J ⧸ Subgroup.center J)) = embedImage H z J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eP⟩ := h.sylow_mulEquiv_quaternion_two P
  obtain ⟨e⟩ := h.nonempty_mulEquiv_alternatingGroup_five
  set Qs : Subgroup (J ⧸ Subgroup.center J) :=
    ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) :
      Sylow 2 (J ⧸ Subgroup.center J)) : Subgroup (J ⧸ Subgroup.center J)) with hQs
  have hmem : ∀ y, y ∈ Qs ↔ InFour P eP y := fun y =>
    (mem_sylowQuotient_iff P eP y).trans (h.inFour_iff P eP y).symm
  set N := Subgroup.normalizer (Qs : Set (J ⧸ Subgroup.center J)) with hN
  have hNB : N ≤ embedImage H z J := h.normalizer_le_embedImage P hP
  have h4 : 4 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := Qs))
    rwa [h.card_sylow_quotient] at this
  obtain ⟨hA, hB⟩ := h.fourGroup P eP e
  obtain ⟨d, hd1, hd3, hd, hdA, hdB⟩ := s5_exists_three_normalizing _ hA _ hB
  set d' : J ⧸ Subgroup.center J := e.symm ⟨d, Perm.mem_alternatingGroup.mpr hd1⟩ with hd'
  have hd'd : permOf e d' = d := by simp [hd', permOf]
  have hconj : ∀ y, InFour P eP y → InFour P eP (d' * y * d'⁻¹) := fun y hy =>
    h.inFour_conj_of_normalizes P eP e (by rwa [hd'd]) (by rwa [hd'd]) hy
  have hd'3 : d' * d' * d' = 1 := by
    apply permOf_injective e
    rw [permOf_mul, permOf_mul, hd'd, hd3, permOf_one]
  have hd'1 : d' ≠ 1 := fun h1 => hd (by rw [← hd'd, h1, permOf_one])
  have hd'N : d' ∈ N := by
    rw [hN, Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    refine ⟨hconj y, fun hy => ?_⟩
    have h1 := hconj _ (hconj _ hy)
    rwa [show d' * (d' * (d' * y * d'⁻¹) * d'⁻¹) * d'⁻¹ = y by
      calc d' * (d' * (d' * y * d'⁻¹) * d'⁻¹) * d'⁻¹ =
          (d' * d' * d') * y * (d' * d' * d')⁻¹ := by group
        _ = y := by rw [hd'3, one_mul, inv_one, mul_one]] at h1
  have h3 : 3 ∣ Nat.card N := by
    have hord : orderOf (⟨d', hd'N⟩ : N) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_three, ← mul_assoc, hd'3]) hd'1
    rw [← hord]
    exact orderOf_dvd_natCard _
  have h12 : 12 ∣ Nat.card N :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4
  have hB60 : Nat.card (embedImage H z J) ∣ 60 := by
    rw [← card_alternatingGroup_fin_five, ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hBne : Nat.card (embedImage H z J) ≠ 60 := fun h60 => h.embedImage_ne_top (by
    rw [← Subgroup.card_eq_iff_eq_top, h60, ← card_alternatingGroup_fin_five,
      ← Nat.card_congr e.toEquiv])
  have h12B : 12 ∣ Nat.card (embedImage H z J) := h12.trans (Subgroup.card_dvd_of_le hNB)
  have hB12 : Nat.card (embedImage H z J) = 12 := by
    obtain ⟨k, hk⟩ := h12B
    obtain ⟨l, hl⟩ := hB60
    rw [hk] at hl hBne
    have hkl : k * l = 5 := by
      have h60 : 12 * (k * l) = 12 * 5 := by rw [← mul_assoc, ← hl]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h60
    have hk5 : k ∣ 5 := ⟨l, hkl.symm⟩
    rcases (Nat.dvd_prime (by norm_num)).mp hk5 with hk1 | hk1
    · rw [hk, hk1]
    · exact absurd (by rw [hk1]) hBne
  have hN12 : 12 ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos h12
  exact Subgroup.eq_of_le_of_card_ge hNB (by rw [hB12]; exact hN12)

theorem action_mem_inner_of_mul_self_eq_one
    {x : EscapingQuotient z}
    (hxS : x ∈ escapingSylowImage S z) (hx2 : x * x = 1) :
    componentQuotientAction J x ∈ inner (J ⧸ Subgroup.center J) := by
  have hq := h.quotientData
  obtain ⟨e⟩ := h.nonempty_mulEquiv_alternatingGroup_five
  obtain ⟨P, hP⟩ := h.exists_sylow_inf h.component
  obtain ⟨eP⟩ := h.sylow_mulEquiv_quaternion_two P
  obtain ⟨σ, hσ'⟩ := exists_perm_of_mulEquiv e (componentQuotientAction J x)
  have hσ : ∀ y, permOf e (componentQuotientAction J x y) = σ * permOf e y * σ⁻¹ := hσ'
  by_cases hsign : Perm.sign σ = 1
  · refine ⟨e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩, ?_⟩
    ext y
    apply permOf_injective e
    rw [hσ y, MulAut.conj_apply, permOf_mul, permOf_mul, permOf_inv]
    simp [permOf]
  exfalso
  set φ := componentQuotientAction J with hφ
  have hσσ : σ * σ = 1 := by
    apply perm_eq_one_of_forall_conj
    intro a
    have h1 := hσ (φ x (e.symm a))
    rw [hσ (e.symm a)] at h1
    have h2 : φ x (φ x (e.symm a)) = e.symm a := by
      rw [← MulAut.mul_apply, ← map_mul, hx2, map_one, MulAut.one_apply]
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
  have hx1 : x ≠ 1 := fun h1 => hφx (by rw [h1, map_one])
  have hxz : x ≠ escapingBar z := fun h1 => hφx (by
    rw [h1]
    exact (h.action_eq_one_iff).mpr hq.bar_mem_component_centralizer)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
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
    refine permOf_of_inFour P eP e ((hmem _).mp (action_mem_sylowQuotient P hP hxS
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
  obtain ⟨c₀, hc₀, -, hc₀x⟩ := h.exists_lift_of_fixed hc'3 hc'fix
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

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
