module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneBender
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.RankOneCases

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  {J : Subgroup (EscapingQuotient z)}

abbrev swapComponent (J : Subgroup (EscapingQuotient z)) (s : EscapingQuotient z) :
    Subgroup (EscapingQuotient z) :=
  J.map (MulAut.conj s).toMonoidHom

omit [Finite G] in
theorem swapComponent_ne {s : EscapingQuotient z}
    (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z))) : swapComponent J s ≠ J :=
  fun heq => hs (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)

namespace RankOneSetting

variable (h : RankOneSetting G S H z J) {s : EscapingQuotient z}
  (hsS : s ∈ escapingSylowImage S z)
  (hs : s ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
include h

theorem swap_isComponent : CFSG.IsComponent (swapComponent J s) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj s) h.component

include hs

theorem map_conj_eq_swap {m : EscapingQuotient z}
    (hm : m ∉ Subgroup.normalizer (J : Set (EscapingQuotient z))) :
    J.map (MulAut.conj m).toMonoidHom = swapComponent J s :=
  h.component_eq_of_ne (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj m) h.component)
    (h.swap_isComponent)
    (fun heq => hm (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)) (swapComponent_ne hs)

theorem inv_mul_mem_normalizer_swap {u v : EscapingQuotient z}
    (hu : u ∉ Subgroup.normalizer (J : Set (EscapingQuotient z)))
    (hv : v ∉ Subgroup.normalizer (J : Set (EscapingQuotient z))) :
    u⁻¹ * v ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) :=
  inv_mul_mem_normalizer_of_map_eq
    ((h.map_conj_eq_swap hs hv).trans (h.map_conj_eq_swap hs hu).symm)

theorem normalizer_index_swap :
    (Subgroup.normalizer (J : Set (EscapingQuotient z))).index = 2 := by
  set N := Subgroup.normalizer (J : Set (EscapingQuotient z))
  rw [Subgroup.index_eq_two_iff]
  refine ⟨s, fun b => ?_⟩
  by_cases hb : b ∈ N
  · refine Or.inr ⟨hb, fun hbs => hs ?_⟩
    have := N.mul_mem (N.inv_mem hb) hbs
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, hb⟩
    have := h.inv_mul_mem_normalizer_swap hs (u := b⁻¹) (v := s)
      (fun hb' => hb (by simpa using N.inv_mem hb')) hs
    rwa [inv_inv] at this

theorem normalizer_normal_swap : (Subgroup.normalizer (J : Set (EscapingQuotient z))).Normal :=
  Subgroup.normal_of_index_eq_two (h.normalizer_index_swap hs)

theorem swap_le_centralizer :
    swapComponent J s ≤ Subgroup.centralizer (J : Set (EscapingQuotient z)) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    ((CFSG.LocalCores.distinct_components_commute (h.swap_isComponent) h.component).resolve_left
      (swapComponent_ne hs))

omit hs in
include hsS in
theorem swap_setting : RankOneSetting G S H z (swapComponent J s) := by
  refine ⟨h.square, h.swap_isComponent, fun hle => h.not_le ?_, fun x hx hx2 =>
    h.eq_bar_of_mem_component (h.swap_isComponent) hx hx2⟩
  intro j hj
  have hsj : s * j * s⁻¹ ∈ escapingImage H z := hle ⟨j, hj, rfl⟩
  have hsH := h.sylowImage_le hsS
  have := (escapingImage H z).mul_mem ((escapingImage H z).mul_mem
    ((escapingImage H z).inv_mem hsH) hsj) hsH
  simpa [mul_assoc] using this

theorem mem_normalizer_of_mul_self_eq_one {x : EscapingQuotient z}
    (hxS : x ∈ escapingSylowImage S z) (hx2 : x * x = 1) :
    x ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) := by
  have hq := h.quotientData
  by_contra hx
  have hxJ := h.map_conj_eq_swap hs hx
  have hx1 : x ≠ 1 := fun h1 => hx (h1 ▸ Subgroup.one_mem _)
  have hzN : escapingBar z ∈ Subgroup.normalizer (J : Set (EscapingQuotient z)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [show escapingBar z * y * (escapingBar z)⁻¹ = y by
      rw [← (hq.commute_bar y).eq, mul_inv_cancel_right]]
  have hxz : x ≠ escapingBar z := fun h1 => hx (h1 ▸ hzN)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hJ' := h.swap_le_centralizer hs
  have hxj : ∀ j ∈ J, x * j * x⁻¹ ∈ Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    intro j hj
    apply hJ'
    rw [← hxJ]
    exact ⟨j, hj, rfl⟩
  have hconj : ∀ j ∈ J, ∀ b ∈ J, b ∈ escapingImage H z → j * b * j⁻¹ ∈ escapingImage H z := by
    intro j hj b hb hbH
    have hdx : j * (x * j * x⁻¹) ∈ Subgroup.centralizer ({x} : Set (EscapingQuotient z)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hc : (x * j * x⁻¹) * j = j * (x * j * x⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hxj j hj) j hj).symm
      rw [hxinv] at hc ⊢
      calc j * (x * j * x) * x = (x * j * x * j) * x := by rw [hc]
        _ = x * (j * (x * j * x)) := by group
    have hdH : j * (x * j * x⁻¹) ∈ escapingImage H z :=
      hq.involution_centralizer_le (h.sylowImage_le hxS) hxo hxz hdx
    have hdb : j * (x * j * x⁻¹) * b * (j * (x * j * x⁻¹))⁻¹ = j * b * j⁻¹ := by
      have hc : (x * j * x⁻¹) * b = b * (x * j * x⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp (hxj j hj) b hb).symm
      rw [mul_inv_rev]
      calc j * (x * j * x⁻¹) * b * ((x * j * x⁻¹)⁻¹ * j⁻¹) =
          j * ((x * j * x⁻¹) * b) * (x * j * x⁻¹)⁻¹ * j⁻¹ := by group
        _ = j * b * j⁻¹ := by rw [hc]; group
    rw [← hdb]
    exact (escapingImage H z).mul_mem ((escapingImage H z).mul_mem hdH hbH)
      ((escapingImage H z).inv_mem hdH)
  have hBn : (embedImage H z J).Normal := by
    constructor
    rintro _ ⟨b, hb, rfl⟩ g
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center J) g
    rw [← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr ?_)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hconj j j.2 b b.2 (Subgroup.mem_subgroupOf.mp hb)
  have : IsSimpleGroup (J ⧸ Subgroup.center J) := h.component.1.2.1
  rcases hBn.eq_bot_or_eq_top with hbot | htop
  · obtain ⟨a, haS, haJ, ha2⟩ := h.exists_sq_eq_bar h.component
    have haB : QuotientGroup.mk' (Subgroup.center J) ⟨a, haJ⟩ ∈ embedImage H z J :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (h.sylowImage_le haS))
    rw [hbot, Subgroup.mem_bot] at haB
    have := h.orderOf_mk_eq_two (t := ⟨a, haJ⟩) ha2
    rw [haB, orderOf_one] at this
    exact absurd this (by decide)
  · exact h.embedImage_ne_top htop

end RankOneSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
