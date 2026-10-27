module

public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineFi22
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi24

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.SporadicRefine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG Subgroup CFSG.Blueprint CFSG.LocalCores
open CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Fi24 (R J JR tR D24 jR cls)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Sporadic.Schreier (fixSub)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem not_fixedCentralizerTwoFree_of_involution {S : Type} [Group S] {σ : MulAut S}
    {D : Subgroup (fixedSubgroup σ)} {z : fixedSubgroup σ} (hz1 : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hzc : ∀ d ∈ D, z * d = d * z) : ¬ F4Pilot.FixedCentralizerTwoFree σ D := by
  intro hfree
  have hz1' : (z : S) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzo : orderOf (z : S) = 2 := by
    refine orderOf_eq_prime ?_ hz1'
    rw [← Subgroup.coe_pow, hz2, Subgroup.coe_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 (zpowers (z : S)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hle1 : zpowers (z : S) ≤
      centralizer ((D.map (fixedSubgroup σ).subtype : Subgroup S) : Set S) := by
    rw [zpowers_le, mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact (congrArg Subtype.val (hzc y hy)).symm
  have hle2 : zpowers (z : S) ≤ fixedSubgroup σ := by
    rw [zpowers_le]
    exact z.2
  have hbot := hfree _ hU hle1 hle2
  apply hz1'
  have : (z : S) ∈ zpowers (z : S) := mem_zpowers _
  rw [hbot, mem_bot] at this
  exact this

theorem exists_involution_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (H : Subgroup X)
    (K : Subgroup Y) (e : H ≃* K) {B : Subgroup H}
    (h : ∃ j : K, j ≠ 1 ∧ j ^ 2 = 1 ∧ ∀ b ∈ B.map e.toMonoidHom, j * b = b * j) :
    ∃ j : H, j ≠ 1 ∧ j ^ 2 = 1 ∧ ∀ b ∈ B, j * b = b * j := by
  obtain ⟨j, hj1, hj2, hjc⟩ := h
  refine ⟨e.symm j, fun h1 => hj1 ?_, ?_, fun b hb => ?_⟩
  · rw [← e.apply_symm_apply j, h1, map_one]
  · rw [← map_pow, hj2, map_one]
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hjc (e b) ⟨b, hb, rfl⟩

theorem component_quotient_mulEquiv_subgroup {X Y : Type*} [Group X] [Group Y] (H : Subgroup X)
    (K : Subgroup Y) (e : H ≃* K) {B : Subgroup H} (hB : IsComponent B) :
    IsComponent (B.map e.toMonoidHom) ∧
      Nat.card (B ⧸ Subgroup.center B) =
        Nat.card (B.map e.toMonoidHom ⧸ Subgroup.center (B.map e.toMonoidHom)) :=
  component_quotient_mulEquiv e hB

section Fi24


theorem fi24CJ_triple_exists_involution {r : R} {k₁ k₂ k₃ : Fin 306936}
    (hne : k₁ ≠ k₂ ∧ k₁ ≠ k₃ ∧ k₂ ≠ k₃) (hr : r = cls k₁ * cls k₂ * cls k₃)
    (hfix : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), r • k = k)
    (hcomm : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k)
    (hchar : ∀ k : Fin 306936, r • k = k → (∀ l : Fin 306936, r • l = l →
      cls k * cls l = cls l * cls k) → k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)))
    {B : Subgroup (fi24CJ r)} (hB : IsComponent B) :
    ∃ j : fi24CJ r, j ≠ 1 ∧ j ^ 2 = 1 ∧ ∀ b ∈ B, j * b = b * j := by
  have m1 : k₁ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have m2 : k₂ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have m3 : k₃ ∈ ({k₁, k₂, k₃} : Set (Fin 306936)) := by simp
  have hY : (cls '' ({k₁, k₂, k₃} : Set (Fin 306936))).Finite := (Set.toFinite _).image cls
  have hY3 : (cls '' ({k₁, k₂, k₃} : Set (Fin 306936))).ncard ≤ 3 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
    have h1 := Set.ncard_insert_le k₁ ({k₂, k₃} : Set (Fin 306936))
    have h2 := Set.ncard_insert_le k₂ ({k₃} : Set (Fin 306936))
    rw [Set.ncard_singleton] at h2
    omega
  have hinv : ∀ c : fi24CJ r, ∀ y ∈ cls '' ({k₁, k₂, k₃} : Set (Fin 306936)),
      (jR.comp (fi24CJ r).subtype) c * y * ((jR.comp (fi24CJ r).subtype) c)⁻¹ ∈
        cls '' ({k₁, k₂, k₃} : Set (Fin 306936)) := by
    rintro c _ ⟨k, hk, rfl⟩
    exact ⟨jR c • k, fo24_triple_perm hfix hcomm hchar (mem_fi24CJ.1 c.2) hk,
      CFSG.Sporadic.Fi24.cls_smul_R (jR c) k⟩
  have key : ∀ b ∈ B, ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)),
      Commute (jR (b : J)) (cls k) := by
    intro b hb k hk
    have h0 : jR (b : J) * cls k * (jR (b : J))⁻¹ = cls k :=
      @conj_eq_of_perfect_of_invariant_hom R (fi24CJ r) inferInstance inferInstance
        (jR.comp (fi24CJ r).subtype) _ hY hY3 hinv B hB.1.1 b hb (cls k) ⟨k, hk, rfl⟩
    show jR (b : J) * cls k = cls k * jR (b : J)
    calc jR (b : J) * cls k = jR (b : J) * cls k * (jR (b : J))⁻¹ * jR (b : J) := by group
      _ = cls k * jR (b : J) := by rw [h0]
  have hfx : ∀ k ∈ ({k₁, k₂, k₃} : Set (Fin 306936)), ∀ k' ∈ ({k₁, k₂, k₃} : Set (Fin 306936)),
      Commute (cls k) (cls k') := fun k hk k' hk' => hcomm k hk k' (hfix k' hk')
  have h12 := hfx k₁ m1 k₂ m2
  have h13 := hfx k₁ m1 k₃ m3
  have h23 := hfx k₂ m2 k₃ m3
  have hout : ∀ k, cls k ∉ JR := fun k =>
    CFSG.Sporadic.Fi24.not_mem_JR_of_mem_D24 (CFSG.Sporadic.Fi24.cls_mem k)
  have hxJ : cls k₁ * cls k₂ ∈ JR :=
    (mul_mem_iff_of_index_two CFSG.Sporadic.Fi24.index_JR).2 (iff_of_false (hout k₁) (hout k₂))
  obtain ⟨j₀, hj₀⟩ : cls k₁ * cls k₂ ∈ jR.range := by
    rw [CFSG.Sporadic.Fi24.range_jR]
    exact hxJ
  have hsq : ∀ k, cls k * cls k = 1 := fun k => by
    rw [← sq, ← CFSG.Sporadic.Fi24.orderOf_mem_D24 (CFSG.Sporadic.Fi24.cls_mem k),
      pow_orderOf_eq_one]
  have hj₀r : j₀ ∈ fi24CJ r := by
    rw [mem_fi24CJ, hj₀, hr]
    exact ((Commute.refl _).mul_right (h13.mul_left h23)).eq
  refine ⟨⟨j₀, hj₀r⟩, fun h1 => ?_, ?_, fun b hb => ?_⟩
  · have h1' : j₀ = 1 := congrArg Subtype.val h1
    rw [h1', map_one] at hj₀
    have hk : cls k₁ = cls k₂ := by
      have e1 : cls k₁ * cls k₂ * cls k₂ = cls k₂ := by rw [← hj₀, one_mul]
      rwa [mul_assoc, hsq, mul_one] at e1
    exact hne.1 (CFSG.Sporadic.Fi24.cls_injective hk)
  · apply Subtype.ext
    apply CFSG.Sporadic.Fi24.jR_injective
    simp only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one]
    rw [hj₀, sq, show cls k₁ * cls k₂ * (cls k₁ * cls k₂) =
      cls k₁ * (cls k₂ * cls k₁) * cls k₂ by group, ← h12.eq,
      show cls k₁ * (cls k₁ * cls k₂) * cls k₂ = (cls k₁ * cls k₁) * (cls k₂ * cls k₂) by group,
      hsq, hsq, one_mul]
  · apply Subtype.ext
    apply CFSG.Sporadic.Fi24.jR_injective
    simp only [Subgroup.coe_mul, map_mul]
    rw [hj₀]
    exact (((key b hb k₁ m1).mul_right (key b hb k₂ m2)).eq).symm

open CFSG.Sporadic.Th in
theorem fi24CJ_outer_unitary_exists_involution {r : R} (hr2 : r * r = 1) (hrJ : r ∉ JR)
    {B : Subgroup (fi24CJ r)} (hB : IsComponent B)
    (hcard : Nat.card (B ⧸ Subgroup.center B) = 9196830720) :
    ∃ j : fi24CJ r, j ≠ 1 ∧ j ^ 2 = 1 ∧ ∀ b ∈ B, j * b = b * j := by
  have hr1 : r ≠ 1 := fun h => hrJ (h ▸ JR.one_mem)
  obtain ⟨s, hs, hsr⟩ := fi24_involution_class hr2 hr1
  obtain ⟨c, hc⟩ := (isConj_iff (α := R)).1 hsr
  have e : fi24CJ r ≃* fi24CJ s :=
    (MulEquiv.subgroupCongr (by rw [hc])).trans (fi24CJConj c s).symm
  refine exists_involution_of_mulEquiv _ _ e ?_
  obtain ⟨hB', hc'⟩ := component_quotient_mulEquiv_subgroup _ _ e hB
  rw [hc'] at hcard
  have hsJ : s ∉ JR := fun h => hrJ (by
    rw [← hc]
    exact CFSG.Sporadic.Fi24.normal_JR.conj_mem s h c)
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · rw [fi24CJ_tR_component hB'] at hcard
    norm_num at hcard
  · rw [fi24CJ_DT_component hB'] at hcard
    norm_num at hcard
  · obtain ⟨k₁, k₂, k₃, hne, hr', hfix, hcomm, hchar⟩ := fi24U2T_triple
    exact fi24CJ_triple_exists_involution hne hr' hfix hcomm hchar hB'
  · obtain ⟨k₁, k₂, k₃, hne, hr', hfix, hcomm, hchar⟩ := fi24U3T_triple
    exact fi24CJ_triple_exists_involution hne hr' hfix hcomm hchar hB'

theorem fi24_outer_not_twoFree_of_unitary {S : Type} [Group S]
    (e : S ≃* NativeSporadic.Fi24prime) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hcard : Nat.card (D ⧸ center D) = 9196830720) :
    ¬ F4Pilot.FixedCentralizerTwoFree σ D := by
  set θ : S ≃* J := e.trans CFSG.Sporadic.Fi24.fi24EquivJ
  have hσ2 : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  obtain ⟨r, hr⟩ := conjJ_surjective ((θ.symm.trans σ).trans θ)
  have hrx : ∀ x : S, θ (σ x) = CFSG.Sporadic.Fi24.conjJ r (θ x) := fun x => by
    rw [hr]
    show θ (σ x) = θ (σ (θ.symm (θ x)))
    rw [MulEquiv.symm_apply_apply]
  have hr2 : r * r = 1 := by
    apply CFSG.Sporadic.Fi24.conjJ_injective
    rw [map_mul, map_one, hr]
    refine MulEquiv.ext fun x => ?_
    show θ (σ (θ.symm (θ (σ (θ.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, ← MulAut.mul_apply, hσ2, MulAut.one_apply,
      MulEquiv.apply_symm_apply]
  have hrJ : r ∉ JR := by
    intro hJ
    obtain ⟨j, rfl⟩ : r ∈ jR.range := by rw [CFSG.Sporadic.Fi24.range_jR]; exact hJ
    apply hout
    refine ⟨θ.symm j, MulEquiv.ext fun x => θ.injective ?_⟩
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hrx,
      CFSG.Sporadic.Fi24.conjJ_jR, MulAut.conj_apply]
  have ψ : fixedSubgroup σ ≃* fi24CJ r :=
    (MulEquiv.subgroupCongr (fixedSubgroup_eq_fixSub σ)).trans (fixSubEquivCJ θ σ r hrx)
  obtain ⟨hD', hc'⟩ := component_quotient_mulEquiv_subgroup _ _ ψ hD
  rw [hc'] at hcard
  obtain ⟨z, hz1, hz2, hzc⟩ := exists_involution_of_mulEquiv _ _ ψ
    (fi24CJ_outer_unitary_exists_involution hr2 hrJ hD' hcard)
  exact not_fixedCentralizerTwoFree_of_involution hz1 hz2 hzc

end Fi24

end CFSG.SeitzReduction.SporadicRefine
