module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714A7
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerA
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714Comp

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2
open scoped MatrixGroups

theorem map_fixedSubgroup_of_comm {G G' : Type} [Group G] [Group G'] (β : G ≃* G') {α : MulAut G}
    {α₀ : MulAut G'} (h : ∀ x, β (α x) = α₀ (β x)) :
    (fixedSubgroup G α).map β.toMonoidHom = fixedSubgroup G' α₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change α₀ (β x) = β x
    rw [← h]
    exact congrArg β hx
  · intro hy
    refine ⟨β.symm y, ?_, β.apply_symm_apply y⟩
    change α (β.symm y) = β.symm y
    apply β.injective
    rw [h, β.apply_symm_apply]
    exact hy

theorem Ivk714Hyp.exists_two_component {K P : Type} [Group K] [Finite K] [Group P] (e : K ≃* P)
    {z : MulAut K} {α : MulAut P} (hα : ∀ s, e (z s) = α (e s)) (h : Ivk714Hyp K z) :
    ∃ J : Subgroup P, J ≤ fixedSubgroup P α ∧
      CFSG.IsPComponent 2 (J.subgroupOf (fixedSubgroup P α)) ∧
      (∃ τ : ↥J →* alternatingGroup (Fin 7), Function.Surjective τ) ∧
      ∃ o : ℕ, Odd o ∧ Nat.card ↥J = 2520 * o := by
  obtain ⟨B, hB, -, ⟨hq⟩, hodd⟩ := h.exists_component
  have hBle : B ≤ fixedSubgroup K z := hB.1
  have hBc : CFSG.IsComponent (B.subgroupOf (fixedSubgroup K z)) :=
    (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hBle).mp hB
  have hBq : CFSG.IsQuasisimple ↥B :=
    (LocalAnalysis.ComponentInitial.isQuasisimple_congr (subgroupOfEquivOfLe hBle)).mp hBc.1
  have hcardB : Nat.card ↥B = 2520 * Nat.card ↥(center ↥B) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥B), Nat.card_congr hq.toEquiv,
      card_alt7]
  have hBe : Even (Nat.card ↥B) := by
    rw [hcardB]
    exact (Nat.even_mul).mpr (Or.inl (by decide))
  have hBP : CFSG.IsPComponent 2 (B.subgroupOf (fixedSubgroup K z)) :=
    CFSG.ComponentClassification.CatFactsSp4.isPComponent_two_of_quasisimple' hBle hBq hBc.2 hBe
  have hmap := map_fixedSubgroup_of_comm e hα
  have hJP := CFSG.ComponentClassification.CatFactsSp4.isPComponent_map_subgroupOf 2 e hBle hBP
  rw [hmap] at hJP
  have hJle : B.map e.toMonoidHom ≤ fixedSubgroup P α := by
    rw [← hmap]
    exact Subgroup.map_mono hBle
  let ψ : ↥B ≃* ↥(B.map e.toMonoidHom) := B.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨B.map e.toMonoidHom, hJle, hJP, ?_, Nat.card ↥(center ↥B), hodd, ?_⟩
  · refine ⟨(hq.toMonoidHom.comp (QuotientGroup.mk' (center ↥B))).comp ψ.symm.toMonoidHom, ?_⟩
    exact (hq.surjective.comp (QuotientGroup.mk'_surjective _)).comp ψ.symm.surjective
  · rw [← Nat.card_congr ψ.toEquiv, hcardB]

theorem false_of_surjective_sl2 {k : Type} [Field k] [Finite k] (hodd : Odd (Nat.card k))
    (h5 : 5 ≤ Nat.card k) {J : Type*} [Group J] (τ : J →* alternatingGroup (Fin 7))
    (hτ : Function.Surjective τ) (φ : SL(2, k) →* J) (hφ : Function.Surjective φ) : False :=
  not_surjective_sl2_alt7 hodd h5 (τ.comp φ) (hτ.comp hφ)

end CFSG.GH74.GLS.IVK
