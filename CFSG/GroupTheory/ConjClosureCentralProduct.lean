module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.LocalCores
open scoped commutatorElement

variable {Y : Type*} [Group Y] [Finite Y]

theorem commutatorElement_mem_of_isMulCommutative_normalizerQuotient {P : Subgroup Y}
    (hP : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient P)) {u v : Y}
    (hu : u ∈ Subgroup.normalizer (P : Set Y)) (hv : v ∈ Subgroup.normalizer (P : Set Y)) :
    ⁅u, v⁆ ∈ P := by
  have h1 : (TauCeti.Subgroup.normalizerQuotientMk P)
        (⟨u, hu⟩ : ↥(Subgroup.normalizer (P : Set Y))) *
      (TauCeti.Subgroup.normalizerQuotientMk P)
        (⟨v, hv⟩ : ↥(Subgroup.normalizer (P : Set Y))) =
      (TauCeti.Subgroup.normalizerQuotientMk P)
        (⟨v, hv⟩ : ↥(Subgroup.normalizer (P : Set Y))) *
        (TauCeti.Subgroup.normalizerQuotientMk P)
          (⟨u, hu⟩ : ↥(Subgroup.normalizer (P : Set Y))) :=
    hP.is_comm.comm _ _
  have h2 : (TauCeti.Subgroup.normalizerQuotientMk P)
      ⁅(⟨u, hu⟩ : ↥(Subgroup.normalizer (P : Set Y))),
        (⟨v, hv⟩ : ↥(Subgroup.normalizer (P : Set Y)))⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h1
  rw [TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff] at h2
  simpa [commutatorElement_def] using h2

theorem commutatorElement_mem_of_isMulCommutative_subgroupOf {K P : Subgroup Y}
    (h : IsMulCommutative (TauCeti.Subgroup.normalizerQuotient (P.subgroupOf K)))
    {u v : Y} (hu : u ∈ K) (hv : v ∈ K) (huN : u ∈ Subgroup.normalizer (P : Set Y))
    (hvN : v ∈ Subgroup.normalizer (P : Set Y)) : ⁅u, v⁆ ∈ P := by
  have hmem : ∀ (w : Y) (hw : w ∈ K), w ∈ Subgroup.normalizer (P : Set Y) →
      (⟨w, hw⟩ : ↥K) ∈ Subgroup.normalizer ((P.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    intro w hw hwN
    rw [Subgroup.mem_normalizer_iff]
    intro k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.1 hwN (k : Y)
  have hc := commutatorElement_mem_of_isMulCommutative_normalizerQuotient h
    (hmem u hu huN) (hmem v hv hvN)
  rw [Subgroup.mem_subgroupOf] at hc
  simpa [commutatorElement_def] using hc

theorem isMulCommutative_normalizerQuotient_of_layer_eq_top (hY : CFSG.layer Y = ⊤)
    (S : Subgroup Y)
    (hK : ∀ K : CFSG.LocalCores.ComponentIndex Y,
      IsMulCommutative (TauCeti.Subgroup.normalizerQuotient ((S ⊓ K.1).subgroupOf K.1))) :
    IsMulCommutative (TauCeti.Subgroup.normalizerQuotient S) := by
  classical
  have key : ∀ (a : Y) (α : ∀ K : CFSG.LocalCores.ComponentIndex Y, K.1),
      CFSG.LocalCores.layerMul Y α = a → a ∈ Subgroup.normalizer (S : Set Y) →
      ∀ K : CFSG.LocalCores.ComponentIndex Y,
        ((α K : Y)) ∈ Subgroup.normalizer ((S ⊓ K.1 : Subgroup Y) : Set Y) := by
    intro a α hα ha K
    have hstep : ∀ k : Y, k ∈ K.1 → a * k * a⁻¹ = (α K : Y) * k * (α K : Y)⁻¹ := by
      intro k hk
      have hcomm := CFSG.LocalCores.commute_layerMul_update α K hk
      have huk : CFSG.LocalCores.layerMul Y (Function.update α K 1) * k *
          (CFSG.LocalCores.layerMul Y (Function.update α K 1))⁻¹ = k := by
        rw [← hcomm.eq]
        group
      calc a * k * a⁻¹ = (CFSG.LocalCores.layerMul Y α) * k *
            (CFSG.LocalCores.layerMul Y α)⁻¹ := by rw [hα]
        _ = ((α K : Y) * CFSG.LocalCores.layerMul Y (Function.update α K 1)) * k *
              ((α K : Y) * CFSG.LocalCores.layerMul Y (Function.update α K 1))⁻¹ := by
              rw [CFSG.LocalCores.layerMul_eq_mul_update α K]
        _ = (α K : Y) * k * (α K : Y)⁻¹ := by
              rw [show ((α K : Y) * CFSG.LocalCores.layerMul Y (Function.update α K 1)) * k *
                ((α K : Y) * CFSG.LocalCores.layerMul Y (Function.update α K 1))⁻¹ =
                (α K : Y) * (CFSG.LocalCores.layerMul Y (Function.update α K 1) * k *
                  (CFSG.LocalCores.layerMul Y (Function.update α K 1))⁻¹) * (α K : Y)⁻¹
                from by group]
              rw [huk]
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      have h1 : a * k * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 ha k).1 hk.1
      exact ⟨by rwa [← hstep k hk.2], K.1.mul_mem (K.1.mul_mem (α K).2 hk.2) (K.1.inv_mem (α K).2)⟩
    · intro hk
      have hkK : k ∈ K.1 := by
        have h1 : (α K : Y) * k * (α K : Y)⁻¹ ∈ K.1 := hk.2
        have h2 : k = (α K : Y)⁻¹ * ((α K : Y) * k * (α K : Y)⁻¹) * (α K : Y) := by group
        rw [h2]
        exact K.1.mul_mem (K.1.mul_mem (K.1.inv_mem (α K).2) h1) (α K).2
      have h1 : a * k * a⁻¹ ∈ S := by rw [hstep k hkK]; exact hk.1
      exact ⟨(Subgroup.mem_normalizer_iff.1 ha k).2 h1, hkK⟩
  have hcommutator : ∀ a ∈ Subgroup.normalizer (S : Set Y),
      ∀ b ∈ Subgroup.normalizer (S : Set Y), ⁅a, b⁆ ∈ S := by
    intro a ha b hb
    obtain ⟨α, hα⟩ := CFSG.LocalCores.exists_layerMul_eq (hY ▸ Subgroup.mem_top a)
    obtain ⟨β, hβ⟩ := CFSG.LocalCores.exists_layerMul_eq (hY ▸ Subgroup.mem_top b)
    have hαN := key a α hα ha
    have hβN := key b β hβ hb
    have hcoord : ∀ K : CFSG.LocalCores.ComponentIndex Y, ⁅(α K : Y), (β K : Y)⁆ ∈ S ⊓ K.1 :=
      fun K => commutatorElement_mem_of_isMulCommutative_subgroupOf (hK K) (α K).2 (β K).2
        (hαN K) (hβN K)
    rw [show ⁅a, b⁆ = CFSG.LocalCores.layerMul Y ⁅α, β⁆ from by
      rw [map_commutatorElement, hα, hβ]]
    exact CFSG.LocalCores.layerMul_mem _ (fun K => (hcoord K).1)
  refine IsMulCommutative.of_comm fun x y => ?_
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hmem : ⁅((b : ↥(Subgroup.normalizer (S : Set Y))) : Y)⁻¹,
      ((a : ↥(Subgroup.normalizer (S : Set Y))) : Y)⁻¹⁆ ∈ S :=
    hcommutator _ (Subgroup.inv_mem _ b.2) _ (Subgroup.inv_mem _ a.2)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hcoe : (((a * b)⁻¹ * (b * a) : ↥(Subgroup.normalizer (S : Set Y))) : Y) =
      ⁅((b : ↥(Subgroup.normalizer (S : Set Y))) : Y)⁻¹,
        ((a : ↥(Subgroup.normalizer (S : Set Y))) : Y)⁻¹⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  rw [hcoe]
  exact hmem

end CFSG.GroupTheory
