module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
public import CFSG.FeitThompson.Representations.CoprimeInvariantCharacterInduction
import CFSG.FeitThompson.Representations.NonprincipalRowRestrictionsDetectCores
import CFSG.FeitThompson.Representations.AbelianInertiaInducedBlock
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {L : Type*} [Group L] {K W₁ W₂ H U : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

structure IsMinimalAbelianCore (K W₁ W₂ H U : Subgroup L) : Prop where
  normal : H.Normal
  isMulCommutative_core : IsMulCommutative ↥H
  isMulCommutative_compl : IsMulCommutative ↥U
  right_le : W₂ ≤ H
  sup_eq : H ⊔ U = K
  inf_eq_bot : H ⊓ U = ⊥
  le_normalizer : W₁ ≤ normalizer (U : Set L)
  prime_natCard : (Nat.card ↥W₁).Prime
  minimal : ∀ M ≤ H, U ≤ normalizer (M : Set L) → W₁ ≤ normalizer (M : Set L) → M = ⊥ ∨ M = H

theorem coreProduct_eq_core_of_coreCentralizer_eq_bot [H.Normal]
    (hC : coreCentralizer H U = ⊥) : coreProduct H U = H := by
  refine SetLike.coe_injective ?_
  rw [coe_coreProduct, hC]
  simp

theorem relIndex_coreCentralizer_eq_natCard (hC : coreCentralizer H U = ⊥) :
    (coreCentralizer H U).relIndex U = Nat.card ↥U := by
  rw [hC, Subgroup.relIndex_bot_left]

namespace IsMinimalAbelianCore

theorem core_le (hc : IsMinimalAbelianCore K W₁ W₂ H U) : H ≤ K := hc.sup_eq ▸ le_sup_left

theorem compl_le (hc : IsMinimalAbelianCore K W₁ W₂ H U) : U ≤ K := hc.sup_eq ▸ le_sup_right

theorem coreProduct_le (hc : IsMinimalAbelianCore K W₁ W₂ H U) : coreProduct H U ≤ K :=
  hc.sup_eq ▸ coreProduct_le_sup H U

theorem core_ne_bot (h : IsPrimeCyclicTIHyp K W₁ W₂) (hc : IsMinimalAbelianCore K W₁ W₂ H U) :
    H ≠ ⊥ := fun hH => h.right_ne_bot (le_bot_iff.1 (hH ▸ hc.right_le))

theorem sup_left_eq_top (h : IsPrimeCyclicTIHyp K W₁ W₂) : K ⊔ W₁ = ⊤ := by
  refine (Subgroup.eq_top_iff' _).2 fun g => ?_
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
  exact mul_mem ((le_sup_left : K ≤ K ⊔ W₁) hk) ((le_sup_right : W₁ ≤ K ⊔ W₁) hw)

theorem coprime_natCard_compl [Finite L] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U) : (Nat.card ↥W₁).Coprime (Nat.card ↥U) :=
  h.coprime_natCard.symm.coprime_dvd_right (Subgroup.card_dvd_of_le hc.compl_le)

theorem primeTIres_conj_eq [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (j : Irr ↥W₂) (t : L) (x y : ↥K)
    (hxy : (y : L) = t⁻¹ * (x : L) * t) : h.primeTIres σ j y = h.primeTIres σ j x := by
  have hcf : h.primeTIirr σ (principalIrr ↥W₁) j ∈ classFun L :=
    Irr_subset_classFun (h.primeTIirr_principal_left_mem_Irr hσ j)
  rw [h.primeTIres_apply, h.primeTIres_apply, hxy]
  simpa using classFun.apply_conj hcf (x : L) t⁻¹

section Main

variable [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]

theorem exists_linearChar_primeTIres [Fintype ↥K] [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hc : IsMinimalAbelianCore K W₁ W₂ H U)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∃ ψ : ↥(coreProduct H U) → ℂ, ψ ∈ Irr ↥(coreProduct H U) ∧ ψ 1 = 1 ∧
      (∃ x : ↥(coreProduct H U), (x : L) ∈ H ∧ ψ x ≠ 1) ∧
      h.primeTIres σ j = indClassFun ((coreProduct H U).subgroupOf K)
        (ψ ∘ Subgroup.subgroupOfEquivOfLe hc.coreProduct_le) ∧
      h.primeTIrow σ j = indClassFun (coreProduct H U) ψ := by
  have hnormal := hc.normal
  have hcomm₁ := hc.isMulCommutative_core
  have hcomm₂ := hc.isMulCommutative_compl
  have hTK := hc.coreProduct_le
  have hrow := h.indClassFun_primeTIres hσ j
  have hsup := hc.sup_eq
  subst hsup
  obtain ⟨ψ₀, hψ₀Irr, hψ₀1, ⟨x₀, hx₀H, hx₀⟩, hind⟩ :=
    exists_linearChar_eq_indClassFun_coreProduct (N := H) (U := U) (Q := W₁)
      (hc.core_ne_bot h) hc.inf_eq_bot (sup_left_eq_top h) h.inf_eq_bot hc.le_normalizer
      hc.prime_natCard rfl (coprime_natCard_compl h hc) hc.minimal
      (h.primeTIres_mem_Irr hσ j) (h.exists_mem_primeTIres_ne hσ hc.right_le hj)
      (fun t _ x y hxy => primeTIres_conj_eq h hσ j t x y hxy)
  set e := Subgroup.subgroupOfEquivOfLe hTK with he
  refine ⟨ψ₀ ∘ e.symm, ?_, ?_, ⟨e x₀, ?_, ?_⟩, ?_, ?_⟩
  · exact mem_Irr_of_comp_mulEquiv e (by simpa [Function.comp_assoc] using hψ₀Irr)
  · simpa using hψ₀1
  · simpa [he] using hx₀H
  · simpa using hx₀
  · rw [hind]; congr 1
  · rw [← hrow, hind,
      ← AbelianInertiaBlock.indClassFun_indClassFun (H := coreProduct H U) (H ⊔ U) hTK
        (ψ₀ ∘ e.symm)]
    congr 2

theorem primeTIres_one_eq_relIndex (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIres σ j 1 = ((coreCentralizer H U).relIndex U : ℂ) := by
  have hnormal := hc.normal
  have hcomm₁ := hc.isMulCommutative_core
  have hcomm₂ := hc.isMulCommutative_compl
  have : Fintype ↥K := Fintype.ofFinite _
  have hsup := hc.sup_eq
  subst hsup
  exact apply_one_eq_relIndex_coreCentralizer (Q := W₁)
    (hc.core_ne_bot h) hc.inf_eq_bot (sup_left_eq_top h) h.inf_eq_bot hc.le_normalizer
    hc.prime_natCard rfl (coprime_natCard_compl h hc) hc.minimal
    (h.primeTIres_mem_Irr hσ j) (h.exists_mem_primeTIres_ne hσ hc.right_le hj)
    (fun t _ x y hxy => primeTIres_conj_eq h hσ j t x y hxy)

theorem primeTIres_eq_zero_of_notMem (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    {x : ↥K} (hx : (x : L) ∉ coreProduct H U) : h.primeTIres σ j x = 0 := by
  have hnormal := hc.normal
  have hcomm₁ := hc.isMulCommutative_core
  have hcomm₂ := hc.isMulCommutative_compl
  have : Fintype ↥K := Fintype.ofFinite _
  have hsup := hc.sup_eq
  subst hsup
  exact eq_zero_of_notMem_coreProduct (Q := W₁)
    (hc.core_ne_bot h) hc.inf_eq_bot (sup_left_eq_top h) h.inf_eq_bot hc.le_normalizer
    hc.prime_natCard rfl (coprime_natCard_compl h hc) hc.minimal
    (h.primeTIres_mem_Irr hσ j) (h.exists_mem_primeTIres_ne hσ hc.right_le hj)
    (fun t _ x y hxy => primeTIres_conj_eq h hσ j t x y hxy) hx

theorem primeTIres_one_eq_natCard_of_coreCentralizer_eq_bot (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hc : IsMinimalAbelianCore K W₁ W₂ H U)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (hC : coreCentralizer H U = ⊥) : h.primeTIres σ j 1 = (Nat.card ↥U : ℂ) := by
  rw [primeTIres_one_eq_relIndex h hc hσ hj, relIndex_coreCentralizer_eq_natCard hC]

theorem primeTIres_eq_zero_of_notMem_core_of_coreCentralizer_eq_bot
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hc : IsMinimalAbelianCore K W₁ W₂ H U)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (hC : coreCentralizer H U = ⊥) {x : ↥K} (hx : (x : L) ∉ H) : h.primeTIres σ j x = 0 := by
  have hnormal := hc.normal
  exact primeTIres_eq_zero_of_notMem h hc hσ hj
    (by rwa [coreProduct_eq_core_of_coreCentralizer_eq_bot hC])

end Main

end IsMinimalAbelianCore

end CFSG.FeitThompson
