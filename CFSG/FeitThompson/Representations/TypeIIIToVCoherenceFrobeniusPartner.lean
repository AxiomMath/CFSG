module

public import CFSG.FeitThompson.Representations.TypeIIIVCoherentCrossedRowData
public import CFSG.FeitThompson.Representations.TypeIINonfrobeniusCrossedColumnData
public import CFSG.FeitThompson.Representations.TypeThreeFiveTypeIISupportDisjoint
public import CFSG.FeitThompson.Representations.CoherentRowColumnDisjointDadeSupport
public import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

variable {G : Type*} [Group G]

section Aux

variable [Fintype G] {W₁ W₂ : Subgroup G}

open scoped Classical in
theorem isEtaSetup_basisProdIrr (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    (hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω) :
    IsEtaSetup W₁ W₂ ω (fun i j => hW.basisProdIrr (i, j)) (hW.prodCharEta ω) where
  isometry := hω
  prod := by
    intro i j x y z hz
    have hzeq : z = ⟨(x : G) * (y : G), mul_mem (hW.left_le x.2) (hW.right_le y.2)⟩ :=
      Subtype.ext hz
    rw [hW.coe_basisProdIrr_apply, hzeq, hW.prodChar_apply_mul]
  eta_eq := fun i j => hW.prodCharEta_eq_coe_apply i j

open CFSG.FeitThompson.Prep05 in
open scoped Classical in
theorem cyclicTIIsometry_data {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G}
    (hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω) :
    (∀ f g, cfIP ((ω f : G → ℂ)) ((ω g : G → ℂ)) =
        cfIP ((f : ↥(W₁ ⊔ W₂) → ℂ)) ((g : ↥(W₁ ⊔ W₂) → ℂ))) ∧
      (∀ f : classFun ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) ∈ virtualChars ↥(W₁ ⊔ W₂) →
        (ω f : G → ℂ) ∈ virtualChars G) ∧
      (∀ f : classFun ↥(W₁ ⊔ W₂), (f : ↥(W₁ ⊔ W₂) → ℂ) = 1 → (ω f : G → ℂ) = 1) ∧
      (∀ f : classFun ↥(W₁ ⊔ W₂),
        (∀ z : ↥(W₁ ⊔ W₂), (z : G) ∉ cyclicTIset W₁ W₂ → (f : ↥(W₁ ⊔ W₂) → ℂ) z = 0) →
        (ω f : G → ℂ) = indToTop (W₁ ⊔ W₂) (f : ↥(W₁ ⊔ W₂) → ℂ)) := by
  refine ⟨fun f g => ?_, hω.map_virtualChars, fun f hf => ?_, fun f hf => ?_⟩
  · rw [cfIP_eq_cfInner, cfIP_eq_cfInner, hω.inner_eq]
  · have hfp : f = principalClassFun ↥(W₁ ⊔ W₂) := Subtype.ext (by rw [hf, coe_principalClassFun])
    rw [hfp, hω.map_principalClassFun, coe_principalClassFun]
  · rw [indToTop_eq_indClassFun]
    refine hω.eq_indClassFun f fun z hz => hf z ?_
    rwa [cyclicTIset_eq_cyclicTIDiff]

end Aux

theorem exists_ne_principalIrr {W : Subgroup G} [Finite G] (hne : W ≠ ⊥) (hcyc : IsCyclic ↥W) :
    ∃ j : ↑(Irr ↥W), j ≠ principalIrr ↥W := by
  have : IsMulCommutative ↥W := hcyc.isMulCommutative
  have hcard : Nat.card ↑(Irr ↥W) = Nat.card ↥W := card_Irr_eq_card_of_isMulCommutative
  have h1 : 1 < Nat.card ↑(Irr ↥W) := by
    rw [hcard]; exact (Subgroup.one_lt_card_iff_ne_bot W).2 hne
  have : Nontrivial ↑(Irr ↥W) := Finite.one_lt_card_iff_nontrivial.mp h1
  exact exists_ne _

theorem conjClosure_fixedSet_eq [Finite G] (N : Subgroup G) :
    CFSG.FeitThompson.Prep05.conjClosure
        (CFSG.FeitThompson.Prep05.fixedSet (⁅N, N⁆ : Subgroup G) (CFSG.FeitThompson.Prep05.hallCoreOf N))
      = ⋃ g : G, (fun x => g⁻¹ * x * g) ''
          {a | a ∈ ((⁅N, N⁆ : Subgroup G) : Set G) \ {1} ∧
            Prep06.hallCoreIn N ⊓ centralizer ({a} : Set G) ≠ ⊥} := by
  have hbase : CFSG.FeitThompson.Prep05.fixedSet (⁅N, N⁆ : Subgroup G) (CFSG.FeitThompson.Prep05.hallCoreOf N)
      = {a | a ∈ ((⁅N, N⁆ : Subgroup G) : Set G) \ {1} ∧
          Prep06.hallCoreIn N ⊓ centralizer ({a} : Set G) ≠ ⊥} := by
    ext a
    simp only [CFSG.FeitThompson.Prep05.mem_fixedSet, CFSG.FeitThompson.Prep05.centralizerIn_eq,
      centralizer_coe_zpowers, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff,
      CFSG.FeitThompson.Prep05.hallCoreOf_eq, Prep06.hallCoreIn_eq]
    tauto
  rw [CFSG.FeitThompson.Prep05.conjClosure, hbase]
  rfl

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson Subgroup CFSG.FeitThompson.Prep06

universe u

open scoped Classical in
theorem FPF_type_iii_v_coherence_forces_frobenius_partner
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FPF_kappa_positive_core_derived_support_disjoint.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₅ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (h₆ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₇ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FPF_type_iii_v_coherence_forces_frobenius_partner.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc hcoh N E hN hNII hcN e heE he1
  by_contra hne
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := CrossedRowData.isCyclicTIPair_sup hG.odd hc
  obtain ⟨ω, hω⟩ := hW.exists_isCyclicTIIsometry
  obtain ⟨d, δ, ρ, hd1, hδ, hρ, hρne, hρη, hρsupp, hrow⟩ :=
    FPF_type_iii_v_coherent_crossed_row_data h₂ h₄ h₅ h₆ h₇ G hG M U W₁ W₂ hM htype hc hcoh
      ω (fun i j => hW.basisProdIrr (i, j)) (hW.prodCharEta ω)
      (isEtaSetup_basisProdIrr hW hω)
  obtain ⟨j₀, hj₀⟩ := exists_ne_principalIrr hc.ne_bot_W₂ hc.isCyclic_W₂
  have hfsupp := hrow j₀ hj₀
  have hMSO : _root_.CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd, hG.simple, hG.nonabelian, hG.solvable⟩
  obtain ⟨hω1, hω2, hω3, hω4⟩ := cyclicTIIsometry_data (W₁ := W₁) (W₂ := W₂) hω
  obtain ⟨i₁, hi₁, ε, hε, lam, hlamZ, hlamS, hlamne, hlamη, hlamD, hgsupp⟩ :=
    FPF_type_ii_nonfrobenius_crossed_column_data.{u, u} h₇ h₈ G hMSO N E W₁ W₂ hN hNII hcN
      ↑(Irr ↥W₁) ↑(Irr ↥W₂) Subtype.val Subtype.val (principalIrr ↥W₁) (principalIrr ↥W₂)
      Subtype.val_injective Subtype.range_coe (coe_principalIrr _)
      Subtype.val_injective Subtype.range_coe (coe_principalIrr _)
      (fun i j => (hW.basisProdIrr (i, j) : ↥(W₁ ⊔ W₂) → ℂ))
      (by
        intro i j x y hx hy hxy
        rw [hW.coe_basisProdIrr_apply]
        exact hW.prodChar_apply_mul _ _ hx hy)
      ω hω1 hω2 hω3 hω4
      (hW.prodCharEta ω)
      (by
        intro i j hwm
        rw [hW.prodCharEta_eq_coe_apply])
      ⟨e, heE, he1, by
        rw [_root_.CFSG.FeitThompson.Prep05.centralizerIn_eq,
          centralizer_coe_zpowers,
          _root_.CFSG.FeitThompson.Prep05.hallCoreOf_eq]
        exact hne⟩
  obtain ⟨hdisj, -⟩ :=
    FPF_type_iii_v_type_ii_support_disjoint h₁ h₂ h₃ h₄ G hG M N hM hN htype hNII _ _ rfl rfl
  have hDisj : Disjoint (dadeDeltaM M)
      (_root_.CFSG.FeitThompson.Prep05.conjClosure
        (_root_.CFSG.FeitThompson.Prep05.fixedSet
          (⁅N, N⁆ : Subgroup G)
          (_root_.CFSG.FeitThompson.Prep05.hallCoreOf N))) := by
    rw [conjClosure_fixedSet_eq]
    exact Set.disjoint_iff_inter_eq_empty.2 hdisj
  refine not_vanishes_outside_of_crossed_array (η := hW.prodCharEta ω) (ρ := ρ) (lam := lam)
    ?_ hρ ((isSignedIrr_iff_mem_signedIrr lam).1 hlamS) ?_ hρη ?_ hDisj ?_ ?_ i₁ j₀ hδ hε (d : ℂ)
    ⟨?_, ?_⟩
  · intro i j i' j'
    rw [hW.cfInner_prodCharEta hω i i' j j']
    by_cases h : i = i' ∧ j = j' <;> simp [h]
  · refine fun hcon => hlamne (funext fun x => ?_)
    rw [_root_.CFSG.FeitThompson.Prep05.cconj_apply,
      ← starRingEnd_apply]
    exact congrFun hcon x
  · intro i j
    have h := hlamη i j
    rwa [cfIP_eq_cfInner] at h
  · intro x hx
    have h := hρsupp x hx
    simpa using h
  · intro x hx
    have h := hlamD x hx
    simpa [_root_.CFSG.FeitThompson.Prep05.cconj_apply] using h
  · intro x hx
    have h := hfsupp x hx
    rwa [finsum_eq_sum_of_fintype] at h
  · intro x hx
    exact hgsupp x hx

end CFSG.FeitThompson.Proofs

end
