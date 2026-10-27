module

import CFSG.FeitThompson.Representations.CyclicTIColumnSumAxisNonvanishing
import CFSG.FeitThompson.Representations.MixedCoreSupportTISubset
import CFSG.FeitThompson.Representations.InductionMulRestrictedClassFun
public import CFSG.FeitThompson.Representations.TypePOrientedCoreFamily
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Representations.TypeIPBridgeOrthogonality
import CFSG.FeitThompson.Representations.TypeIIIIVRowDegreeKernel
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Local.SplitPrimeKernelFreeComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup
open CFSG.FeitThompson.Prep03
open CFSG.FeitThompson.Prep05 (IsFixedPointFreeOn centralizerIn
  IsMinimalSimpleOdd)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

variable {G : Type*} [Group G]

theorem natCard_dvd_natCard_sub_one_of_isFixedPointFreeOn [Finite G] {U W₁ : Subgroup G}
    (hnorm : W₁ ≤ normalizer (U : Set G)) (hfree : IsFixedPointFreeOn U W₁) :
    Nat.card ↥W₁ ∣ Nat.card ↥U - 1 := by
  refine card_dvd_card_sub_one_of_fixedPointFree (φ := conjOnNormalized U hnorm) ?_
  intro w hw x hx
  have hwx : (w : G) * (x : G) * (w : G)⁻¹ = (x : G) := by
    have h := congrArg (Subtype.val (p := fun y => y ∈ U)) hx
    rwa [conjOnNormalized_apply_coe] at h
  have hcomm : Commute (x : G) (w : G) := (mul_inv_eq_iff_eq_mul.1 hwx).symm
  have hbot := hfree (w : G) w.2 (fun h => hw (Subtype.ext h))
  have hmem : (x : G) ∈ centralizerIn U (zpowers (w : G)) := by
    refine Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (hcomm.zpow_right n).symm
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem indG_eq_zero_of_notMem_sat_union [Fintype G] {S W₁ W₂ : Subgroup G} {f : ↥S → ℂ}
    (hf : ∀ y : ↥S, (y : G) ∉ mixedSupport S W₁ W₂ → f y = 0) {x : G}
    (hx : x ∉ Prep03.sat (Prep03.hallCoreIn S : Set G) ∪ Prep03.sat ((W₁ ⊔ W₂ : Subgroup G) : Set G)) :
    indG S f x = 0 := by
  refine indClassFun_apply_eq_zero_of_forall_not_isConj S
    (A := mixedSupport S W₁ W₂) hf (fun v hv hconj => ?_)
  rcases CFSG.FeitThompson.Proofs.mem_mixedSupport_iff.1 hv with ⟨hvP, -⟩ | ⟨s, -, z, hz, hvz⟩
  · exact hx (Or.inl (mem_sat_of_isConj hvP hconj))
  · refine hx (Or.inr (mem_sat_of_isConj (X := W₁ ⊔ W₂) (mem_cyclicTIset.1 hz).1 ?_))
    refine hconj.trans (isConj_iff.2 ⟨s, ?_⟩)
    rw [← hvz]
    group

section Ambient

variable [Fintype G]

theorem cfInner_indG_one (S : Subgroup G) (f : ↥S → ℂ) :
    cfInner (indG S f) (1 : G → ℂ) = cfInner f (1 : ↥S → ℂ) := by
  change cfInner (indClassFun S f) (1 : G → ℂ) = _
  rw [cfInner_indClassFun S f (one_mem_classFun G), resClassFun_one]

theorem indG_mem_virtualChars {S : Subgroup G} {f : ↥S → ℂ} (hf : f ∈ virtualChars ↥S) :
    indG S f ∈ virtualChars G := by
  have h : indG S f = InducedCharacterConstruction.indClassFun S f := by
    rw [NormalInducedFamily.indClassFun_inducedCharacterConstruction_eq]; rfl
  rw [h]
  exact InducedCharacterConstruction.indClassFun_mem_virtualChars
    (mem_span_Irr_of_mem_virtualChars hf)

theorem cfInner_isTIExtension_one_eq_zero {W₁ W₂ X : Subgroup G}
    {Φ : (↥(W₁ ⊔ W₂) → ℂ) → (↥X → ℂ)} (hΦ : IsTIExtension W₁ W₂ X Φ)
    {f : ↥(W₁ ⊔ W₂) → ℂ} (hf : cfInner f (1 : ↥(W₁ ⊔ W₂) → ℂ) = 0) :
    cfInner (Φ f) (1 : ↥X → ℂ) = 0 := by
  have h := hΦ.inner_eq f 1
  rwa [hΦ.map_one, hf] at h

theorem cfInner_omega_one_eq_zero {W₁ W₂ : Subgroup G} {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {f : ↥(W₁ ⊔ W₂) → ℂ} (hf : cfInner f (1 : ↥(W₁ ⊔ W₂) → ℂ) = 0) :
    cfInner (ω f) (1 : G → ℂ) = 0 := by
  rw [← cfInner_top_eq (ω f) (1 : G → ℂ)]
  exact cfInner_isTIExtension_one_eq_zero hω hf

theorem omega_mem_virtualChars {W₁ W₂ : Subgroup G} {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {f : ↥(W₁ ⊔ W₂) → ℂ} (hf : f ∈ virtualChars ↥(W₁ ⊔ W₂)) : ω f ∈ virtualChars G :=
  mem_virtualChars_of_mem_virtualChars_top (hω.maps_virtualChars f hf)

end Ambient

section Rows

variable [Fintype G] {W₁ W₂ : Subgroup G} {I J : Type} {i0 : I} {j0' : J} {α : I → ↥W₁ → ℂ}
  {β : J → ↥W₂ → ℂ} {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
  (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
  (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
    w i j z = α i x * β j y)

include hW hw

omit [Fintype G] in
theorem prodRow_eq (hα0 : α i0 = 1) (j : J) :
    w i0 j = hW.prodChar (1 : ↥W₁ → ℂ) (β j) :=
  prodChar_eq_of_tensor hW (fun x y z hz => by rw [hw i0 j x y z hz, hα0])

omit [Fintype G] in
theorem prodRow_mem_Irr (hβ : ∀ j, β j ∈ Irr ↥W₂) (hα0 : α i0 = 1) (j : J) :
    w i0 j ∈ Irr ↥(W₁ ⊔ W₂) := by
  rw [prodRow_eq hW hw hα0 j]
  exact hW.prodChar_mem_Irr one_mem_Irr (hβ j)

theorem cfInner_prodRow_one (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hα0 : α i0 = 1) (hβ0 : β j0' = 1) {j : J} (hj : j ≠ j0') :
    cfInner (w i0 j) (1 : ↥(W₁ ⊔ W₂) → ℂ) = 0 := by
  refine cfInner_eq_zero_of_mem_Irr (prodRow_mem_Irr hW hw hβ hα0 j) one_mem_Irr (fun heq => ?_)
  rw [prodRow_eq hW hw hα0 j, ← IsCyclicTIPair.prodChar_one_one hW] at heq
  exact hj (hβinj (((hW.prodChar_injective one_mem_Irr one_mem_Irr (hβ j) one_mem_Irr
    heq).2).trans hβ0.symm))

theorem cfInner_prodRow_prodRow (hβ : ∀ j, β j ∈ Irr ↥W₂) (hβinj : Function.Injective β)
    (hα0 : α i0 = 1) {j k : J} (hjk : j ≠ k) : cfInner (w i0 j) (w i0 k) = 0 := by
  refine cfInner_eq_zero_of_mem_Irr (prodRow_mem_Irr hW hw hβ hα0 j)
    (prodRow_mem_Irr hW hw hβ hα0 k) (fun heq => ?_)
  rw [prodRow_eq hW hw hα0 j, prodRow_eq hW hw hα0 k] at heq
  exact hjk (hβinj ((hW.prodChar_injective one_mem_Irr one_mem_Irr (hβ j) (hβ k) heq).2))

omit [Fintype G] in
theorem conj_prodRow_eq (hα0 : α i0 = 1) {j k : J}
    (hk : β k = fun y => (starRingEnd ℂ) (β j y)) :
    (fun z => (starRingEnd ℂ) (w i0 j z)) = w i0 k := by
  rw [prodRow_eq hW hw hα0 k]
  refine prodChar_eq_of_tensor hW (fun x y z hz => ?_)
  rw [hw i0 j x y z hz, hα0, hk]
  simp

end Rows

section SigmaLocal

variable [Fintype G] {S W₁ W₂ : Subgroup G} (h1 : W₁ ≤ S) (h2 : W₂ ≤ S)
  (hloc : IsCyclicTIPair (W₁.subgroupOf S ⊔ W₂.subgroupOf S) (W₁.subgroupOf S) (W₂.subgroupOf S))
  {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ)} (hσ : IsTIExtension W₁ W₂ S σ)

include h1 h2 hloc hσ

theorem isTIExtension_apply_of_mem_cyclicTIset
    {f : ↥(W₁ ⊔ W₂) → ℂ} (hf : f ∈ classFun ↥(W₁ ⊔ W₂)) {x : ↥S} {z : ↥(W₁ ⊔ W₂)}
    (hxz : (x : G) = (z : G)) (hz : (z : G) ∈ cyclicTIset W₁ W₂) :
    σ f x = f z := by
  set e := OrientedCoreFamily.supSubgroupOfEquiv h1 h2 with he
  set g : classFun ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S) :=
    ⟨f ∘ e, mem_classFun_comp_mulEquiv e hf⟩ with hg
  have hv : ((e.symm z : ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S)) : ↥S) ∈
      cyclicTIDiff (W₁.subgroupOf S ⊔ W₂.subgroupOf S) (W₁.subgroupOf S) (W₂.subgroupOf S) := by
    refine (OrientedCoreFamily.mem_cyclicTIDiff_subgroupOf_iff h1 h2 _).2 ?_
    rw [OrientedCoreFamily.coe_supSubgroupOfEquiv_symm]
    exact hz
  have hkey := (OrientedCoreFamily.isCyclicTIIsometry_sigmaLocalHom h1 h2
    hσ).apply_eq_of_mem_cyclicTIDiff hloc g (v := e.symm z) hv
  rw [OrientedCoreFamily.coe_sigmaLocalHom h1 h2 hσ g] at hkey
  have e2 : ((g : ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S) → ℂ)) ∘ (e.symm : _ → _) = f := by
    funext y; simp [hg]
  rw [e2] at hkey
  have hx : x = ((e.symm z : ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S)) : ↥S) := by
    refine Subtype.ext ?_
    rw [OrientedCoreFamily.coe_supSubgroupOfEquiv_symm]
    exact hxz
  rw [hx, hkey]
  simp [hg]

theorem isTIExtension_apply_star
    {f : ↥(W₁ ⊔ W₂) → ℂ} (hf : f ∈ classFun ↥(W₁ ⊔ W₂)) (x : ↥S) :
    σ (fun z => (starRingEnd ℂ) (f z)) x = (starRingEnd ℂ) (σ f x) := by
  set e := OrientedCoreFamily.supSubgroupOfEquiv h1 h2 with he
  set g : classFun ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S) :=
    ⟨f ∘ e, mem_classFun_comp_mulEquiv e hf⟩ with hg
  have hkey := (OrientedCoreFamily.isCyclicTIIsometry_sigmaLocalHom h1 h2
    hσ).apply_starₗ_apply hloc g x
  rw [OrientedCoreFamily.coe_sigmaLocalHom h1 h2 hσ (classFun.starₗ _ g),
    OrientedCoreFamily.coe_sigmaLocalHom h1 h2 hσ g] at hkey
  have e1 : ((classFun.starₗ ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S) g :
      classFun ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S)) : _ → ℂ) ∘ (e.symm : _ → _)
      = fun z => (starRingEnd ℂ) (f z) := by
    funext z
    rw [Function.comp_apply, classFun.starₗ_apply_apply]
    simp [hg]
  have e2 : ((g : ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S) → ℂ)) ∘ (e.symm : _ → _) = f := by
    funext z; simp [hg]
  rw [e1, e2] at hkey
  exact hkey

end SigmaLocal

theorem omega_apply_star [Fintype G] {W₁ W₂ : Subgroup G}
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)}
    (hω : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G)))
    {f : ↥(W₁ ⊔ W₂) → ℂ} (hf : f ∈ classFun ↥(W₁ ⊔ W₂)) (x : G) :
    ω (fun z => (starRingEnd ℂ) (f z)) x = (starRingEnd ℂ) (ω f x) := by
  have h := (isCyclicTIIsometry_tiExtensionHom hω).apply_starₗ_apply hW ⟨f, hf⟩ x
  rw [coe_tiExtensionHom_apply hω (classFun.starₗ ↥(W₁ ⊔ W₂) ⟨f, hf⟩),
    coe_tiExtensionHom_apply hω ⟨f, hf⟩] at h
  have he : (fun z => (starRingEnd ℂ) (f z)) = ((classFun.starₗ ↥(W₁ ⊔ W₂) ⟨f, hf⟩ :
      classFun ↥(W₁ ⊔ W₂)) : ↥(W₁ ⊔ W₂) → ℂ) :=
    funext fun z => (classFun.starₗ_apply_apply (X := ↥(W₁ ⊔ W₂)) ⟨f, hf⟩ z).symm
  rw [he, h]

structure IsTypePBridgeSetup (G : Type*) [Group G] [Fintype G] (S U W₁ W₂ : Subgroup G)
    {I J : Type} (i0 : I) (j0' : J) (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ)
    (w : I → J → ↥(W₁ ⊔ W₂) → ℂ) (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ))
    (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)) (δ : J → ℂ) (μ : J → ↥S → ℂ) (η : I → J → G → ℂ)
    (γ b : J → ↥S → ℂ) : Prop where
  ambient : IsAmbient G
  config : IsPConfigSetup G S U W₁ W₂
  alpha_mem : ∀ i, α i ∈ Irr ↥W₁
  beta_mem : ∀ j, β j ∈ Irr ↥W₂
  alpha_injective : Function.Injective α
  beta_injective : Function.Injective β
  alpha_surjective : ∀ χ ∈ Irr ↥W₁, ∃ i, α i = χ
  beta_surjective : ∀ χ ∈ Irr ↥W₂, ∃ j, β j = χ
  alpha_principal : α i0 = 1
  beta_principal : β j0' = 1
  prod_eq : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
    w i j z = α i x * β j y
  sigma_isTIExtension : IsTIExtension W₁ W₂ S σ
  omega_isTIExtension : IsTIExtension W₁ W₂ (⊤ : Subgroup G) (fun f x => ω f (x : G))
  sign_eq : ∀ j, δ j = 1 ∨ δ j = -1
  mu_eq : ∀ j, μ j = δ j • σ (w i0 j)
  mu_mem_Irr : ∀ j, μ j ∈ Irr ↥S
  eta_eq : ∀ i j, η i j = ω (w i j)
  gamma_eq : ∀ j, γ j = indClassFun (((Prep03.hallCoreIn S) ⊔ W₁).subgroupOf S) (fun _ => (1 : ℂ))
  b_eq : ∀ j, b j = γ j - μ j

namespace IsTypePBridgeSetup

variable [Fintype G] {S U W₁ W₂ : Subgroup G} {I J : Type} {i0 : I} {j0' : J} {α : I → ↥W₁ → ℂ}
  {β : J → ↥W₂ → ℂ} {w : I → J → ↥(W₁ ⊔ W₂) → ℂ} {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ)}
  {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)} {δ : J → ℂ} {μ : J → ↥S → ℂ} {η : I → J → G → ℂ}
  {γ b : J → ↥S → ℂ}
  (hS : IsTypePBridgeSetup G S U W₁ W₂ i0 j0' α β w σ ω δ μ η γ b)

include hS

theorem gamma_mem_virtualChars (j : J) : γ j ∈ virtualChars ↥S := by
  have h : γ j = indClassFun (((Prep03.hallCoreIn S) ⊔ W₁).subgroupOf S) 1 := hS.gamma_eq j
  rw [h]
  exact indClassFun_one_mem_virtualChars _

theorem cfInner_gamma_one (j : J) : cfInner (γ j) (1 : ↥S → ℂ) = 1 := by
  have h : γ j = indClassFun (((Prep03.hallCoreIn S) ⊔ W₁).subgroupOf S) 1 := hS.gamma_eq j
  rw [h]
  exact NormalInducedFamily.cfInner_indClassFun_one_left_one

theorem b_mem_virtualChars (j : J) : b j ∈ virtualChars ↥S := by
  rw [hS.b_eq j]
  exact sub_mem (hS.gamma_mem_virtualChars j) (Irr_subset_virtualChars (hS.mu_mem_Irr j))

theorem isCyclicTIPair_sup (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) :
    IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ :=
  hS.config.config.isCyclicTIPair_sup hS.ambient.odd_natCard hcop

theorem cfInner_mu_one (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) {j : J} (hj : j ≠ j0') :
    cfInner (μ j) (1 : ↥S → ℂ) = 0 := by
  rw [hS.mu_eq j, cfInner_smul_left,
    cfInner_isTIExtension_one_eq_zero hS.sigma_isTIExtension
      (cfInner_prodRow_one (hS.isCyclicTIPair_sup hcop) hS.prod_eq hS.beta_mem hS.beta_injective
        hS.alpha_principal hS.beta_principal hj), mul_zero]

theorem cfInner_b_one (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) {j : J} (hj : j ≠ j0') :
    cfInner (b j) (1 : ↥S → ℂ) = 1 := by
  rw [hS.b_eq j, cfInner_sub_left, hS.cfInner_gamma_one j, hS.cfInner_mu_one hcop hj, sub_zero]

theorem eta_mem_virtualChars (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) (j : J) :
    η i0 j ∈ virtualChars G := by
  rw [hS.eta_eq i0 j]
  exact omega_mem_virtualChars hS.omega_isTIExtension
    (Irr_subset_virtualChars
      (prodRow_mem_Irr (hS.isCyclicTIPair_sup hcop) hS.prod_eq hS.beta_mem hS.alpha_principal j))

theorem cfInner_eta_one (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) {j : J} (hj : j ≠ j0') :
    cfInner (η i0 j) (1 : G → ℂ) = 0 := by
  rw [hS.eta_eq i0 j]
  exact cfInner_omega_one_eq_zero hS.omega_isTIExtension
    (cfInner_prodRow_one (hS.isCyclicTIPair_sup hcop) hS.prod_eq hS.beta_mem hS.beta_injective
      hS.alpha_principal hS.beta_principal hj)

theorem remainder_mem_virtualChars (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) (j₀ : J)
    {Γ : G → ℂ} (hΓ : Γ = indG S (b j₀) - 1 + η i0 j₀) : Γ ∈ virtualChars G := by
  rw [hΓ]
  exact add_mem (sub_mem (indG_mem_virtualChars (hS.b_mem_virtualChars j₀))
    (Irr_subset_virtualChars one_mem_Irr)) (hS.eta_mem_virtualChars hcop j₀)

theorem cfInner_remainder_one (hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂)) {j₀ : J}
    (hj₀ : j₀ ≠ j0') {Γ : G → ℂ} (hΓ : Γ = indG S (b j₀) - 1 + η i0 j₀) :
    cfInner Γ (1 : G → ℂ) = 0 := by
  rw [hΓ, cfInner_add_left, cfInner_sub_left, cfInner_indG_one, hS.cfInner_b_one hcop hj₀,
    hS.cfInner_eta_one hcop hj₀, cfInner_one_one]
  ring

theorem le_S_W₁ : W₁ ≤ S := hS.config.config.le_M_W₁

theorem le_S_W₂ : W₂ ≤ S := hS.config.config.le_M_W₂

theorem le_S_sup : W₁ ⊔ W₂ ≤ S := sup_le hS.le_S_W₁ hS.le_S_W₂

theorem isCyclicTIPair_subgroupOf :
    IsCyclicTIPair (W₁.subgroupOf S ⊔ W₂.subgroupOf S) (W₁.subgroupOf S) (W₂.subgroupOf S) :=
  (hS.config.config.isPrimeCyclicTIHyp_subgroupOf hS.ambient.odd_natCard).isCyclicTIPair

theorem coprime_natCard : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂) := by
  have h := hS.isCyclicTIPair_subgroupOf.coprime_natCard
  rwa [natCard_subgroupOf_eq hS.le_S_W₁, natCard_subgroupOf_eq hS.le_S_W₂] at h

theorem isCyclicTIPair_sup' : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ :=
  hS.isCyclicTIPair_sup hS.coprime_natCard

theorem b_mem_classFun (j : J) : b j ∈ classFun ↥S := by
  rw [hS.b_eq j, hS.gamma_eq j]
  exact sub_mem (indClassFun_mem_classFun _ _) (Irr_subset_classFun (hS.mu_mem_Irr j))

theorem b_sub_b_eq (j k : J) : b j - b k = μ k - μ j := by
  rw [hS.b_eq j, hS.b_eq k, hS.gamma_eq j, hS.gamma_eq k]
  ring

theorem cfInner_mu_mu {j k : J} (hjk : j ≠ k) : cfInner (μ j) (μ k) = 0 := by
  rw [hS.mu_eq j, hS.mu_eq k, cfInner_smul_left, cfInner_smul_right,
    hS.sigma_isTIExtension.inner_eq (w i0 j) (w i0 k),
    cfInner_prodRow_prodRow hS.isCyclicTIPair_sup' hS.prod_eq hS.beta_mem hS.beta_injective
      hS.alpha_principal hjk]
  ring

theorem cfInner_self_b_sub {j k : J} (hjk : j ≠ k) : cfInner (b j - b k) (b j - b k) = 2 := by
  rw [hS.b_sub_b_eq j k, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right,
    hS.cfInner_mu_mu hjk, hS.cfInner_mu_mu (Ne.symm hjk),
    cfInner_self_of_mem_Irr (hS.mu_mem_Irr k), cfInner_self_of_mem_Irr (hS.mu_mem_Irr j)]
  ring

theorem prodRow_mem_classFun (j : J) : w i0 j ∈ classFun ↥(W₁ ⊔ W₂) :=
  Irr_subset_classFun (prodRow_mem_Irr hS.isCyclicTIPair_sup' hS.prod_eq hS.beta_mem
    hS.alpha_principal j)

theorem mu_apply_of_mem_cyclicTIset (j : J) {x : ↥S} {z : ↥(W₁ ⊔ W₂)}
    (hxz : (x : G) = (z : G)) (hz : (z : G) ∈ cyclicTIset W₁ W₂) :
    μ j x = δ j * w i0 j z := by
  rw [hS.mu_eq j, Pi.smul_apply, smul_eq_mul]
  congr 1
  exact isTIExtension_apply_of_mem_cyclicTIset hS.le_S_W₁ hS.le_S_W₂
    hS.isCyclicTIPair_subgroupOf hS.sigma_isTIExtension (hS.prodRow_mem_classFun j) hxz hz

theorem exists_conj_index {j : J} (hj : j ≠ j0') :
    ∃ k : J, k ≠ j0' ∧ β k = fun y => (starRingEnd ℂ) (β j y) := by
  obtain ⟨k, hk⟩ := hS.beta_surjective _ (conj_mem_Irr (hS.beta_mem j))
  refine ⟨k, fun hkk => hj ?_, hk⟩
  subst hkk
  refine hS.beta_injective ?_
  rw [hS.beta_principal]
  funext y
  have h := congrFun hk y
  rw [hS.beta_principal] at h
  have h2 := congrArg (starRingEnd ℂ) h
  simpa using h2.symm

theorem conj_gamma_apply (j : J) (x : ↥S) : (starRingEnd ℂ) (γ j x) = γ j x := by
  rw [hS.gamma_eq j]
  have h := congrFun (conj_indClassFun ((Prep03.hallCoreIn S ⊔ W₁).subgroupOf S)
    (fun _ : ↥((Prep03.hallCoreIn S ⊔ W₁).subgroupOf S) => (1 : ℂ))) x
  simpa using h

theorem conj_mu_eq {j k : J} (hδj : δ j = 1) (hδk : δ k = 1)
    (hk : β k = fun y => (starRingEnd ℂ) (β j y)) (x : ↥S) :
    (starRingEnd ℂ) (μ j x) = μ k x := by
  rw [hS.mu_eq j, hS.mu_eq k, hδj, hδk, one_smul, one_smul,
    ← isTIExtension_apply_star hS.le_S_W₁ hS.le_S_W₂ hS.isCyclicTIPair_subgroupOf
      hS.sigma_isTIExtension (hS.prodRow_mem_classFun j) x,
    conj_prodRow_eq hS.isCyclicTIPair_sup' hS.prod_eq hS.alpha_principal hk]

theorem conj_eta_eq {j k : J} (hk : β k = fun y => (starRingEnd ℂ) (β j y)) (x : G) :
    (starRingEnd ℂ) (η i0 j x) = η i0 k x := by
  rw [hS.eta_eq i0 j, hS.eta_eq i0 k,
    ← omega_apply_star hS.isCyclicTIPair_sup' hS.omega_isTIExtension
      (hS.prodRow_mem_classFun j) x,
    conj_prodRow_eq hS.isCyclicTIPair_sup' hS.prod_eq hS.alpha_principal hk]

theorem conj_b_eq {j k : J} (hδj : δ j = 1) (hδk : δ k = 1)
    (hk : β k = fun y => (starRingEnd ℂ) (β j y)) :
    (fun x => (starRingEnd ℂ) (b j x)) = b k := by
  funext x
  rw [hS.b_eq j, hS.b_eq k, Pi.sub_apply, Pi.sub_apply, map_sub, hS.conj_gamma_apply j x,
    hS.conj_mu_eq hδj hδk hk x, hS.gamma_eq j, hS.gamma_eq k]

theorem indG_b_sub_indG_b
    (hTI : IsTIWithNormalizer (mixedSupport S W₁ W₂) S)
    (hiso : ∀ f : ↥S → ℂ, f ∈ virtualChars ↥S →
      (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
      cfInner (indG S f) (indG S f) = cfInner f f)
    (hδ1 : ∀ j : J, j ≠ j0' → δ j = 1)
    (hsupp : ∀ j : J, j ≠ j0' → ∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0)
    {j k : J} (hj : j ≠ j0') (hk : k ≠ j0') (hjk : j ≠ k) :
    indG S (b j) - indG S (b k) = η i0 k - η i0 j := by
  classical
  set hW := hS.isCyclicTIPair_sup' with hWdef
  set i0' := irrEquivOfEnum α hS.alpha_mem hS.alpha_injective hS.alpha_surjective i0 with hi0'
  set j' := irrEquivOfEnum β hS.beta_mem hS.beta_injective hS.beta_surjective j with hj'
  set k' := irrEquivOfEnum β hS.beta_mem hS.beta_injective hS.beta_surjective k with hk'
  have hfind : indG S (b j) - indG S (b k) = indG S (b j - b k) :=
    (indClassFun_sub S (b j) (b k)).symm
  have hdiffsupp : ∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → (b j - b k) x = 0 := by
    intro x hx
    rw [Pi.sub_apply, hsupp j hj x hx, hsupp k hk x hx, sub_zero]
  have hdiffvc : (b j - b k) ∈ virtualChars ↥S :=
    sub_mem (hS.b_mem_virtualChars j) (hS.b_mem_virtualChars k)
  have hfmem : indG S (b j) - indG S (b k) ∈ Submodule.span ℤ (Irr G) := by
    rw [hfind]
    exact mem_span_Irr_of_mem_virtualChars (indG_mem_virtualChars hdiffvc)
  have hfnorm : cfInner (indG S (b j) - indG S (b k)) (indG S (b j) - indG S (b k)) = 2 := by
    rw [hfind, hiso _ hdiffvc hdiffsupp, hS.cfInner_self_b_sub hjk]
  have hfV : ∀ v : ↥(W₁ ⊔ W₂), (v : G) ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ →
      (indG S (b j) - indG S (b k)) (v : G) = 1 * (hW.prodChar (i0' : ↥W₁ → ℂ) (k' : ↥W₂ → ℂ) v
        - hW.prodChar (i0' : ↥W₁ → ℂ) (j' : ↥W₂ → ℂ) v) := by
    intro v hv
    rw [cyclicTIDiff_sup_eq_cyclicTIset] at hv
    have hvS : (v : G) ∈ S := hS.le_S_sup v.2
    have hvB : ((⟨(v : G), hvS⟩ : ↥S) : G) ∈ mixedSupport S W₁ W₂ :=
      CFSG.FeitThompson.Proofs.mem_mixedSupport_iff.2 (Or.inr ⟨1, one_mem _, (v : G), hv, by group⟩)
    have hval : (indG S (b j) - indG S (b k)) (v : G) = (b j - b k) ⟨(v : G), hvS⟩ := by
      rw [hfind]
      exact hTI.indClassFun_apply_of_mem
        (sub_mem (hS.b_mem_classFun j) (hS.b_mem_classFun k)) hdiffsupp hvB
    rw [hval, hS.b_sub_b_eq j k, Pi.sub_apply,
      hS.mu_apply_of_mem_cyclicTIset k (x := ⟨(v : G), hvS⟩) rfl hv,
      hS.mu_apply_of_mem_cyclicTIset j (x := ⟨(v : G), hvS⟩) rfl hv,
      hδ1 j hj, hδ1 k hk, one_mul, one_mul,
      prodRow_eq hW hS.prod_eq hS.alpha_principal j,
      prodRow_eq hW hS.prod_eq hS.alpha_principal k]
    have hcoe1 : (i0' : ↥W₁ → ℂ) = 1 := by
      rw [hi0', coe_irrEquivOfEnum_apply, hS.alpha_principal]
    have hcoej : (j' : ↥W₂ → ℂ) = β j := by rw [hj', coe_irrEquivOfEnum_apply]
    have hcoek : (k' : ↥W₂ → ℂ) = β k := by rw [hk', coe_irrEquivOfEnum_apply]
    rw [hcoe1, hcoej, hcoek]
    ring
  have hne : (i0', k') ≠ (i0', j') := by
    intro hcc
    have h2 : k' = j' := congrArg Prod.snd hcc
    exact hjk ((irrEquivOfEnum β hS.beta_mem hS.beta_injective hS.beta_surjective).injective
      (a₁ := k) (a₂ := j) (by rw [← hj', ← hk', h2])).symm
  have hres := hW.eq_signed_sub_prodCharEta
    (σ := tiExtensionHom hS.omega_isTIExtension)
    (isCyclicTIIsometry_tiExtensionHom hS.omega_isTIExtension) hne (ε := 1) (Or.inl rfl)
    hfmem hfnorm hfV
  rw [one_smul] at hres
  rw [hres,
    eta_eq_prodCharEta hW hS.omega_isTIExtension hS.alpha_mem hS.beta_mem hS.alpha_injective
      hS.beta_injective hS.alpha_surjective hS.beta_surjective hS.prod_eq hS.eta_eq i0 k,
    eta_eq_prodCharEta hW hS.omega_isTIExtension hS.alpha_mem hS.beta_mem hS.alpha_injective
      hS.beta_injective hS.alpha_surjective hS.beta_surjective hS.prod_eq hS.eta_eq i0 j]

theorem indG_b_eq_of_remainder
    (hTI : IsTIWithNormalizer (mixedSupport S W₁ W₂) S)
    (hiso : ∀ f : ↥S → ℂ, f ∈ virtualChars ↥S →
      (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
      cfInner (indG S f) (indG S f) = cfInner f f)
    (hδ1 : ∀ j : J, j ≠ j0' → δ j = 1)
    (hsupp : ∀ j : J, j ≠ j0' → ∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0)
    {j₀ : J} (hj₀ : j₀ ≠ j0') {Γ : G → ℂ} (hΓ : Γ = indG S (b j₀) - 1 + η i0 j₀)
    {j : J} (hj : j ≠ j0') (x : G) :
    indG S (b j) x = 1 - η i0 j x + Γ x := by
  rcases eq_or_ne j j₀ with rfl | hjj₀
  · rw [hΓ]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
    ring
  · have h := congrFun (hS.indG_b_sub_indG_b hTI hiso hδ1 hsupp hj hj₀ hjj₀) x
    rw [hΓ]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply] at h ⊢
    linear_combination h

theorem isRealValued_remainder
    (hTI : IsTIWithNormalizer (mixedSupport S W₁ W₂) S)
    (hiso : ∀ f : ↥S → ℂ, f ∈ virtualChars ↥S →
      (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
      cfInner (indG S f) (indG S f) = cfInner f f)
    (hδ1 : ∀ j : J, j ≠ j0' → δ j = 1)
    (hsupp : ∀ j : J, j ≠ j0' → ∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0)
    {j₀ : J} (hj₀ : j₀ ≠ j0') {Γ : G → ℂ} (hΓ : Γ = indG S (b j₀) - 1 + η i0 j₀) :
    IsRealValued Γ := by
  intro x
  obtain ⟨k₀, hk₀, hk₀β⟩ := hS.exists_conj_index hj₀
  have hbconj : (fun y => (starRingEnd ℂ) (b j₀ y)) = b k₀ :=
    hS.conj_b_eq (hδ1 j₀ hj₀) (hδ1 k₀ hk₀) hk₀β
  have hind : (starRingEnd ℂ) (indG S (b j₀) x) = indG S (b k₀) x := by
    rw [← hbconj]
    exact congrFun (conj_indClassFun S (b j₀)) x
  have heta : (starRingEnd ℂ) (η i0 j₀ x) = η i0 k₀ x := hS.conj_eta_eq hk₀β x
  have hΓconj : (starRingEnd ℂ) (Γ x) = indG S (b k₀) x - 1 + η i0 k₀ x := by
    rw [hΓ]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply, map_add, map_sub, map_one]
    rw [hind, heta]
  rw [hΓconj]
  rcases eq_or_ne k₀ j₀ with rfl | hne
  · rw [hΓ]; simp only [Pi.add_apply, Pi.sub_apply, Pi.one_apply]
  · have h := congrFun (hS.indG_b_sub_indG_b hTI hiso hδ1 hsupp hk₀ hj₀ hne) x
    rw [hΓ]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply] at h ⊢
    linear_combination h

end IsTypePBridgeSetup

namespace LocalRows

open Pointwise
open CFSG.FeitThompson.Prep05 (hallCoreOf)

variable {G : Type*} [Group G] [Fintype G]

noncomputable def localIrrIndex {S W₂ : Subgroup G} (h2 : W₂ ≤ S) {β : ↥W₂ → ℂ}
    (hβ : β ∈ Irr ↥W₂) : Irr ↥(W₂.subgroupOf S) :=
  ⟨β ∘ (Subgroup.subgroupOfEquivOfLe h2), CFSG.FeitThompson.Proofs.irr_comp_mulEquiv hβ _⟩

omit [Fintype G] in
theorem coe_localIrrIndex {S W₂ : Subgroup G} (h2 : W₂ ≤ S) {β : ↥W₂ → ℂ} (hβ : β ∈ Irr ↥W₂)
    (y : ↥(W₂.subgroupOf S)) :
    ((localIrrIndex h2 hβ : Irr ↥(W₂.subgroupOf S)) : ↥(W₂.subgroupOf S) → ℂ) y
      = β ⟨((y : ↥S) : G), mem_subgroupOf.1 y.2⟩ := (rfl)

omit [Fintype G] in
theorem localIrrIndex_ne_principalIrr {S W₂ : Subgroup G} (h2 : W₂ ≤ S) {β : ↥W₂ → ℂ}
    (hβ : β ∈ Irr ↥W₂) (hβ1 : β ≠ 1) :
    localIrrIndex h2 hβ ≠ principalIrr ↥(W₂.subgroupOf S) := by
  intro heq
  refine hβ1 (funext fun y => ?_)
  have h : ((localIrrIndex h2 hβ : Irr ↥(W₂.subgroupOf S)) : ↥(W₂.subgroupOf S) → ℂ)
      = (1 : ↥(W₂.subgroupOf S) → ℂ) := by rw [heq, coe_principalIrr]
  have h2' := congrFun h ⟨⟨(y : G), h2 y.2⟩, mem_subgroupOf.2 y.2⟩
  rw [coe_localIrrIndex] at h2'
  simpa using h2'

theorem sigmaLocalHom_basisProdIrr_eq {S W₁ W₂ : Subgroup G} (h1 : W₁ ≤ S) (h2 : W₂ ≤ S)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ)} (hσ : IsTIExtension W₁ W₂ S σ)
    (hWloc : IsCyclicTIPair (W₁.subgroupOf S ⊔ W₂.subgroupOf S) (W₁.subgroupOf S)
      (W₂.subgroupOf S))
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) {β : ↥W₂ → ℂ} (hβ : β ∈ Irr ↥W₂)
    {I J : Type} {i0 : I} {α : I → ↥W₁ → ℂ} {βf : J → ↥W₂ → ℂ} {j : J}
    (hβj : βf j = β) (hα0 : α i0 = 1) {w : I → J → ↥(W₁ ⊔ W₂) → ℂ}
    (hw : ∀ i j, ∀ x : ↥W₁, ∀ y : ↥W₂, ∀ z : ↥(W₁ ⊔ W₂), (z : G) = (x : G) * (y : G) →
      w i j z = α i x * βf j y) :
    ((OrientedCoreFamily.sigmaLocalHom h1 h2 hσ
        (hWloc.basisProdIrr (principalIrr ↥(W₁.subgroupOf S), localIrrIndex h2 hβ))) : ↥S → ℂ)
      = σ (w i0 j) := by
  rw [OrientedCoreFamily.coe_sigmaLocalHom]
  congr 1
  funext z
  have hz : (z : G) ∈ ((W₁ : Set G) * (W₂ : Set G)) := by rw [hW.mul_eq]; exact z.2
  obtain ⟨x, hx, y, hy, hxy⟩ := hz
  have hxS : (⟨x, h1 hx⟩ : ↥S) ∈ W₁.subgroupOf S := mem_subgroupOf.2 hx
  have hyS : (⟨y, h2 hy⟩ : ↥S) ∈ W₂.subgroupOf S := mem_subgroupOf.2 hy
  have hkey : ((OrientedCoreFamily.supSubgroupOfEquiv h1 h2).symm z :
      ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S))
      = ⟨(⟨x, h1 hx⟩ : ↥S) * (⟨y, h2 hy⟩ : ↥S),
        mul_mem (hWloc.left_le hxS) (hWloc.right_le hyS)⟩ := by
    refine Subtype.ext (Subtype.ext ?_)
    rw [OrientedCoreFamily.coe_supSubgroupOfEquiv_symm]
    simpa using hxy.symm
  rw [Function.comp_apply, IsCyclicTIPair.coe_basisProdIrr_apply, hkey,
    hWloc.prodChar_apply_mul _ _ hxS hyS, hw i0 j ⟨x, hx⟩ ⟨y, hy⟩ z (by rw [← hxy]),
    hα0, hβj, coe_principalIrr, coe_localIrrIndex]
  simp

theorem primeTIirr_eq_of_sign_smul {S W₁ W₂ : Subgroup G}
    (hloc : IsPrimeCyclicTIHyp (commutator ↥S) (W₁.subgroupOf S) (W₂.subgroupOf S))
    {σloc : classFun ↥(W₁.subgroupOf S ⊔ W₂.subgroupOf S) →ₗ[ℂ] classFun ↥S}
    (hσloc : IsCyclicTIIsometry (W₁.subgroupOf S ⊔ W₂.subgroupOf S) (W₁.subgroupOf S)
      (W₂.subgroupOf S) σloc)
    {jl : Irr ↥(W₂.subgroupOf S)} {d : ℂ} (hd : d = 1 ∨ d = -1) {f : ↥S → ℂ}
    (hf : (σloc (hloc.isCyclicTIPair.basisProdIrr (principalIrr ↥(W₁.subgroupOf S), jl))
      : ↥S → ℂ) = f)
    (hIrr : d • f ∈ Irr ↥S) :
    d = hloc.primeTISign σloc jl ∧
      d • f = hloc.primeTIirr σloc (principalIrr ↥(W₁.subgroupOf S)) jl := by
  obtain ⟨d0, -, huniq⟩ := hloc.existsUnique_primeTISign hσloc jl
  have hh1 : d = d0 := huniq d ⟨hd, by rw [hf]; exact hIrr⟩
  have hh2 : hloc.primeTISign σloc jl = d0 :=
    huniq _ ⟨hloc.primeTISign_eq_one_or_eq_neg_one jl,
      by rw [← hloc.primeTIirr_principal_left (σ := σloc) jl]
         exact hloc.primeTIirr_principal_left_mem_Irr hσloc jl⟩
  exact ⟨by rw [hh1, hh2], by rw [hloc.primeTIirr_principal_left, hh2, ← hh1, hf]⟩

noncomputable def commutatorSubgroupEquiv (S : Subgroup G) :
    ↥(commutator ↥S) ≃* ↥(⁅S, S⁆ : Subgroup G) :=
  (MulEquiv.subgroupCongr (commutator_eq_subgroupOf_commutator S)).trans
    (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self S))

omit [Fintype G] in
theorem coe_commutatorSubgroupEquiv (S : Subgroup G) (x : ↥(commutator ↥S)) :
    ((commutatorSubgroupEquiv S x : ↥(⁅S, S⁆ : Subgroup G)) : G) = ((x : ↥S) : G) := (rfl)

omit [Fintype G] in
theorem coe_commutatorSubgroupEquiv_symm (S : Subgroup G) (y : ↥(⁅S, S⁆ : Subgroup G)) :
    (((commutatorSubgroupEquiv S).symm y : ↥(commutator ↥S)) : ↥S)
      = ⟨(y : G), Subgroup.commutator_le_self S y.2⟩ := by
  refine Subtype.ext ?_
  have h := coe_commutatorSubgroupEquiv S ((commutatorSubgroupEquiv S).symm y)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

theorem indClassFun_hallCoreIn_sup_eq_bridgePermChar {S W₁ : Subgroup G} (h1 : W₁ ≤ S) :
    indClassFun (((Prep03.hallCoreIn S) ⊔ W₁).subgroupOf S) (fun _ => (1 : ℂ))
      = bridgePermChar (hallCore ↥S) (W₁.subgroupOf S) := by
  have hle : Prep03.hallCoreIn S ≤ S := Subgroup.map_subtype_le _
  have h : ((Prep03.hallCoreIn S) ⊔ W₁).subgroupOf S = hallCore ↥S ⊔ W₁.subgroupOf S := by
    rw [Subgroup.subgroupOf_sup hle h1, OrientedCoreFamily.subgroupOf_hallCoreIn S]
  rw [h, bridgePermChar_eq_frobeniusComplementChar,
    ← indClassFun_one_eq_frobeniusComplementChar]
  rfl

theorem mem_mixedSupport_of_mem_sdiff_union {S W₁ W₂ : Subgroup G} (h1 : W₁ ≤ S) (h2 : W₂ ≤ S)
    {x : ↥S} (hx : x ∈ ((hallCore ↥S : Subgroup ↥S) : Set ↥S) \ {1} ∪
      cyclicTIsetConj (W₁.subgroupOf S) (W₂.subgroupOf S)) :
    (x : G) ∈ mixedSupport S W₁ W₂ := by
  refine _root_.CFSG.FeitThompson.Proofs.mem_mixedSupport_iff.2 ?_
  rcases hx with ⟨hxH, hx1⟩ | hxV
  · exact Or.inl ⟨⟨x, hxH, rfl⟩, fun h => hx1 (Subtype.ext h)⟩
  · obtain ⟨t, v, hv, htv⟩ := mem_cyclicTIsetConj.1 hxV
    refine Or.inr ⟨(t : G), t.2, (v : G),
      (OrientedCoreFamily.mem_cyclicTIset_subgroupOf_iff h1 h2).1 hv, ?_⟩
    have h := congrArg (Subtype.val (p := fun y => y ∈ S)) htv
    simpa using h

theorem isPrimeTIBridgeConfig_subgroupOf {S U W₁ W₂ : Subgroup G}
    (hodd : Odd (Nat.card G)) (hc : IsWitnessedPConfiguration S U W₁ W₂)
    (hUne : U ≠ ⊥) (hfree : IsFixedPointFreeOn U W₁) :
    IsPrimeTIBridgeConfig (commutator ↥S) (W₁.subgroupOf S) (W₂.subgroupOf S)
      (hallCore ↥S) (U.subgroupOf S)
      (((commutator ↥S : Subgroup ↥S) : Set ↥S) \ {1}) := by
  have hnormal : (hallCore ↥S).Normal := hallCore_normal
  have hKnormal : (commutator ↥S).Normal := inferInstance
  refine
    { primeCyclicTI := OrientedCoreFamily.isPrimeCyclicTIHyp_commutator hodd hc
      right_le_H := OrientedCoreFamily.le_hallCore_subgroupOf_W₂ hc
      H_le_K := ?_
      A_subset := subset_rfl
      A_conj_mem := ?_
      centralizer_sdiff_subset := ?_
      U_ne_bot := ?_
      sup_H_U := OrientedCoreFamily.sup_hallCore_subgroupOf_eq_commutator hc
      disjoint_H_U := ?_
      le_normalizer_U := OrientedCoreFamily.le_normalizer_subgroupOf hc.le_normalizer_E
      inf_centralizer_U_eq_bot := ?_ }
  · rw [← OrientedCoreFamily.sup_hallCore_subgroupOf_eq_commutator hc]; exact le_sup_left
  · intro g a ha
    refine ⟨by simpa [mul_assoc] using hKnormal.conj_mem a ha.1 g⁻¹, ?_⟩
    intro hcon
    refine ha.2 ?_
    have hc1 : g⁻¹ * a * g = 1 := hcon
    calc a = g * (g⁻¹ * a * g) * g⁻¹ := by group
      _ = 1 := by rw [hc1]; group
  · intro h _ _ x hx
    exact ⟨(Subgroup.mem_inf.1 hx.1).1, hx.2⟩
  · intro hbot
    refine hUne (Subgroup.card_eq_one.1 ?_)
    rw [← natCard_subgroupOf_eq_of_le hc.le_M_E, hbot]
    simp
  · rw [disjoint_iff]
    exact OrientedCoreFamily.inf_hallCore_subgroupOf_eq_bot hc
  · intro x hx hx1
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvU, hvc⟩ := Subgroup.mem_inf.1 hv
    have hvUG : (v : G) ∈ U := mem_subgroupOf.1 hvU
    have hxG : (x : G) ∈ W₁ := mem_subgroupOf.1 hx
    have hxG1 : (x : G) ≠ 1 := fun hcon => hx1 (Subtype.ext hcon)
    have hcomm : Commute ((v : G)) ((x : G)) :=
      congrArg (Subtype.val (p := fun y => y ∈ S))
        (Subgroup.mem_centralizer_singleton_iff.1 hvc)
    have hbot := hfree (x : G) hxG hxG1
    have hmem : (v : G) ∈ centralizerIn U (zpowers (x : G)) := by
      refine Subgroup.mem_inf.2 ⟨hvUG, Subgroup.mem_centralizer_iff.2 ?_⟩
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact (hcomm.zpow_right n).symm
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.2 (Subtype.ext hmem)

theorem coreCentralizer_eq_bot {S U : Subgroup G}
    (h : centralizerIn U (hallCoreOf S) = ⊥) :
    coreCentralizer (hallCore ↥S) (U.subgroupOf S) = ⊥ := by
  rw [coreCentralizer_hallCore_eq_subgroupOf]
  have h2 : U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn S : Subgroup G) : Set G) = ⊥ := h
  rw [h2, Subgroup.bot_subgroupOf]

theorem bridge_local_rows_of_core_data {S U W₁ W₂ : Subgroup G} {uu qq : ℕ}
    {I J : Type} {i0 : I} {j0' : J} {α : I → ↥W₁ → ℂ} {β : J → ↥W₂ → ℂ}
    {w : I → J → ↥(W₁ ⊔ W₂) → ℂ} {σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ)}
    {ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)} {δ : J → ℂ} {μ : J → ↥S → ℂ} {η : I → J → G → ℂ}
    {γ b : J → ↥S → ℂ}
    (hS : IsTypePBridgeSetup G S U W₁ W₂ i0 j0' α β w σ ω δ μ η γ b)
    (hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    (hUne : U ≠ ⊥) (hfree : IsFixedPointFreeOn U W₁)
    (hCbot : centralizerIn U (hallCoreOf S) = ⊥)
    (hmac : IsMinimalAbelianCore (commutator ↥S) (W₁.subgroupOf S) (W₂.subgroupOf S)
      (hallCore ↥S) (U.subgroupOf S))
    (hu : uu = Nat.card ↥U) (hq : qq = Nat.card ↥W₁) {j : J} (hj : j ≠ j0') :
    δ j = 1 ∧
      (∃ χ : ↥(⁅S, S⁆ : Subgroup G) → ℂ, χ ∈ Irr ↥(⁅S, S⁆ : Subgroup G) ∧
        (∀ y : ↥(⁅S, S⁆ : Subgroup G), χ y = μ j ⟨(y : G),
          (Subgroup.commutator_le_self S) y.2⟩) ∧
        χ 1 = (uu : ℂ) ∧
        ∀ y : ↥(⁅S, S⁆ : Subgroup G), (y : G) ∉ Prep03.hallCoreIn S → χ y = 0) ∧
      (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0) ∧
      cfInner (b j) (b j) = (((uu : ℚ) - 1) / (qq : ℚ) + 2 : ℚ) := by
  classical
  have h1 : W₁ ≤ S := hS.config.config.le_M_W₁
  have h2 : W₂ ≤ S := hS.config.config.le_M_W₂
  have hU : U ≤ S := hS.config.config.le_M_E
  have hodd : Odd (Nat.card G) := hS.ambient.odd_natCard
  have hbc := isPrimeTIBridgeConfig_subgroupOf hodd hS.config.config hUne hfree
  have hC : coreCentralizer (hallCore ↥S) (U.subgroupOf S) = ⊥ := coreCentralizer_eq_bot hCbot
  set σloc := OrientedCoreFamily.sigmaLocalHom h1 h2 hS.sigma_isTIExtension with hσlocdef
  have hσloc := OrientedCoreFamily.isCyclicTIIsometry_sigmaLocalHom h1 h2 hS.sigma_isTIExtension
  have hβ1 : β j ≠ 1 := by
    rw [← hS.beta_principal]
    exact fun hcon => hj (hS.beta_injective hcon)
  set jl := localIrrIndex h2 (hS.beta_mem j) with hjldef
  have hjl : jl ≠ principalIrr ↥(W₂.subgroupOf S) :=
    localIrrIndex_ne_principalIrr h2 (hS.beta_mem j) hβ1
  have haxis : ((σloc (hbc.primeCyclicTI.isCyclicTIPair.basisProdIrr
        (principalIrr ↥(W₁.subgroupOf S), jl))) : ↥S → ℂ) = σ (w i0 j) :=
    sigmaLocalHom_basisProdIrr_eq h1 h2 hS.sigma_isTIExtension _ hW (hS.beta_mem j) rfl
      hS.alpha_principal hS.prod_eq
  obtain ⟨hsign, hmueq⟩ := primeTIirr_eq_of_sign_smul hbc.primeCyclicTI hσloc
    (hS.sign_eq j) haxis (by rw [← hS.mu_eq j]; exact hS.mu_mem_Irr j)
  have hmu : μ j = hbc.primeCyclicTI.primeTIirr σloc (principalIrr ↥(W₁.subgroupOf S)) jl := by
    rw [hS.mu_eq j, ← hmueq]
  have hchi1 : hbc.primeCyclicTI.primeTIres σloc jl 1 = (Nat.card ↥(U.subgroupOf S) : ℂ) :=
    hmac.primeTIres_one_eq_natCard_of_coreCentralizer_eq_bot hbc.primeCyclicTI hσloc hjl hC
  have hchi1' : hbc.primeCyclicTI.primeTIres σloc jl 1 = (uu : ℂ) := by
    rw [hchi1, natCard_subgroupOf_eq_of_le hU, hu]
  have hchi0 : ∀ k : ↥(commutator ↥S), (k : ↥S) ∉ hallCore ↥S →
      hbc.primeCyclicTI.primeTIres σloc jl k = 0 := fun k hk =>
    hmac.primeTIres_eq_zero_of_notMem_core_of_coreCentralizer_eq_bot hbc.primeCyclicTI hσloc
      hjl hC hk
  have hδ1 : δ j = 1 := by rw [hsign, hbc.primeTISign_eq_one hσloc hchi1]
  have hbj : b j = hbc.bridgeChar (σ := σloc) (j := jl) := by
    funext x
    rw [hS.b_eq j, Pi.sub_apply, hS.gamma_eq j,
      indClassFun_hallCoreIn_sup_eq_bridgePermChar h1, hmu, hbc.bridgeChar_apply]
  refine ⟨hδ1, ⟨hbc.primeCyclicTI.primeTIres σloc jl ∘ (commutatorSubgroupEquiv S).symm,
    ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine mem_Irr_of_comp_mulEquiv (commutatorSubgroupEquiv S) ?_
    have hcomp : (hbc.primeCyclicTI.primeTIres σloc jl ∘
          ((commutatorSubgroupEquiv S).symm : ↥(⁅S, S⁆ : Subgroup G) → ↥(commutator ↥S)))
        ∘ ((commutatorSubgroupEquiv S) : ↥(commutator ↥S) → ↥(⁅S, S⁆ : Subgroup G))
        = hbc.primeCyclicTI.primeTIres σloc jl := by
      funext x; simp
    rw [hcomp]
    exact hbc.primeCyclicTI.primeTIres_mem_Irr hσloc jl
  · intro y
    rw [Function.comp_apply, hbc.primeCyclicTI.primeTIres_apply,
      coe_commutatorSubgroupEquiv_symm, hmu]
  · rw [Function.comp_apply, map_one, hchi1']
  · intro y hy
    refine hchi0 _ ?_
    rw [coe_commutatorSubgroupEquiv_symm]
    exact fun hcon => hy ⟨_, hcon, rfl⟩
  · intro x hx
    rw [hbj]
    refine hbc.bridgeChar_eq_zero_of_notMem_sdiff_union hσloc hchi1 hchi0 ?_
    exact fun hcon => hx (mem_mixedSupport_of_mem_sdiff_union h1 h2 hcon)
  · rw [hbj, hbc.cfInner_bridgeChar_self hσloc hjl, natCard_subgroupOf_eq_of_le hU,
      natCard_subgroupOf_eq_of_le h1, ← hu, ← hq]
    push_cast
    ring

end LocalRows

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep03
open CFSG.FeitThompson.Prep05 (IsMinimalSimpleOdd)

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

theorem natCard_W₁_dvd_natCard_U_sub_one
    (h₃ : Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G] [Fintype G]
    (hA : IsAmbient G) {S U W₁ W₂ : Subgroup G} (hcfg : IsPConfigSetup G S U W₁ W₂) :
    Nat.card ↥W₁ ∣ Nat.card ↥U - 1 := by
  have hG : IsMinimalSimpleOdd G :=
    ⟨hA.odd_natCard, hA.isSimpleGroup, hA.not_isMulCommutative, hA.forall_isSolvable⟩
  have H := h₃ G hG S U W₁ W₂ hcfg.isCoatom hcfg.config
    (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  exact natCard_dvd_natCard_sub_one_of_isFixedPointFreeOn
    (le_sup_right.trans H.2.2.2.2.2.2.2.2.2.1.le_normalizer)
    H.2.2.2.2.2.2.2.2.2.2.2.1

theorem coprime_natCard_W₁_natCard_W₂
    (h₃ : Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G] [Fintype G]
    (hA : IsAmbient G) {S U W₁ W₂ : Subgroup G} (hcfg : IsPConfigSetup G S U W₁ W₂) :
    (Nat.card ↥W₁).Coprime (Nat.card ↥W₂) := by
  have hG : IsMinimalSimpleOdd G :=
    ⟨hA.odd_natCard, hA.isSimpleGroup, hA.not_isMulCommutative, hA.forall_isSolvable⟩
  obtain ⟨-, hp, hq, -, -, hpq, -⟩ :=
    h₃ G hG S U W₁ W₂ hcfg.isCoatom hcfg.config (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  exact (Nat.coprime_primes hq hp).2 fun h => hpq h.symm

theorem cfInner_self_indG_of_supported
    (h₃ : Statements.FNI_type_p_elementary_core_structure.{u}) {G : Type u} [Group G] [Fintype G]
    (hA : IsAmbient G) {S U W₁ W₂ : Subgroup G} (hcfg : IsPConfigSetup G S U W₁ W₂)
    {f : ↥S → ℂ} (hf : f ∈ virtualChars ↥S)
    (hf0 : ∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) :
    cfInner (indG S f) (indG S f) = cfInner f f := by
  obtain ⟨-, -, -, -, -, hiso, -⟩ := FCH_type_p_core_mixed_ti h₃ G hA S U W₁ W₂ hcfg
  exact hiso f f (virtualChars_le_classFun hf) (virtualChars_le_classFun hf) hf0 hf0

private theorem bridge_local_rows
    (_h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (_h₂ : Statements.FNI_p_configuration_kappa_factors.{u})
    (_h₃ : Statements.FNI_type_p_elementary_core_structure.{u})
    (_h₄ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (_h₅ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (_h₆ : Statements.FTS_canonical_signalizer_structure.{u})
    (_h₇ : Statements.FTS_type_II_extended_support_ti.{u}) :
    ∀ (G : Type u) [Group G] [Fintype G] (S U W₁ W₂ : Subgroup G) (u q : ℕ)
      (I J : Type) (i0 : I) (j0' : J) (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ)
      (w : I → J → ↥(W₁ ⊔ W₂) → ℂ) (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ))
      (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)) (δ : J → ℂ) (μ : J → ↥S → ℂ) (η : I → J → G → ℂ)
      (γ b : J → ↥S → ℂ),
      IsTypePBridgeSetup G S U W₁ W₂ i0 j0' α β w σ ω δ μ η γ b →
      u = Nat.card ↥U → q = Nat.card ↥W₁ →
      ∀ j : J, j ≠ j0' → δ j = 1 ∧
        (∃ χ : ↥(⁅S, S⁆ : Subgroup G) → ℂ, χ ∈ Irr ↥(⁅S, S⁆ : Subgroup G) ∧
          (∀ y : ↥(⁅S, S⁆ : Subgroup G), χ y = μ j ⟨(y : G),
            (Subgroup.commutator_le_self S) y.2⟩) ∧
          χ 1 = (u : ℂ) ∧
          ∀ y : ↥(⁅S, S⁆ : Subgroup G), (y : G) ∉ hallCoreIn S → χ y = 0) ∧
        (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0) ∧
        cfInner (b j) (b j) = (((u : ℚ) - 1) / (q : ℚ) + 2 : ℚ) := by
  intro G _ _ S U W₁ W₂ u q I J i0 j0' α β w σ ω δ μ η γ b hS hu hq j hj
  have hA : IsAmbient G := hS.ambient
  have hG : IsMinimalSimpleOdd G :=
    ⟨hA.odd_natCard, hA.isSimpleGroup, hA.not_isMulCommutative, hA.forall_isSolvable⟩
  obtain ⟨-, -, -, -, -, -, hUne, -, -, -, -, hfree, -⟩ :=
    _h₃ G hG S U W₁ W₂ hS.config.isCoatom hS.config.config (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  have hCbot := (FNI_type_p_inner_action_faithful.{u} _h₁ _h₃ G hG S U W₁ W₂
    hS.config.isCoatom hS.config.config).1
  have hmac := OrientedCoreFamily.isMinimalAbelianCore_of_isWitnessedPConfiguration _h₃ hA
    hS.config.isCoatom hS.config.config
  exact LocalRows.bridge_local_rows_of_core_data hS
    (hS.isCyclicTIPair_sup (coprime_natCard_W₁_natCard_W₂ _h₃ hA hS.config))
    hUne hfree hCbot hmac hu hq hj

private theorem bridge_remainder_reality
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₄ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₅ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₆ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₇ : Statements.FTS_type_II_extended_support_ti.{u}) :
    ∀ (G : Type u) [Group G] [Fintype G] (S U W₁ W₂ : Subgroup G)
      (I J : Type) (i0 : I) (j0' : J) (α : I → ↥W₁ → ℂ) (β : J → ↥W₂ → ℂ)
      (w : I → J → ↥(W₁ ⊔ W₂) → ℂ) (σ : (↥(W₁ ⊔ W₂) → ℂ) → (↥S → ℂ))
      (ω : (↥(W₁ ⊔ W₂) → ℂ) → (G → ℂ)) (δ : J → ℂ) (μ : J → ↥S → ℂ) (η : I → J → G → ℂ)
      (γ b : J → ↥S → ℂ),
      IsTypePBridgeSetup G S U W₁ W₂ i0 j0' α β w σ ω δ μ η γ b →
      ∀ j₀ : J, j₀ ≠ j0' →
        ∀ Γ : G → ℂ, Γ = indG S (b j₀) - 1 + η i0 j₀ →
          IsRealValued Γ ∧
          ∀ j : J, j ≠ j0' → ∀ x : G, indG S (b j) x = 1 - η i0 j x + Γ x := by
  intro G _ _ S U W₁ W₂ I J i0 j0' α β w σ ω δ μ η γ b hS j₀ hj₀ Γ hΓ
  obtain ⟨-, -, -, hTI, -, -, -⟩ :=
    FCH_type_p_core_mixed_ti h₃ G hS.ambient S U W₁ W₂ hS.config
  have hiso : ∀ f : ↥S → ℂ, f ∈ virtualChars ↥S →
      (∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → f x = 0) →
      cfInner (indG S f) (indG S f) = cfInner f f :=
    fun f hf hf0 => cfInner_self_indG_of_supported h₃ hS.ambient hS.config hf hf0
  have hrow := bridge_local_rows h₁ h₂ h₃ h₄ h₅ h₆ h₇ G S U W₁ W₂ (Nat.card ↥U) (Nat.card ↥W₁)
    I J i0 j0' α β w σ ω δ μ η γ b hS rfl rfl
  have hδ1 : ∀ j : J, j ≠ j0' → δ j = 1 := fun j hj => (hrow j hj).1
  have hsupp : ∀ j : J, j ≠ j0' → ∀ x : ↥S, (x : G) ∉ mixedSupport S W₁ W₂ → b j x = 0 :=
    fun j hj => (hrow j hj).2.2.1
  exact ⟨hS.isRealValued_remainder hTI hiso hδ1 hsupp hj₀ hΓ,
    fun j hj x => hS.indG_b_eq_of_remainder hTI hiso hδ1 hsupp hj₀ hΓ hj x⟩

theorem FCH_type_p_actual_bridge_remainder
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_p_configuration_kappa_factors.{u})
    (h₃ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₄ : Statements.FPF_non_type_i_sigma_core_identities.{u})
    (h₅ : Statements.FTS_canonical_signalizer_full_support_coprimality.{u})
    (h₆ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₇ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FCH_type_p_actual_bridge_remainder.{u} := by
  intro G _ _ hA S U W₁ W₂ hcfg u p q hu _hp hq I J hI hJ i0 j0' α β hα hβ hαinj hβinj
    hαsurj hβsurj hα0 hβ0 w hw σ ω hσ hω δ μ η hδ hμ hμIrr hη γ b hγ hb
  have hS : IsTypePBridgeSetup G S U W₁ W₂ i0 j0' α β w σ ω δ μ η γ b :=
    { ambient := hA, config := hcfg, alpha_mem := hα, beta_mem := hβ,
      alpha_injective := hαinj, beta_injective := hβinj, alpha_surjective := hαsurj,
      beta_surjective := hβsurj, alpha_principal := hα0, beta_principal := hβ0,
      prod_eq := hw, sigma_isTIExtension := hσ, omega_isTIExtension := hω, sign_eq := hδ,
      mu_eq := hμ, mu_mem_Irr := hμIrr, eta_eq := hη, gamma_eq := hγ, b_eq := hb }
  have hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂) :=
    coprime_natCard_W₁_natCard_W₂ h₃ hA hcfg
  have hrow := bridge_local_rows h₁ h₂ h₃ h₄ h₅ h₆ h₇ G S U W₁ W₂ u q I J i0 j0' α β w σ ω δ μ η
    γ b hS hu hq
  refine ⟨fun j hj => ?_, ?_, fun j₀ hj₀ Γ hΓ => ?_⟩
  ·
    obtain ⟨hδ1, hχ, hsupp, hnorm⟩ := hrow j hj
    exact ⟨hδ1, hχ, hS.b_mem_virtualChars j, hsupp, hnorm⟩
  ·
    rw [hq, hu]
    exact natCard_W₁_dvd_natCard_U_sub_one h₃ hA hcfg
  ·
    obtain ⟨hΓreal, hdec⟩ := bridge_remainder_reality h₁ h₂ h₃ h₄ h₅ h₆ h₇ G S U W₁ W₂ I J i0 j0'
      α β w σ ω δ μ η γ b hS j₀ hj₀ Γ hΓ
    refine ⟨hS.remainder_mem_virtualChars hcop j₀ hΓ, hΓreal,
      hS.cfInner_remainder_one hcop hj₀ hΓ, fun j hj => ?_⟩
    obtain ⟨-, -, hsupp, hnorm⟩ := hrow j hj
    refine ⟨hdec j hj, ?_, fun x hx => indG_eq_zero_of_notMem_sat_union hsupp hx⟩
    rw [cfInner_self_indG_of_supported h₃ hA hcfg (hS.b_mem_virtualChars j) hsupp]
    exact hnorm

end CFSG.FeitThompson.Proofs

end
