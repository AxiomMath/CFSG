module

public import CFSG.FeitThompson.Representations.ActualPairedSupportSaturation
public import CFSG.FeitThompson.Local.PairedSupportingCrossedAlternatives
public import CFSG.FeitThompson.Local.PairedSupportingInnerFullNormOrder
public import CFSG.FeitThompson.Local.AllTypeIKernelPartition
public import CFSG.FeitThompson.Representations.CyclicTIIsometryExistence
public import CFSG.FeitThompson.OddOrder.BoundedKernelEqualsComplement
public import CFSG.FeitThompson.OddOrder.ExceptionalPrimesSupportThreshold
public import CFSG.FeitThompson.OddOrder.GeometricSumCongruences

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace PairedSupportingKernel

open Subgroup _root_.CFSG.FeitThompson

attribute [local instance] _root_.CFSG.FeitThompson.subgroupFintype

universe u

theorem intModEq_one_of_dvd_sub_one {m a : ℕ} (ha : 1 ≤ a) (h : m ∣ a - 1) :
    (a : ℤ) ≡ 1 [ZMOD (m : ℤ)] := by
  have hz : (m : ℤ) ∣ (a : ℤ) - 1 := by
    have h2 := Int.natCast_dvd_natCast.2 h
    rwa [Nat.cast_sub ha, Nat.cast_one] at h2
  exact (Int.modEq_iff_dvd.2 hz).symm

theorem ediv_le_sub_one_of_div_le {m a : ℕ} (hm : 0 < m) (ha : 1 ≤ a) (hdvd : m ∣ a - 1)
    (hb : ((a : ℚ) - 1) / (m : ℚ) ≤ (m : ℚ) - 1) :
    ((a : ℤ) - 1) / (m : ℤ) ≤ (m : ℤ) - 1 := by
  obtain ⟨k, hk⟩ := hdvd
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hmq : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm
  have hkz : (a : ℤ) - 1 = (m : ℤ) * (k : ℤ) := by
    have h' : ((a - 1 : ℕ) : ℤ) = ((m * k : ℕ) : ℤ) := by
      exact_mod_cast congrArg (fun n : ℕ => n) hk
    rw [Nat.cast_sub ha] at h'
    push_cast at h'
    linarith
  have hkq : (k : ℚ) ≤ (m : ℚ) - 1 := by
    have hq : ((a : ℚ) - 1) = (m : ℚ) * (k : ℚ) := by exact_mod_cast hkz
    rw [hq, mul_div_cancel_left₀ _ (ne_of_gt hmq)] at hb
    exact hb
  rw [hkz, Int.mul_ediv_cancel_left _ (ne_of_gt hmz)]
  exact_mod_cast hkq

variable {G : Type u} [Group G] [Fintype G]

@[expose] noncomputable def omegaUnbundled {W₁ W₂ : Subgroup G} (hcyc : IsCyclic ↥(W₁ ⊔ W₂))
    (τ : ↥(classFun ↥(W₁ ⊔ W₂)) →ₗ[ℂ] ↥(classFun G)) :
    (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ) :=
  ((classFun G).subtype).comp (τ.comp
    ((LinearEquiv.ofTop _ (_root_.CFSG.FeitThompson.Proofs.Recip.classFunTop hcyc)).symm.toLinearMap))

omit [Fintype G] in
theorem omegaUnbundled_apply {W₁ W₂ : Subgroup G} (hcyc : IsCyclic ↥(W₁ ⊔ W₂))
    (τ : ↥(classFun ↥(W₁ ⊔ W₂)) →ₗ[ℂ] ↥(classFun G)) (f : ↥(W₁ ⊔ W₂) → ℂ) :
    omegaUnbundled hcyc τ f =
      ((τ ⟨f, by rw [_root_.CFSG.FeitThompson.Proofs.Recip.classFunTop hcyc]; trivial⟩ :
        ↥(classFun G)) : G → ℂ) := rfl

theorem isOmegaMap_omegaUnbundled {W₁ W₂ : Subgroup G} (hcyc : IsCyclic ↥(W₁ ⊔ W₂))
    {τ : ↥(classFun ↥(W₁ ⊔ W₂)) →ₗ[ℂ] ↥(classFun G)}
    (hτ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ τ) :
    IsOmegaMap W₁ W₂ (omegaUnbundled hcyc τ) := by
  refine ⟨fun f => _root_.CFSG.FeitThompson.Proofs.Recip.isClassFun_of_mem (τ _).2, ?_, ?_, ?_, ?_⟩
  · intro f g
    rw [cfInnerFin_eq_cfInner, cfInnerFin_eq_cfInner, omegaUnbundled_apply,
      omegaUnbundled_apply, hτ.inner_eq]
  · intro f hf
    rw [omegaUnbundled_apply]
    exact hτ.map_virtualChars _ hf
  · have h1 : (⟨(1 : ↥(W₁ ⊔ W₂) → ℂ), by
        rw [_root_.CFSG.FeitThompson.Proofs.Recip.classFunTop hcyc]; trivial⟩ :
        ↥(classFun ↥(W₁ ⊔ W₂)))
        = principalClassFun ↥(W₁ ⊔ W₂) := by
      apply Subtype.ext; rw [coe_principalClassFun]
    rw [omegaUnbundled_apply, h1, hτ.map_principalClassFun, coe_principalClassFun]
  · intro f hf
    rw [omegaUnbundled_apply,
      hτ.eq_indClassFun _ (fun z hz => hf z (by
        rwa [_root_.CFSG.FeitThompson.Proofs.cyclicTIDiff_eq_cyclicTIset] at hz)),
      _root_.CFSG.FeitThompson.Proofs.indTop_eq_indClassFun]

omit [Fintype G] in
theorem isCyclicTIPair_swap_sup {W₁ W₂ : Subgroup G}
    (h : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂) : IsCyclicTIPair (W₂ ⊔ W₁) W₂ W₁ := by
  rw [sup_comm W₂ W₁]; exact h.swap

theorem exists_isPBridgeData (hodd : Odd (Nat.card G)) {S L U W₁ W₂ : Subgroup G}
    (hS : IsCoatom S) (hcfg : IsWitnessedPConfiguration S U W₁ W₂)
    (hL : IsCoatom L) (hLI : IsTypeI L) :
    ∃ (I J : Type u) (_ : Fintype I) (_ : Fintype J) (α : I → (↥W₁ → ℂ))
      (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J) (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
      (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
      (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
      (bfam : J → (↥S → ℂ)),
      IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam := by
  classical
  have hpair : IsCyclicTIPair (W₂ ⊔ W₁) W₂ W₁ :=
    isCyclicTIPair_swap_sup
      (isCyclicTIPair_map_subtype_of_isWitnessedPConfiguration hodd hcfg)
  have hcyc : IsCyclic ↥(W₂ ⊔ W₁) := hpair.isCyclic
  obtain ⟨τ, hτ⟩ := hpair.exists_isCyclicTIIsometry
  set ω : (↥(W₂ ⊔ W₁) → ℂ) →ₗ[ℂ] (G → ℂ) := omegaUnbundled hcyc τ with hωdef
  have hω : IsOmegaMap W₂ W₁ ω := isOmegaMap_omegaUnbundled hcyc hτ
  have _ : Fintype ↥(Irr ↥W₂) := Fintype.ofFinite _
  have _ : Fintype ↥(Irr ↥W₁) := Fintype.ofFinite _
  have hIrr2 : IsIrrIndexing W₂ (Subtype.val : ↥(Irr ↥W₂) → (↥W₂ → ℂ)) (principalIrr ↥W₂) :=
    ⟨Subtype.val_injective, Subtype.range_val, coe_principalIrr _⟩
  have hIrr1 : IsIrrIndexing W₁ (Subtype.val : ↥(Irr ↥W₁) → (↥W₁ → ℂ)) (principalIrr ↥W₁) :=
    ⟨Subtype.val_injective, Subtype.range_val, coe_principalIrr _⟩
  set w : ↥(Irr ↥W₂) → ↥(Irr ↥W₁) → (↥(W₂ ⊔ W₁) → ℂ) :=
    fun i j => hpair.prodChar (i : ↥W₂ → ℂ) (j : ↥W₁ → ℂ) with hw
  have hprod : IsProductCharFamily W₂ W₁ (Subtype.val : ↥(Irr ↥W₂) → (↥W₂ → ℂ))
      (Subtype.val : ↥(Irr ↥W₁) → (↥W₁ → ℂ)) w := by
    intro i j x y hxy
    exact hpair.prodChar_apply_mul _ _ x.2 y.2
  obtain ⟨σS, δ', μ', γ', b', hdata⟩ :=
    _root_.CFSG.FeitThompson.Proofs.Recip.exists_reciprocal_bridge_data (T := S) (W₂ := W₁) (W₁ := W₂)
      hodd hS hcfg hL hLI hIrr2 hIrr1 hprod hω
  exact ⟨_, _, inferInstance, inferInstance, _, _, principalIrr ↥W₁, principalIrr ↥W₂,
    _root_.CFSG.FeitThompson.Proofs.Recip.wR w, σS, _root_.CFSG.FeitThompson.Proofs.Recip.omegaR ω, _,
    δ', μ', γ', b', hdata⟩

theorem isPBridgeData_replace {S L L' U W₁ W₂ : Subgroup G} {I J : Type u}
    [Fintype I] [Fintype J] {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)}
    {σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
    {η : I → J → (G → ℂ)} {δ : J → ℂ} {μ : J → (↥S → ℂ)} {γ : ↥S → ℂ} {bfam : J → (↥S → ℂ)}
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (hL' : IsCoatom L') (hLI' : IsTypeI L') :
    IsPBridgeData S L' U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam :=
  ⟨hdata.isCoatom_S, hdata.isPConfig, hL', hLI', hdata.isIrrIndexing_W₁, hdata.isIrrIndexing_W₂,
    hdata.isProductCharFamily, hdata.isSigmaMap, hdata.isOmegaMap, hdata.eta_eq,
    hdata.delta_sign, hdata.mu_eq, hdata.mu_irr, hdata.gamma_eq, hdata.b_eq⟩

end PairedSupportingKernel

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.PairedSupportingKernel
open CFSG.FeitThompson.PairedSupportingInnerNorm
open CFSG.FeitThompson.Prep05

attribute [local instance] CFSG.FeitThompson.subgroupFintype

universe u

theorem cfInner_beta_nu_eq_zero
    (h₁ : Statements.FCH_actual_type_I_crossed_control.{u})
    (h₂ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₃ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₅ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (h₇ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₈ : Statements.FPF_type_I_frobenius.{u})
    (h₉ : Statements.FTS_type_I_dade_support.{u})
    (G : Type u) [Group G] [Fintype G]
    (hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G)
    (S T L M U V W₁ W₂ : Subgroup G)
    (hS : IsCoatom S) (hcfg : IsWitnessedPConfiguration S U W₁ W₂)
    (hT : IsCoatom T) (hcfgT : IsWitnessedPConfiguration T V W₂ W₁)
    (hL : IsCoatom L) (hIL : IsTypeI L) (hM : IsCoatom M) (hIM : IsTypeI M)
    (hnc : ∀ g : G, L ≠ _root_.CFSG.FeitThompson.conjSubgroup M g)
    (νL : (↥L → ℂ) → (G → ℂ)) (φL : ↥L → ℂ) (βL : G → ℂ)
    (hLdata : _root_.CFSG.FeitThompson.IsCoreCharData L νL φL βL)
    (νM : (↥M → ℂ) → (G → ℂ)) (φM : ↥M → ℂ) (βM : G → ℂ)
    (hMdata : _root_.CFSG.FeitThompson.IsCoreCharData M νM φM βM)
    (hle : CFSG.FeitThompson.hallCoreIndex L
      ≤ Nat.card ↥W₂ * Nat.card ↥W₁)
    (hthr1 : ((Nat.card ↥U : ℚ) - 1) / (Nat.card ↥W₁ : ℚ)
      < ((Nat.card ↥(_root_.CFSG.FeitThompson.hallCoreIn L) : ℚ) - 1)
        / (CFSG.FeitThompson.hallCoreIndex L : ℚ))
    (hthr2 : ((Nat.card ↥V : ℚ) - 1) / (Nat.card ↥W₂ : ℚ)
      < ((Nat.card ↥(_root_.CFSG.FeitThompson.hallCoreIn L) : ℚ) - 1)
        / (CFSG.FeitThompson.hallCoreIndex L : ℚ)) :
    cfInner βL (νM φM) = 0 := by
  classical
  have hamb : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG2.odd_natCard, hG2.isSimpleGroup, hG2.not_isMulCommutative, hG2.isSolvable_of_ne_top⟩
  obtain ⟨I, J, _, _, α, β, i₀, j₀, w, σ, ω, η, δ, μ, γ, bfam, hdata⟩ :=
    exists_isPBridgeData hG2.odd_natCard hS hcfg hL hIL
  obtain ⟨-, ε, χ, -, hχalt, -, hβexp, -⟩ :=
    FCH_actual_paired_support_saturation.{u} h₂ h₃ h₅ h₇ h₈ h₉ G hG2 S L U W₁ W₂ I J
      inferInstance inferInstance α β i₀ j₀ w σ ω η δ μ γ bfam hdata T V hT hcfgT
      _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
      νL (CFSG.FeitThompson.CoreCharData.isCoherentDade hLdata)
      φL (CFSG.FeitThompson.CoreCharData.mem_calLFam hLdata)
      (CFSG.FeitThompson.CoreCharData.apply_one hLdata)
      βL (CFSG.FeitThompson.CoreCharData.beta_eq hLdata)
      hle hthr1 hthr2
  obtain ⟨hMorth, -⟩ :=
    FCH_type_I_P_bridge_orthogonality.{u} h₂ h₃ h₅ G hG2 S M U W₁ W₂ I J
      inferInstance inferInstance α β i₀ j₀ w σ ω η δ μ γ bfam
      (isPBridgeData_replace hdata hM hIM)
      νM (CFSG.FeitThompson.CoreCharData.isCoherentDade hMdata)
      φM (CFSG.FeitThompson.CoreCharData.mem_calLFam hMdata)
      (CFSG.FeitThompson.CoreCharData.apply_one hMdata)
      βM (CFSG.FeitThompson.CoreCharData.beta_eq hMdata)
  have hetaorth : ∀ (i : I) (j : J), cfInner (η i j) (νM φM) = 0 := by
    intro i j
    have h0 := hMorth φM (CFSG.FeitThompson.CoreCharData.mem_calLFam hMdata) i j
    rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner] at h0
    rw [← conj_cfInner, h0, map_zero]
  obtain ⟨-, hfamorth, -⟩ :=
    h₁ G hG2 M L hM hL hnc hIM hIL
      (Nat.card ↥(CFSG.FeitThompson.hallCoreIn M))
      (Nat.card ↥(CFSG.FeitThompson.hallCoreIn L))
      (CFSG.FeitThompson.hallCoreIndex M)
      (CFSG.FeitThompson.hallCoreIndex L) rfl rfl rfl rfl
      νM (CFSG.FeitThompson.CoreCharData.isCoherentDade hMdata)
      νL (CFSG.FeitThompson.CoreCharData.isCoherentDade hLdata)
      φM (CFSG.FeitThompson.CoreCharData.mem_calLFam hMdata)
      (CFSG.FeitThompson.CoreCharData.apply_one hMdata)
      φL (CFSG.FeitThompson.CoreCharData.mem_calLFam hLdata)
      (CFSG.FeitThompson.CoreCharData.apply_one hLdata)
      βM βL (CFSG.FeitThompson.CoreCharData.beta_eq hMdata)
      (CFSG.FeitThompson.CoreCharData.beta_eq hLdata)
      _ _ rfl rfl
  have hχorth : cfInner χ (νM φM) = 0 := by
    have hconjmem : (fun x => (starRingEnd ℂ) (φL x))
        ∈ CFSG.FeitThompson.calLFam L := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hclosed, -⟩ := h₃ G hamb L hL hIL
      have h2' := hclosed φL (by
        rw [hallIndFamily_eq_calLFam]
        exact CFSG.FeitThompson.CoreCharData.mem_calLFam hLdata)
      rwa [hallIndFamily_eq_calLFam] at h2'
    rcases hχalt with rfl | rfl
    · have h0 := hfamorth φM (CFSG.FeitThompson.CoreCharData.mem_calLFam hMdata)
        φL (CFSG.FeitThompson.CoreCharData.mem_calLFam hLdata)
      rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner] at h0
      rw [← conj_cfInner, h0, map_zero]
    · have h0 := hfamorth φM (CFSG.FeitThompson.CoreCharData.mem_calLFam hMdata)
        _ hconjmem
      rw [CFSG.FeitThompson.cfInnerFin_eq_cfInner] at h0
      rw [cfInner_neg_left, ← conj_cfInner, h0, map_zero, neg_zero]
  rw [hβexp, cfInner_sub_left, hχorth, sub_zero, cfInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cfInner_sum_smul_left]
  exact Finset.sum_eq_zero fun j _ => by rw [hetaorth i j, mul_zero]

theorem FNI_paired_supporting_kernel_collapse
    (h₁ : Statements.FCH_actual_type_I_crossed_control.{u})
    (h₂ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₃ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₄ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₅ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (h₆ : Statements.FNI_paired_supporting_maxima_nonconjugate.{u})
    (h₇ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₈ : Statements.FPF_type_I_frobenius.{u})
    (h₉ : Statements.FTS_type_I_dade_support.{u})
    (h₁₀ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FNI_paired_supporting_kernel_collapse.{u} := by
  intro G _ _ hG S T L U V W₁ W₂ y hsetup hIL heL M hM hIM hHM heM νL φL βL hLdata νM φM βM hMdata
  classical
  have hG2 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG5 : IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  set p := Nat.card ↥W₂ with hp
  set q := Nat.card ↥W₁ with hq
  obtain ⟨-, hpp, hqq, hop, hoq, hpqne, hUne, -, -, hsemiUW, -, hfreeUW, -⟩ :=
    h₇ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.config_S p q rfl rfl
  set H : Subgroup G := _root_.CFSG.FeitThompson.hallCoreIn L with hHdef
  have hUH : U ≤ H := hsetup.le_hallCoreIn_L
  have hnc : ∀ g : G, L ≠ _root_.CFSG.FeitThompson.conjSubgroup M g :=
    fun g => h₆ G hG S T L U V W₁ W₂ y hsetup M hM hHM g
  have heL' : CFSG.FeitThompson.hallCoreIndex L = p * q := by
    rw [← CFSG.FeitThompson.relIndex_hallCoreIn_eq_hallCoreIndex]; exact heL
  have huQ : (Nat.card ↥U : ℚ) = ((p : ℚ) ^ q - 1) / ((p : ℚ) - 1) :=
    FNI_paired_supporting_inner_full_norm_order.{u} h₁ h₄ h₆ h₇ h₁₀ G hG S T L U V W₁ W₂ y
      hsetup hIL heL M hM hIM hHM heM νL φL βL hLdata νM φM βM hMdata
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hpp.one_lt
  have huN : Nat.card ↥U = ∑ i ∈ Finset.range q, p ^ i := by
    have hgeo := cast_geomSum_mul_sub_one (p := p) (q := q) hpp.one_le
    have h1 : (Nat.card ↥U : ℚ) * ((p : ℚ) - 1) = (p : ℚ) ^ q - 1 := by
      rw [huQ, div_mul_cancel₀ _ (by linarith)]
    have hcast : (Nat.card ↥U : ℚ) = ((∑ i ∈ Finset.range q, p ^ i : ℕ) : ℚ) :=
      mul_right_cancel₀ (b := (p : ℚ) - 1) (by linarith) (by rw [h1, hgeo])
    exact_mod_cast hcast
  have hu1 : 1 ≤ Nat.card ↥U := Nat.card_pos
  have hqu : q ∣ Nat.card ↥U - 1 :=
    natCard_dvd_natCard_sub_one_of_free (le_sup_right.trans hsemiUW.le_normalizer) hfreeUW
  have hpu : p ∣ Nat.card ↥U - 1 :=
    (Nat.modEq_iff_dvd' hu1).1 (huN ▸ sum_range_pow_modEq_one (p := p) (q := q) hqq.pos).symm
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).2 hpqne
  have hpqu : p * q ∣ Nat.card ↥U - 1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpu hqu
  have hpqh : p * q ∣ Nat.card ↥H - 1 := by
    have hEnorm : (W₁ ⊔ _root_.CFSG.FeitThompson.conjSubgroup W₂ y) ≤ normalizer (H : Set G) :=
      hsetup.isInternalSemidirectProduct.right_le.trans
        hsetup.isInternalSemidirectProduct.le_normalizer
    have hEfree : IsFixedPointFreeOn H (W₁ ⊔ _root_.CFSG.FeitThompson.conjSubgroup W₂ y) :=
      isFixedPointFreeOn_of_centralizer_eq_bot hsetup.centralizer_eq_bot
    have hEcard : Nat.card ↥(W₁ ⊔ _root_.CFSG.FeitThompson.conjSubgroup W₂ y) = p * q := by
      rw [← relIndex_eq_natCard_of_isInternalSemidirectProduct
        hsetup.isInternalSemidirectProduct]
      exact heL
    rw [← hEcard]
    exact natCard_dvd_natCard_sub_one_of_free hEnorm hEfree
  rcases FNI_paired_supporting_crossed_alternatives.{u} h₁ h₄ h₆ h₇ G hG S T L U V W₁ W₂ y
      hsetup hIL heL M hM hIM hHM heM νL φL βL hLdata νM φM βM hMdata with ⟨-, hb⟩ | ⟨hc, h3, h5⟩
  ·
    have hmpos : 0 < p * q := Nat.mul_pos hpp.pos hqq.pos
    have hm2 : (2 : ℤ) ≤ ((p * q : ℕ) : ℤ) := by
      have h2' : 2 ≤ p * q := by
        have := hpp.two_le; have := hqq.two_le; nlinarith
      exact_mod_cast h2'
    have hhmod : ((Nat.card ↥H : ℕ) : ℤ) ≡ 1 [ZMOD ((p * q : ℕ) : ℤ)] :=
      intModEq_one_of_dvd_sub_one Nat.card_pos hpqh
    have humod : ((Nat.card ↥U : ℕ) : ℤ) ≡ 1 [ZMOD ((p * q : ℕ) : ℤ)] :=
      intModEq_one_of_dvd_sub_one hu1 hpqu
    have hbound : ((Nat.card ↥H : ℤ) - 1) / ((p * q : ℕ) : ℤ) ≤ ((p * q : ℕ) : ℤ) - 1 := by
      refine ediv_le_sub_one_of_div_le hmpos Nat.card_pos hpqh ?_
      push_cast
      exact hb
    exact (eq_of_le_of_modEq_one_of_ediv_le hUH hUne hm2 hhmod humod hbound).symm
  ·
    by_contra hne
    have hq3 : q = 3 := hq.trans h3
    have hp5 : p = 5 := hp.trans h5
    have hu31 : Nat.card ↥U = 31 := by rw [huN, hq3, hp5]; norm_num
    have hqp : q < p := by omega
    have hv : Nat.card ↥V = (q ^ p - 1) / (q - 1) :=
      natCard_reciprocal_complement h₄ h₇ hG5 T V W₁ W₂ hsetup.isCoatom_T hsetup.config_T hqp
    rw [hq3, hp5] at hv
    have hv121 : Nat.card ↥V = 121 := by rw [hv]; norm_num
    have hUsub : U.subgroupOf H ≠ ⊤ := fun htop =>
      hne (le_antisymm (subgroupOf_eq_top.1 htop) hUH)
    have hcard : Nat.card ↥(U.subgroupOf H) = (5 ^ 3 - 1) / (5 - 1) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv, hu31]; norm_num
    have hmod : (Nat.card ↥H : ℤ) ≡ 1 [ZMOD 5 * 3] := by
      have hz : ((p * q : ℕ) : ℤ) ∣ (Nat.card ↥H : ℤ) - 1 := by
        have h2' := Int.natCast_dvd_natCast.2 hpqh
        rwa [Nat.cast_sub Nat.card_pos, Nat.cast_one] at h2'
      rw [hq3, hp5] at hz
      have h3' := (Int.modEq_iff_dvd.2 hz).symm
      push_cast at h3'
      exact h3'
    obtain ⟨e1, e2, -, hgap⟩ := exceptional_support_degree_gap hcard hmod hUsub
    have hthr1 : ((Nat.card ↥U : ℚ) - 1) / (q : ℚ)
        < ((Nat.card ↥H : ℚ) - 1)
          / (CFSG.FeitThompson.hallCoreIndex L : ℚ) := by
      rw [heL', hq3, hp5, hu31]
      norm_num at e1 e2 hgap ⊢
      linarith
    have hthr2 : ((Nat.card ↥V : ℚ) - 1) / (p : ℚ)
        < ((Nat.card ↥H : ℚ) - 1)
          / (CFSG.FeitThompson.hallCoreIndex L : ℚ) := by
      rw [heL', hq3, hp5, hv121]
      norm_num at e1 e2 hgap ⊢
      linarith
    exact hc (cfInner_beta_nu_eq_zero h₁ h₂ h₃ h₅ h₇ h₈ h₉ G hG2 S T L M U V W₁ W₂
      hsetup.isCoatom_S hsetup.config_S hsetup.isCoatom_T hsetup.config_T
      hsetup.isCoatom_L hIL hM hIM hnc νL φL βL hLdata νM φM βM hMdata
      (le_of_eq heL') hthr1 hthr2)

end

end CFSG.FeitThompson.Proofs
