module

public import CFSG.FeitThompson.Representations.TypeIIIIVTwoCoherentLayers
public import CFSG.FeitThompson.Representations.TypeIIIVCoherentCrossedRowData
public import CFSG.FeitThompson.Representations.TypeIIIIVRowDegreeKernel
public import CFSG.FeitThompson.Representations.LowFamilyBridgePrincipalAxis
public import CFSG.FeitThompson.Representations.PrincipalColumnProjectionGluesFamilies
public import CFSG.FeitThompson.Representations.DadeInductionCoprimePowerStable

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep05

universe u

theorem natCard_W₂_ne_natCard_W₁_of_isTypeIII_or_isTypeIV {G : Type u} [Group G] [Finite G]
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    (hG : IsMinimalSimpleOdd G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Nat.card W₂ ≠ Nat.card W₁ :=
  (CFSG.FeitThompson.Proofs.FPF_type_iii_iv_chief_data h₅ G hG M U W₁ W₂ hM htype hc
    (Nat.card W₂) (Nat.card W₁) rfl rfl).2.2.2.2.1

theorem cyclicTIDiff_subset_dadeA0 {G : Type*} [Group G] (M W₁ W₂ : Subgroup G) :
    cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ ⊆ CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂ := by
  intro v hv
  rw [CFSG.FeitThompson.Prep06.dadeA0_eq]
  right
  refine CFSG.FeitThompson.Proofs.mem_mixedConj.2 ⟨1, M.one_mem, v, ?_, by group⟩
  obtain ⟨h1, h2, h3⟩ := mem_cyclicTIDiff.1 hv
  exact mem_cyclicTIset.2 ⟨h1, h2, h3⟩

theorem isCoprimePowerStable_dadeA0 {G : Type*} [Group G] [Finite G] (M W₁ W₂ : Subgroup G) :
    IsCoprimePowerStable (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) := by
  rw [isCoprimePowerStable_iff]
  intro m hm1 hm a ha
  obtain ⟨b, -, -, hb⟩ := exists_coprime_pow_pow_eq_self (G := G) hm1 hm
  rw [CFSG.FeitThompson.Prep06.dadeA0_eq] at ha ⊢
  rcases ha with ⟨haK, ha1⟩ | ha
  · left
    refine ⟨Subgroup.pow_mem _ haK m, fun h1 => ha1 ?_⟩
    rw [Set.mem_singleton_iff] at h1 ⊢
    have := hb a
    rw [h1, one_pow] at this
    exact this.symm
  · right
    obtain ⟨g, hg, v, hv, rfl⟩ := CFSG.FeitThompson.Proofs.mem_mixedConj.1 ha
    refine CFSG.FeitThompson.Proofs.mem_mixedConj.2 ⟨g, hg, v ^ m, ?_, ?_⟩
    · obtain ⟨hvW, hv1, hv2⟩ := mem_cyclicTIset.1 hv
      refine mem_cyclicTIset.2 ⟨Subgroup.pow_mem _ hvW m, fun h => hv1 ?_, fun h => hv2 ?_⟩
      · rw [← hb v]; exact Subgroup.pow_mem _ h b
      · rw [← hb v]; exact Subgroup.pow_mem _ h b
    · have := conj_pow (a := g⁻¹) (b := v) (i := m)
      rw [inv_inv] at this
      exact this.symm

theorem powOp_mem_indFamKer {G : Type*} [Group G] [Fintype G] {M : Subgroup G}
    {K A : Subgroup ↥M} {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G)) {f : ↥M → ℂ}
    (hf : f ∈ CFSG.FeitThompson.Prep06.indFamKer M K A) :
    powOp k f ∈ CFSG.FeitThompson.Prep06.indFamKer M K A := by
  classical
  rw [CFSG.FeitThompson.Prep06.indFamKer_eq, mem_indFam] at hf ⊢
  obtain ⟨θ, ⟨hθ, hker⟩, rfl⟩ := hf
  obtain ⟨hirr, hne⟩ := mem_nonprincipalIrr.1 hθ
  have hMdvd : Nat.card ↥M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  have hKdvd : Nat.card ↥K ∣ Nat.card G :=
    (Subgroup.card_subgroup_dvd_card K).trans hMdvd
  have hkK : k.Coprime (Nat.card ↥K) := hk.coprime_dvd_right hKdvd
  obtain ⟨b, -, hkb⟩ := exists_one_le_mul_modEq_one (G := ↥K) hk1 hkK
  refine ⟨powOp k θ, ⟨mem_nonprincipalIrr.2 ⟨powOp_mem_Irr hk1 hkK hirr, ?_⟩, ?_⟩, ?_⟩
  · intro h1
    apply hne
    have := powOp_powOp_eq_self (G := ↥K) hkb θ
    rw [h1] at this
    rw [← this]
    funext x
    simp [powOp_apply]
  · intro x hx
    rw [powOp_apply, powOp_apply, one_pow]
    exact hker (x ^ k) (by simpa using Subgroup.pow_mem A hx k)
  · exact (powOp_indClassFun K (hk.coprime_dvd_right hMdvd).symm θ).symm

open scoped Classical in
theorem indFamDetectKer_subset_indFam_sdiff {G : Type*} [Group G] [Fintype G] {M : Subgroup G}
    {K C H : Subgroup ↥M} :
    CFSG.FeitThompson.Prep06.indFamDetectKer M K C H ⊆ indFam K (Irr ↥K \ {1}) := by
  rw [CFSG.FeitThompson.Prep06.indFamDetectKer_eq]
  refine indFam_mono K ?_
  rintro θ ⟨hθ, -, x, -, hx⟩
  refine ⟨by rw [Irr_eq_irrChar]; exact hθ, fun h1 => hx ?_⟩
  rw [Set.mem_singleton_iff] at h1
  subst h1
  rfl

open scoped Classical in
theorem isCoherent_of_hasCoherentMap {G : Type*} [Group G] [Fintype G] {M W₁ W₂ : Subgroup G}
    {S : Set (↥M → ℂ)} {τ : charSpanZero S →+ virtualChars G}
    (hτ : ∀ f : charSpanZero S, ((τ f : virtualChars G) : G → ℂ)
      = dadeMapFun M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) (CFSG.FeitThompson.Prep06.dadeT M) (f : ↥M → ℂ))
    (h : CFSG.FeitThompson.Prep06.HasCoherentMap M W₁ W₂ S) : IsCoherent S τ := by
  obtain ⟨ν, hiso, heq⟩ := CFSG.FeitThompson.Prep06.hasCoherentMap_iff.1 h
  refine isCoherent_iff.2 ⟨ν, ⟨hiso, fun f => Subtype.ext ?_⟩⟩
  rw [hτ f, ← CFSG.FeitThompson.Prep06.dadeTau_eq]
  exact heq _ (charSpanZero_apply_one f)

theorem cfInner_dadeMap_powOp_prodCharEta_eq {G : Type*} [Group G] [Fintype G]
    {W W1 W2 : Subgroup G} {ω : classFun ↥W →ₗ[ℂ] classFun G}
    {L : Subgroup G} {A0 : Set G} {T : G → Subgroup G}
    (hD : IsDadeData L A0 T) (hA : IsCoprimePowerStable A0) {F : ↥L → ℂ}
    (hF : F ∈ dadeDomain L A0) {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    (hW : IsCyclicTIPair W W1 W2) (i : Irr ↥W1) (j : Irr ↥W2)
    (hinv : ∀ b : ℕ, 1 ≤ b → b.Coprime (Nat.card G) → ∀ hb : powOp b F - F ∈ dadeDomain L A0,
      cfInner ((dadeMap hD ⟨powOp b F - F, hb⟩ : classFun G) : G → ℂ) (hW.prodCharEta ω i j) = 0) :
    cfInner ((dadeMap hD ⟨F, hF⟩ : classFun G) : G → ℂ) (powOp k (hW.prodCharEta ω i j))
      = cfInner ((dadeMap hD ⟨F, hF⟩ : classFun G) : G → ℂ) (hW.prodCharEta ω i j) := by
  obtain ⟨b, hb1, hbcop, hb⟩ := exists_coprime_pow_pow_eq_self (G := G) hk1 hk
  set ψ : G → ℂ := ((dadeMap hD ⟨F, hF⟩ : classFun G) : G → ℂ) with hψ
  have hkb : powOp k (powOp b ψ) = ψ := by
    funext x; simp only [powOp_apply, hb x]
  have h1 : cfInner ψ (powOp k (hW.prodCharEta ω i j))
      = cfInner (powOp b ψ) (hW.prodCharEta ω i j) := by
    conv_lhs => rw [← hkb]
    exact cfInner_powOp_powOp hk _ _
  have hPb := dadeMap_powOp hD hA hb1 hbcop ⟨F, hF⟩
  have hdom : powOp b F - F ∈ dadeDomain L A0 :=
    Submodule.sub_mem _ (powOp_mem_dadeDomain hA hb1 hbcop hF) hF
  have hsub : ((dadeMap hD ⟨powOp b F - F, hdom⟩ : classFun G) : G → ℂ) = powOp b ψ - ψ := by
    have : (⟨powOp b F - F, hdom⟩ : dadeDomain L A0)
        = ⟨powOp b F, powOp_mem_dadeDomain hA hb1 hbcop hF⟩ - ⟨F, hF⟩ := rfl
    rw [this, map_sub, Submodule.coe_sub, hPb]
  have h2 := hinv b hb1 hbcop hdom
  rw [hsub, cfInner_sub_left, sub_eq_zero] at h2
  rw [h1, h2]

theorem isCoherent_union_of_isOrthogonal_prodCharEtaColSum {G : Type*} [Group G] [Fintype G]
    {L : Subgroup G} [Fintype ↥L] {K X₁ X₂ : Subgroup ↥L} [K.Normal]
    [Fintype ↥(X₁ ⊔ X₂)] [Fintype ↑(Irr ↥X₁)] {h : IsPrimeCyclicTIHyp K X₁ X₂}
    {σ : classFun ↥(X₁ ⊔ X₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n : ℤ} {A₀ : Set G}
    {T : G → Subgroup G} {S₁ S₂ : Set (↥L → ℂ)} {τ₁ : charSpanZero S₁ →+ virtualChars G}
    {τ₂ : charSpanZero S₂ →+ virtualChars G} {τU : charSpanZero (S₁ ∪ S₂) →+ virtualChars G}
    {Wamb V₁ V₂ : Subgroup G} [Fintype ↥Wamb] {ωa : classFun ↥Wamb →ₗ[ℂ] classFun G}
    (hmapW : (X₁ ⊔ X₂).map L.subtype = Wamb) (hmap1 : X₁.map L.subtype = V₁)
    (hmap2 : X₂.map L.subtype = V₂)
    (hodd : Odd (Nat.card G)) (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K X₁ X₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)
      = cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)}
      = (((X₁ ⊔ X₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (X₁ ⊔ X₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype)
        ∩ cyclicTIDiff ((X₁ ⊔ X₂).map L.subtype) (X₁.map L.subtype) (X₂.map L.subtype) = ∅)
    (hWpair : IsCyclicTIPair Wamb V₁ V₂) (hωa : IsCyclicTIIsometry Wamb V₁ V₂ ωa)
    (hprime₁ : (Nat.card ↥X₁).Prime) (hprime₂ : (Nat.card ↥X₂).Prime)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁)
    (hncard : (S₁.ncard : ℤ) = n) (hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥X₁ : ℂ))
    (hS₂ : S₂ ⊆ indFam K (Irr ↥K \ {1}))
    (hS₂star : ∀ χ ∈ S₂, star χ ∈ S₂) (hS₁S₂ : Disjoint S₁ S₂)
    (hrows : ∀ j : Irr ↥X₂, j ≠ principalIrr ↥X₂ → h.primeTIrow σ j ∈ S₂)
    (hτ₁ : ∀ (f : charSpanZero S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₁ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτ₂ : ∀ (f : charSpanZero S₂) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τ₂ f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hτU : ∀ (f : charSpanZero (S₁ ∪ S₂)) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      ((τU f : virtualChars G) : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hcoh₁ : IsCoherent S₁ τ₁) (hcoh₂ : IsCoherent S₂ τ₂)
    (hF : h.primeTIrow σ (principalIrr ↥X₂) - ζ ∈ dadeDomain L A₀)
    (hproj : ∀ (i : Irr ↥V₁) (l : Irr ↥V₂),
      IsOrthogonal (((dadeMap hD ⟨h.primeTIrow σ (principalIrr ↥X₂) - ζ, hF⟩ : classFun G) : G → ℂ)
          - hWpair.prodCharEtaColSum ωa (principalIrr ↥V₂))
        (hWpair.prodCharEta ωa i l)) :
    IsCoherent (S₁ ∪ S₂) τU := by
  subst hmapW hmap1 hmap2
  refine PrimeDadeColumnGluing.isCoherent_union hodd hB hA hD hstab hdisj hωa hprime₁ hprime₂
    hS₁ hS₁star hζS₁ hncard hdeg hS₂ hS₂star hS₁S₂ hrows hτ₁ hτ₂ hτU hcoh₁ hcoh₂ ?_
  intro i l
  rw [PrimeDadeLowFamily.tauPrincipalRowSub_eq_dadeMap hB hA hD ⟨_, hF⟩ rfl]
  exact hproj i l

set_option maxHeartbeats 1000000 in
open scoped Classical in
theorem exists_isUniformBridgeData_of_isRowSetup
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {σ w l δ μ}
    (hrow : CFSG.FeitThompson.Prep06.IsRowSetup M W₁ W₂ σ w l δ μ)
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (h : IsPrimeCyclicTIHyp (CFSG.FeitThompson.Prep06.derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    (hrowsum : ∀ j, (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j) = h.primeTIrow σ j)
    (hδ : ∀ j, δ j = h.primeTISign σ j) (hμ : ∀ i j, μ i j = h.primeTIirr σ i j)
    {ζ : ↥M → ℂ}
    (hζind : ζ ∈ indFam (CFSG.FeitThompson.Prep06.derivedOf M)
      (Irr ↥(CFSG.FeitThompson.Prep06.derivedOf M) \ {1}))
    (hζIrr : ζ ∈ Irr ↥M)
    (hζ1 : ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ))
    (hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁) :
    ∃ d n : ℤ, h.IsUniformBridgeData σ ζ d n 1 ∧
      (∀ j, j ≠ principalIrr ↥(W₂.subgroupOf M) →
        h.primeTIrow σ j ∈ CFSG.FeitThompson.Prep06.indFamDetectKer M (CFSG.FeitThompson.Prep06.derivedOf M)
          ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).subgroupOf M)
          ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M)) ∧
      (n : ℤ) = (Nat.card (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M)) : ℤ) := by
  obtain ⟨d, n, dsign, -, hd1, -, -, hn2, hdeg, hsign, hdn⟩ :=
    (CFSG.FeitThompson.Proofs.FPF_type_iii_v_local_character_constants h₅ G hG M U W₁ W₂ hM
      (by tauto) hc).2.2 σ w l δ μ hrow
  obtain ⟨hrd, -, -, hdu, hds, hnq⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_row_degree_and_kernel h₁ h₅ G hG M U W₁ W₂ hM htype hc
      σ w l δ μ hrow d n dsign hdeg hsign hdn
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, n₁, hn₁card, -, -, hn₁q⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_two_coherent_layers h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂
      hM htype hc _ rfl _ _ rfl rfl
  have hq0 : 0 < Nat.card ↥W₁ := Nat.card_pos
  have hnn : n₁ = n := by
    have : n₁ * Nat.card ↥W₁ = n * Nat.card ↥W₁ := by rw [hn₁q, hnq]
    exact Nat.eq_of_mul_eq_mul_right hq0 this
  refine ⟨d, n, ?_, ?_, ?_⟩
  · refine ⟨hrow.isometry, hζind, hζIrr, hζ1, by exact_mod_cast hd1, by exact_mod_cast hn2,
      Or.inl rfl, ?_, ?_, ?_⟩
    · intro i j hj; rw [← hμ]; exact hdeg i j hj
    · intro j hj; rw [← hδ, hsign j hj, hds]; simp
    · rw [hcard1]
      have : d - 1 = n * Nat.card ↥W₁ := by omega
      omega
  · intro j hj
    obtain ⟨hIrrK, hkerC, hdetH, -, hind, -, -⟩ := hrd j hj
    rw [← hrowsum j, hind, CFSG.FeitThompson.Prep06.indFamDetectKer_eq, mem_indFam]
    refine ⟨_, ⟨?_, hkerC, hdetH⟩, indClassFun_inst _ _ _ _⟩
    rw [← Irr_eq_irrChar]; exact hIrrK
  · rw [hn₁card, hnn]

set_option maxHeartbeats 1000000 in
open scoped Classical in
private theorem not_forall_isOrthogonal_sub_prodCharEtaColSum
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    [Fintype ↑(Irr ↥(W₁.subgroupOf M))]
    (h : IsPrimeCyclicTIHyp (CFSG.FeitThompson.Prep06.derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {σ : classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M) →ₗ[ℂ] classFun ↥M}
    {ζ : ↥M → ℂ} {d n : ℤ} (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hrows : ∀ j, j ≠ principalIrr ↥(W₂.subgroupOf M) →
        h.primeTIrow σ j ∈ CFSG.FeitThompson.Prep06.indFamDetectKer M (CFSG.FeitThompson.Prep06.derivedOf M)
          ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).subgroupOf M)
          ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M))
    (hncard : (n : ℤ) = (Nat.card (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M)) : ℤ))
    (hζ : ζ ∈ CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M))
    (hD : IsDadeData M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) (CFSG.FeitThompson.Prep06.dadeT M))
    (hF : h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ
      ∈ dadeDomain M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂))
    {ω : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun G} (hω : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ ω)
    (hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    (hproj : ∀ (i : Irr ↥W₁) (l : Irr ↥W₂),
      IsOrthogonal (((dadeMap hD ⟨_, hF⟩ : classFun G) : G → ℂ)
          - hWpair.prodCharEtaColSum ω (principalIrr ↥W₂))
        (hWpair.prodCharEta ω i l)) : False := by
  have hfin : Finite G := Finite.of_fintype G
  have hodd := hG.odd
  have hKn : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := h.normal
  set S₁ := CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M) with hS₁def
  set S₂ := CFSG.FeitThompson.Prep06.indFamDetectKer M (CFSG.FeitThompson.Prep06.derivedOf M)
          ((U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).subgroupOf M)
          ((CFSG.FeitThompson.Prep06.hallCoreIn M).subgroupOf M) with hS₂def
  obtain ⟨-, -, -, hdisj12, hS₁star, hS₂star, -, hcoh₁, hcoh₂, hnot, hS₁Irr, hS₁deg, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_two_coherent_layers h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂
      hM htype hc _ rfl S₁ S₂ rfl rfl
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hcard2 : Nat.card ↥(W₂.subgroupOf M) = Nat.card ↥W₂ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₂
  have hS₁ind : S₁ ⊆ indFam (CFSG.FeitThompson.Prep06.derivedOf M)
      (Irr ↥(CFSG.FeitThompson.Prep06.derivedOf M) \ {1}) := by
    intro f hf
    have := CFSG.FeitThompson.Prep06.indFamKer_subset_indFamNonprincipal M _ _ hf
    rwa [indFamNonprincipal_eq_indFam_sdiff] at this
  have hS₂ind : S₂ ⊆ indFam (CFSG.FeitThompson.Prep06.derivedOf M)
      (Irr ↥(CFSG.FeitThompson.Prep06.derivedOf M) \ {1}) := indFamDetectKer_subset_indFam_sdiff
  have hA := CrossedRowData.image_primeTIbridgeSupport_subset_dadeA0 hc
  have hAb := PrimeDadeColumnGluing.image_bridgeSupport_subset hA
  have hqprime : (Nat.card ↥W₁).Prime := by
    rcases htype with hT | hT
    · exact (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
    · exact (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
  have hpprime : (Nat.card ↥W₂).Prime := h₅ G hG M U W₁ W₂ hM (by tauto) hc
  let τ₁ := TypeVTwoFamilyJoining.subDadeHom (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
    hD hS₁ind hAb
  let τ₂ := TypeVTwoFamilyJoining.subDadeHom (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
    hD hS₂ind hAb
  let τU := TypeVTwoFamilyJoining.subDadeHom (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
    hD (Set.union_subset hS₁ind hS₂ind) hAb
  have hU := isCoherent_union_of_isOrthogonal_prodCharEtaColSum (τ₁ := τ₁) (τ₂ := τ₂) (τU := τU)
    (CrossedRowData.map_subtype_subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂)
    (Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₁) (Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₂)
    hodd hB hA hD (CrossedRowData.setOf_conj_eq_of_isWitnessedPConfiguration hc)
    (CrossedRowData.inter_eq_empty_of_isWitnessedPConfiguration hc) hWpair hω
    (hcard1 ▸ hqprime) (hcard2 ▸ hpprime) (fun χ hχ => ⟨hS₁ind hχ, hS₁Irr hχ⟩) hS₁star hζ
    (by rw [hncard, Nat.card_coe_set_eq])
    (fun χ hχ => by rw [hcard1]; exact hS₁deg χ hχ) hS₂ind hS₂star hdisj12 hrows
    (fun f F hfF => TypeVTwoFamilyJoining.coe_subDadeHom hD hS₁ind hAb f F hfF.symm)
    (fun f F hfF => TypeVTwoFamilyJoining.coe_subDadeHom hD hS₂ind hAb f F hfF.symm)
    (fun f F hfF => TypeVTwoFamilyJoining.coe_subDadeHom hD _ hAb f F hfF.symm)
    (isCoherent_of_hasCoherentMap
      (TypeVTwoFamilyJoining.coe_subDadeHom_eq_dadeMapFun hD hS₁ind hAb) hcoh₁)
    (isCoherent_of_hasCoherentMap
      (TypeVTwoFamilyJoining.coe_subDadeHom_eq_dadeMapFun hD hS₂ind hAb) hcoh₂)
    hF hproj
  exact hnot (hasCoherentMap_of_isCoherent
    (TypeVTwoFamilyJoining.coe_subDadeHom_eq_dadeMapFun hD _ hAb) hU)

set_option maxHeartbeats 1000000 in
open scoped Classical in
private theorem principalRowProjection_of_mem
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u})
    {G : Type u} [Group G] [Fintype G] (hG : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G)
    {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {σ w l δ μ}
    (hrow : CFSG.FeitThompson.Prep06.IsRowSetup M W₁ W₂ σ w l δ μ) {ω wG η}
    (heta : CFSG.FeitThompson.Prep06.IsEtaSetup W₁ W₂ ω wG η) {ζ : ↥M → ℂ}
    (hζ : ζ ∈ CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M)) :
    (∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)),
        cfInner (CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂
            ((∑ᶠ i' : ↑(Irr ↥(W₁.subgroupOf M)), μ i' (principalIrr ↥(W₂.subgroupOf M))) - ζ)
          - ∑ᶠ j' : ↑(Irr ↥W₂), η (principalIrr ↥W₁) j') (η i j) = 0) ∧
      Nat.card W₂ ≤ Nat.card W₁ := by
  have hfin : Finite G := Finite.of_fintype G
  have hodd := hG.odd
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn : (CFSG.FeitThompson.Prep06.derivedOf M).Normal := h.normal
  have hσ := hrow.isometry
  have hδ : ∀ j, δ j = h.primeTISign σ j := by
    intro j
    refine (h.existsUnique_primeTISign hσ j).unique ⟨hrow.sign j, ?_⟩
      ⟨h.primeTISign_eq_one_or_eq_neg_one j, ?_⟩
    · rw [← rowData_w_eq h hrow.toIsRowData]
      exact hrow.mu_zero_mem j
    · exact h.primeTIirr_principal_left (σ := σ) j ▸
        h.primeTIirr_principal_left_mem_Irr hσ j
  have hμ : ∀ i j, μ i j = h.primeTIirr σ i j := by
    intro i j
    rw [hrow.mu_eq i j, rowData_l_eq h hrow.toIsRowData i,
      rowData_w_eq h hrow.toIsRowData, hδ j, h.primeTIirr_eq_mul i j,
      h.primeTIirr_principal_left]
  have hrowsum : ∀ j, (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), μ i j) = h.primeTIrow σ j := by
    intro j
    rw [finsum_eq_sum_of_fintype, h.primeTIrow_def]
    exact Finset.sum_congr rfl fun i _ => hμ i j
  have hWpair : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := CrossedRowData.isCyclicTIPair_sup hodd hc
  have hηeq : ∀ i j, η i j = hWpair.prodCharEta ω i j :=
    CrossedRowData.eta_eq_prodCharEta hWpair heta
  have hR0 : (∑ᶠ j' : ↑(Irr ↥W₂), η (principalIrr ↥W₁) j')
      = ∑ j : ↑(Irr ↥W₂), hWpair.prodCharEta ω (principalIrr ↥W₁) j := by
    rw [finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun j _ => hηeq _ j
  have hω := heta.isometry
  obtain ⟨-, -, -, hD, -⟩ := h₃ G hG M U W₁ W₂ hM (by tauto) hc
  have hA := CrossedRowData.image_primeTIbridgeSupport_subset_dadeA0 hc
  have hA0 : ∀ x ∈ CFSG.FeitThompson.Prep06.derivedOf M, x ≠ 1 →
      (x : G) ∈ CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂ := fun x hx hx1 =>
    hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hx hx1, rfl⟩
  set S₁ := CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M) with hS₁def
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hS₁ind : S₁ ⊆ indFam (CFSG.FeitThompson.Prep06.derivedOf M)
      (Irr ↥(CFSG.FeitThompson.Prep06.derivedOf M) \ {1}) := by
    intro f hf
    have := CFSG.FeitThompson.Prep06.indFamKer_subset_indFamNonprincipal M _ _ hf
    rwa [indFamNonprincipal_eq_indFam_sdiff] at this
  obtain ⟨hS₁Irr, hS₁deg⟩ := layer_one_subset_Irr h₂ hG hM htype hc
  have hζind := hS₁ind hζ
  have hζIrr : ζ ∈ Irr ↥M := hS₁Irr hζ
  have hζ1 : ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ) := by rw [hcard1]; exact hS₁deg ζ hζ
  have hqprime : (Nat.card ↥W₁).Prime := by
    rcases htype with hT | hT
    · exact (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
    · exact (hT.clauses_of_isWitnessedPConfiguration_of_minimalSimple hG.simple hG.nonabelian
        hG.odd hG.solvable hM hc).1.prime_natCard_W₁
  have hpprime : (Nat.card ↥W₂).Prime := h₅ G hG M U W₁ W₂ hM (by tauto) hc
  have hζne1 : ζ 1 ≠ 1 := by
    rw [hζ1, hcard1]; exact_mod_cast hqprime.one_lt.ne'
  have hF : h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ
      ∈ dadeDomain M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂) :=
    mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_Irr (h.primeTIrow_sub_mem_span_Irr hσ hζind),
      fun x hx => h.primeTIrow_sub_apply_eq_zero hσ hζind hζ1 fun hmem => hx (hA0 x hmem.1 hmem.2)⟩
  obtain ⟨ν, hνiso, hνtau⟩ := hasCoherentMap_layer_one h₂ h₃ h₄ hG hM htype hc
  have hντ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain M (CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂)),
      (f : ↥M → ℂ) = (F : ↥M → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ) := by
    intro f F hfF
    have hF1 : (F : ↥M → ℂ) 1 = 0 := by
      refine (mem_dadeDomain.1 F.2).2 1 ?_
      intro hh
      have h5 := hD.subset_sdiff hh
      simp at h5
    rw [hνtau f (hfF ▸ hF1), coe_dadeMap, ← hfF, CFSG.FeitThompson.Prep06.dadeTau_eq]
  have hSdet : S₁ ⊆ indFamDetect (CFSG.FeitThompson.Prep06.derivedOf M)
      ((CFSG.FeitThompson.Prep06.derivedOf M).subgroupOf (CFSG.FeitThompson.Prep06.derivedOf M)) := by
    rw [PrimeFixedTIPGroupCoherence.indFamDetect_self_eq_indFam_sdiff]; exact hS₁ind
  have hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁ := fun χ hχ => star_mem_indFamKer hχ
  have hS0 : ∀ (f : charSpanZero S₁) (x : ↥M), (x : G) ∉ CFSG.FeitThompson.Prep06.dadeA0 M W₁ W₂ →
      (f : ↥M → ℂ) x = 0 := fun f x hx =>
    (mem_dadeDomain.1 (PrimeDadePivot.mem_dadeDomain_of_mem_span_indFam hA0
      (hS₁ind.trans (indFam_mono _ Set.sdiff_subset)) (mem_charSpanZero.1 f.2).1
      (mem_charSpanZero.1 f.2).2)).2 x hx
  have hW2K : W₂ ≤ (CFSG.FeitThompson.Prep06.derivedOf M).map M.subtype := by
    rw [CFSG.FeitThompson.Prep06.map_subtype_derivedOf]
    exact hc.le_commutator_commutator_W₂.trans (Subgroup.commutator_le_self _)
  have hW1K : W₁ ⊓ (CFSG.FeitThompson.Prep06.derivedOf M).map M.subtype = ⊥ := by
    rw [CFSG.FeitThompson.Prep06.map_subtype_derivedOf, inf_comm]
    exact disjoint_iff.1 hc.disjoint_commutator_W₁
  set ψ : G → ℂ := ((dadeMap hD ⟨_, hF⟩ : classFun G) : G → ℂ) with hψdef
  have hψspan : ψ ∈ Submodule.span ℤ (Irr G) :=
    hD.dadeMap_mem_span_Irr hF (h.primeTIrow_sub_mem_span_Irr hσ hζind)
  have hnorm : cfInner ψ ψ = (Nat.card ↥W₁ : ℂ) + 1 := by
    rw [hψdef, cfInner_dadeMap hD]
    change cfInner (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ)
      (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ) = _
    have h0 := PrimeDadeAxis.cfInner_primeTIrow_principal_eq_zero h hσ hζIrr hζne1
    have h0' : cfInner ζ (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M))) = 0 := by
      rw [← conj_cfInner, h0, map_zero]
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, h0, h0',
      h.cfInner_self_primeTIrow hσ, cfInner_eq_ite_of_mem_Irr hζIrr hζIrr, if_pos rfl, hcard1]
    ring
  have hV : ∀ v ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂, ψ v = 0 := by
    intro v hv
    have hvA := cyclicTIDiff_subset_dadeA0 M W₁ W₂ hv
    rw [hψdef, dadeMap_apply_mem hD _ hvA]
    refine h.primeTIrow_sub_apply_eq_zero hσ hζind hζ1 fun hmem => ?_
    exact notMem_map_of_mem_cyclicTIDiff hWpair hW2K hW1K hv ⟨_, hmem.1, rfl⟩
  have h00 : cfInner ψ (hWpair.prodCharEta ω (principalIrr ↥W₁) (principalIrr ↥W₂)) = 1 := by
    rw [hWpair.prodCharEta_principal hω, hψdef, NormalInducedFamily.cfInner_dadeMap_one hD]
    change cfInner (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ) 1 = 1
    rw [h.primeTIrow_principal hσ]
    exact NormalInducedFamily.cfInner_indClassFun_one_sub_one hζind
  have hpow : ∀ k : ℕ, 1 ≤ k → k.Coprime (Nat.card G) → ∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)),
      cfInner ψ (powOp k (hWpair.prodCharEta ω i j)) = cfInner ψ (hWpair.prodCharEta ω i j) := by
    intro k hk1 hk i j
    refine cfInner_dadeMap_powOp_prodCharEta_eq hD (isCoprimePowerStable_dadeA0 M W₁ W₂) hF hk1 hk
      hWpair i j ?_
    intro b hb1 hbcop hb
    have hcopM : (Nat.card ↥M).Coprime b :=
      (hbcop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card M)).symm
    have hM0 : powOp b (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)))
        = h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) := by
      rw [h.primeTIrow_principal hσ, powOp_indClassFun _ hcopM]
      congr 1
      funext x; simp [powOp_apply]
    have hζ' := powOp_mem_indFamKer hb1 hbcop hζ
    have heqF : powOp b (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ)
        - (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ) = ζ - powOp b ζ := by
      rw [powOp_sub, hM0]; abel
    have hmem : ζ - powOp b ζ ∈ Submodule.span ℤ S₁ :=
      Submodule.sub_mem _ (Submodule.subset_span hζ) (Submodule.subset_span hζ')
    have hval := hντ ⟨_, hmem⟩ ⟨_, hb⟩ heqF.symm
    rw [← hval]
    have hsplit : (⟨ζ - powOp b ζ, hmem⟩ : Submodule.span ℤ S₁)
        = ⟨ζ, Submodule.subset_span hζ⟩ - ⟨powOp b ζ, Submodule.subset_span hζ'⟩ := rfl
    rw [hsplit, map_sub, Submodule.coe_sub, cfInner_sub_left,
      isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hWpair hW2K hW1K hω hD
        (cyclicTIDiff_subset_dadeA0 M W₁ W₂) hSdet hS₁star hνiso hS0 hντ hζ hζIrr i j),
      isOrthogonal_iff.1 (CoherentCore.isOrthogonal_nu_prodCharEta hodd hWpair hW2K hW1K hω hD
        (cyclicTIDiff_subset_dadeA0 M W₁ W₂) hSdet hS₁star hνiso hS0 hντ hζ' (hS₁Irr hζ') i j),
      sub_zero]
  obtain ⟨hdich, -, -, horth⟩ := PrimeDadeAxis.axis_projection_dadeMap hodd hWpair hW2K hW1K hω hD
    (cyclicTIDiff_subset_dadeA0 M W₁ W₂) hSdet hS₁star hνiso hS0 hντ hζ hζIrr h hσ hζne1 hF rfl
    hψspan hnorm hV h00 hqprime hpprime hpow
  rcases hdich with hcol | ⟨hrowX, hle⟩
  ·
    exfalso
    obtain ⟨d, n, hB, hrows, hncard⟩ := exists_isUniformBridgeData_of_isRowSetup h₁ h₂ h₃ h₄ h₅
      hG hM htype hc hrow h hrowsum hδ hμ hζind hζIrr hζ1 hcard1
    refine not_forall_isOrthogonal_sub_prodCharEtaColSum h₁ h₂ h₃ h₄ h₅ hG hM htype hc h hB
      hrows hncard hζ hD hF hω hWpair fun i l => ?_
    have := horth i l
    rwa [hcol] at this
  · refine ⟨fun i j => ?_, hle⟩
    have hτ : CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂
        ((∑ᶠ i' : ↑(Irr ↥(W₁.subgroupOf M)), μ i' (principalIrr ↥(W₂.subgroupOf M))) - ζ) = ψ := by
      rw [hrowsum, CFSG.FeitThompson.Prep06.dadeTau_eq, hψdef, coe_dadeMap]
    rw [hτ, hR0, hηeq i j, ← hrowX]
    exact isOrthogonal_iff.1 (horth i j)

open scoped Classical in
private theorem principalRowProjection_residual
    (_h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (_h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (_h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (_h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (_h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    ∀ (G : Type u) [Group G] [Fintype G], CFSG.FeitThompson.Prep06.IsMinimalOddSimple G →
      ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
        IsWitnessedPConfiguration M U W₁ W₂ →
        ∀ σ w l δ μ, CFSG.FeitThompson.Prep06.IsRowSetup M W₁ W₂ σ w l δ μ →
        ∀ ω wG η, CFSG.FeitThompson.Prep06.IsEtaSetup W₁ W₂ ω wG η →
        (∀ ζ ∈ CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
            (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
              (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
                : Subgroup G)).subgroupOf M),
          ∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)),
            cfInner (CFSG.FeitThompson.Prep06.dadeTau M W₁ W₂
                ((∑ᶠ i' : ↑(Irr ↥(W₁.subgroupOf M)), μ i' (principalIrr ↥(W₂.subgroupOf M))) - ζ)
              - ∑ᶠ j' : ↑(Irr ↥W₂), η (principalIrr ↥W₁) j') (η i j) = 0) ∧
          Nat.card W₂ ≤ Nat.card W₁ := by
  intro G _ _ hG M U W₁ W₂ hM htype hc σ w l δ μ hrow ω wG η heta
  refine ⟨fun ζ hζ => (principalRowProjection_of_mem _h₁ _h₂ _h₃ _h₄ _h₅ hG hM htype hc hrow
    heta hζ).1, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, n, hncard, -, hn2, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_two_coherent_layers _h₁ _h₂ _h₃ _h₄ _h₅ G hG M U W₁ W₂
      hM htype hc _ rfl _ _ rfl rfl
  obtain ⟨ζ, hζ⟩ : (CFSG.FeitThompson.Prep06.indFamKer M (CFSG.FeitThompson.Prep06.derivedOf M)
      (((CFSG.FeitThompson.Prep06.hallCoreIn M ⊔
        (U ⊓ centralizer ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G))
          : Subgroup G)).subgroupOf M)).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hncard
    simp at hncard
    omega
  exact (principalRowProjection_of_mem _h₁ _h₂ _h₃ _h₄ _h₅ hG hM htype hc hrow heta hζ).2

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05

universe u

open scoped Classical in
theorem FPF_type_iii_iv_principal_row_projection
    (h₁ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_principal_row_projection.{u} := by
  classical
  intro G _ _ hG M U W₁ W₂ hM htype hc σ w l δ μ hrow ω wG η heta
  have hfin : Finite G := Finite.of_fintype G
  have hG5 : IsMinimalSimpleOdd G := isMinimalSimpleOdd_of_isMinimalOddSimple hG
  obtain ⟨hproj, hle⟩ := principalRowProjection_residual h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂ hM htype hc
    σ w l δ μ hrow ω wG η heta
  exact ⟨hproj, lt_of_le_of_ne hle (natCard_W₂_ne_natCard_W₁_of_isTypeIII_or_isTypeIV h₅ hG5 hM htype hc)⟩

end CFSG.FeitThompson.Proofs

end
