module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Representations.IndexCollapseSupport
import CFSG.FeitThompson.Representations.TypeIIIToVCoherenceFrobeniusPartner
import CFSG.FeitThompson.Representations.DadeBetaProjectionIntegralParameter
import CFSG.FeitThompson.Representations.ExteriorImageProportionalCentralCoefficients
public import CFSG.FeitThompson.Representations.TIRectangleCoefficientExchange

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

universe u

theorem dvd_relIndex_centralizer_of_le {G : Type*} [Group G] {U E H : Subgroup G} (hEH : E ≤ H) :
    (U ⊓ centralizer (E : Set G)).relIndex U ∣ (U ⊓ centralizer (H : Set G)).relIndex U :=
  relIndex_dvd_of_le_left U (inf_le_inf_left U (centralizer_le hEH))

theorem eq_of_dvd_of_mul_int_eq_one_or_neg_one {a u : ℕ} (hdvd : a ∣ u) {k : ℤ}
    (hk : ((u / a : ℕ) : ℤ) * k = 1 ∨ ((u / a : ℕ) : ℤ) * k = -1) : u = a := by
  have h1 : ((u / a : ℕ) : ℤ) ∣ 1 := by
    rcases hk with hk | hk
    · exact Dvd.intro k hk
    · exact dvd_neg.mp (Dvd.intro k hk)
  have hc : u / a = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp h1)
  rw [← Nat.div_mul_cancel hdvd, hc, one_mul]

set_option maxHeartbeats 4000000 in
open scoped Classical in
private theorem indexCollapse_residual
    (h₁ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : CFSG.FeitThompson.Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : CFSG.FeitThompson.Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : CFSG.FeitThompson.Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : CFSG.FeitThompson.Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    ∀ (G : Type u) [Group G] [Fintype G], IsMinimalOddSimple G →
      ∀ M U W₁ W₂ : Subgroup G, IsCoatom M → (IsTypeIII M ∨ IsTypeIV M) →
        IsWitnessedPConfiguration M U W₁ W₂ →
        ∀ E : Fin (Nat.card W₁) → Subgroup G, ∀ a : ℕ, ∀ b : G,
          (∀ i, E i ≤ Prep06.hallCoreIn M) →
          (∀ i, Nat.card (E i) = Nat.card W₂) →
          (⨆ i, E i) = Prep06.hallCoreIn M →
          (∀ i, E i ⊓ (⨆ j ∈ ({i}ᶜ : Set (Fin (Nat.card W₁))), E j) = ⊥) →
          (∀ i, U ≤ normalizer ((E i : Subgroup G) : Set G)) →
          (b ∈ W₁ ∧ zpowers b = W₁) →
          (∀ i : Fin (Nat.card W₁),
            Subgroup.map (MulAut.conj b⁻¹ : G ≃* G) (E i) = E (i + 1)) →
          (∀ (i : Fin (Nat.card W₁)) (x : G), x ∈ U → ∃ m : ℕ,
            ∀ y ∈ E i, x⁻¹ * y * x = y ^ m) →
          1 < a →
          (∀ i, (U ⊓ centralizer ((E i : Subgroup G) : Set G)).relIndex U = a) →
          ∃ k : ℤ,
            (((U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G)).relIndex U / a : ℕ) : ℤ)
                * k = 1 ∨
              (((U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G)).relIndex U / a : ℕ)
                : ℤ) * k = -1 := by
  intro G _ _ hG M U W₁ W₂ hM htype hc E a b hEH hcard hsup hindep hUnorm hb hconj _hscalar ha hidx
  have hfin : Finite G := Finite.of_fintype G
  have hodd := hG.odd
  have : Fintype ↑(Irr ↥(W₁.subgroupOf M)) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hodd
  have hKn : (derivedOf M).Normal := h.normal
  obtain ⟨σ, hσ⟩ := h.exists_isCyclicTIIsometry
  set w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :=
    fun i j => h.isCyclicTIPair.basisProdIrr (i, j) with hw
  set l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ := fun i => h.inflateLeft i with hl
  have hrowD : IsRowData M W₁ W₂ σ w l := by
    refine { isometry := hσ, prod := ?_, infl := ?_ }
    · intro i j x y z hz
      rw [hw, h.isCyclicTIPair.coe_basisProdIrr_apply]
      have h6 := h.isCyclicTIPair.prodChar_apply_mul (i : ↥(W₁.subgroupOf M) → ℂ)
        (j : ↥(W₂.subgroupOf M) → ℂ) x.2 y.2
      convert h6 using 2
      exact Subtype.ext hz
    · intro i k v z hz
      subst hz
      exact h.inflateLeft_apply_mul i k.2 v.2
  set sg : ↑(Irr ↥(W₂.subgroupOf M)) → ℂ := fun j => h.primeTISign σ j with hsg
  set mu : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) → ↥M → ℂ :=
    fun i j => h.primeTIirr σ i j with hmu
  have hsetup : IsRowSetup M W₁ W₂ σ w l sg mu := by
    refine { toIsRowData := hrowD, sign := ?_, mu_zero_mem := ?_, mu_eq := ?_ }
    · intro j; exact h.primeTISign_eq_one_or_eq_neg_one j
    · intro j
      have h4 := h.primeTIirr_principal_left_mem_Irr hσ j
      rw [h.primeTIirr_principal_left] at h4
      exact h4
    · intro i j
      change h.primeTIirr σ i j = _
      rw [h.primeTIirr_eq_mul i j, h.primeTIirr_principal_left]
  have hrowsum : ∀ j, (∑ᶠ i : ↑(Irr ↥(W₁.subgroupOf M)), mu i j) = h.primeTIrow σ j := by
    intro j
    rw [finsum_eq_sum_of_fintype, h.primeTIrow_def]
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := CrossedRowData.isCyclicTIPair_sup hodd hc
  obtain ⟨ω, hω⟩ := hW.exists_isCyclicTIIsometry
  have heta := isEtaSetup_basisProdIrr hW hω
  set C : Subgroup G := U ⊓ centralizer ((Prep06.hallCoreIn M : Subgroup G) : Set G) with hCdef
  set S₁ := indFamKer M (derivedOf M) ((Prep06.hallCoreIn M ⊔ C : Subgroup G).subgroupOf M) with hS₁def
  set S₂ := indFamDetectKer M (derivedOf M) (C.subgroupOf M) ((Prep06.hallCoreIn M).subgroupOf M)
    with hS₂def
  obtain ⟨-, hCeq, -, hdisj12, -, hS₂star, -, -, hcoh₂, -, hS₁Irr, hS₁deg, n₁, hn₁card, -, hn₁2,
    -⟩ := CFSG.FeitThompson.Proofs.FPF_type_iii_iv_two_coherent_layers h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂
      hM htype hc C rfl S₁ S₂ rfl rfl
  obtain ⟨ζ, hζ⟩ : S₁.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hn₁card
    simp at hn₁card
    omega
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hS₁ind : S₁ ⊆ indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) := by
    intro f hf
    have := indFamKer_subset_indFamNonprincipal M _ _ hf
    rwa [indFamNonprincipal_eq_indFam_sdiff] at this
  have hS₂ind : S₂ ⊆ indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1}) :=
    indFamDetectKer_subset_indFam_sdiff
  have hζind := hS₁ind hζ
  have hζIrr : ζ ∈ Irr ↥M := hS₁Irr hζ
  have hζ1 : ζ 1 = (Nat.card ↥(W₁.subgroupOf M) : ℂ) := by rw [hcard1]; exact hS₁deg ζ hζ
  obtain ⟨d, n, hB, hrows, -⟩ := exists_isUniformBridgeData_of_isRowSetup h₁ h₂ h₃ h₄ h₅
    hG hM htype hc hsetup h hrowsum (fun _ => rfl) (fun _ _ => rfl) hζind hζIrr hζ1 hcard1
  obtain ⟨d', n', dsign, -, -, -, -, -, hdeg, hsign, hdn⟩ :=
    (CFSG.FeitThompson.Proofs.FPF_type_iii_v_local_character_constants h₅ G hG M U W₁ W₂ hM
      (by tauto) hc).2.2 σ w l sg mu hsetup
  obtain ⟨hrd, -, -, -, -, -⟩ :=
    CFSG.FeitThompson.Proofs.FPF_type_iii_iv_row_degree_and_kernel h₁ h₅ G hG M U W₁ W₂ hM htype hc
      σ w l sg mu hsetup d' n' dsign hdeg hsign hdn
  obtain ⟨-, -, -, hD, -⟩ := h₃ G hG M U W₁ W₂ hM (by tauto) hc
  have hA := CrossedRowData.image_primeTIbridgeSupport_subset_dadeA0 hc
  have hAb := PrimeDadeColumnGluing.image_bridgeSupport_subset hA
  have hA0 : ∀ x ∈ derivedOf M, x ≠ 1 → (x : G) ∈ dadeA0 M W₁ W₂ := fun x hx hx1 =>
    hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hx hx1, rfl⟩
  have hF : h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ
      ∈ dadeDomain M (dadeA0 M W₁ W₂) :=
    mem_dadeDomain.2 ⟨mem_classFun_of_mem_span_Irr (h.primeTIrow_sub_mem_span_Irr hσ hζind),
      fun x hx => h.primeTIrow_sub_apply_eq_zero hσ hζind hζ1 fun hmem => hx (hA0 x hmem.1 hmem.2)⟩
  set ψ : G → ℂ := ((dadeMap hD ⟨_, hF⟩ : classFun G) : G → ℂ) with hψdef
  have hψspan : ψ ∈ Submodule.span ℤ (Irr G) :=
    hD.dadeMap_mem_span_Irr hF (h.primeTIrow_sub_mem_span_Irr hσ hζind)
  let τ₂ := TypeVTwoFamilyJoining.subDadeHom (W₁ := W₁.subgroupOf M) (W₂ := W₂.subgroupOf M)
    hD hS₂ind hAb
  obtain ⟨ν₂, hν₂⟩ := isCoherent_iff.1 (isCoherent_of_hasCoherentMap (τ := τ₂)
      (TypeVTwoFamilyJoining.coe_subDadeHom_eq_dadeMapFun hD hS₂ind hAb) hcoh₂)
  obtain ⟨hproj, -⟩ := CFSG.FeitThompson.Proofs.FPF_type_iii_iv_principal_row_projection h₁ h₂ h₃ h₄ h₅
    G hG M U W₁ W₂ hM htype hc σ w l sg mu hsetup ω _ _ heta
  have hψη : ∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)),
      cfInner ψ (hW.prodCharEta ω i j) = if i = principalIrr ↥W₁ then 1 else 0 := by
    intro i j
    have h0 := hproj ζ hζ i j
    have hτ : dadeTau M W₁ W₂
        ((∑ᶠ i' : ↑(Irr ↥(W₁.subgroupOf M)), mu i' (principalIrr ↥(W₂.subgroupOf M))) - ζ) = ψ := by
      rw [hrowsum, dadeTau_eq, hψdef, coe_dadeMap]
    rw [hτ, cfInner_sub_left, sub_eq_zero, finsum_eq_sum_of_fintype, cfInner_sum_left] at h0
    rw [h0]
    simp_rw [hW.cfInner_prodCharEta hω]
    by_cases hi : i = principalIrr ↥W₁
    · subst hi; simp
    · simp [Ne.symm hi, hi]
  have hψP : ∀ j : ↑(Irr ↥W₂), cfInner ψ (hW.prodCharEtaColSum ω j) = 1 := by
    intro j
    rw [hW.prodCharEtaColSum_eq_sum, cfInner_sum_right]
    simp_rw [hψη]
    simp
  have hcfg := isScalarCoreConfig_hallCoreLineFamily h₁ h₃ h₅ hG hM htype hc hEH hcard hsup
    hindep hUnorm hb hconj ha hidx
  have _hNZ : NeZero (Nat.card W₁) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨θ, hθIrr, hθker, hθdet, hθ1, hθind⟩ := hcfg.exists_mem_Irr_axis
  have hUM : U ≤ M := hc.le_M_E
  have hCsub : ∀ x : ↥(derivedOf M), (x : ↥M) ∈ C.subgroupOf M →
      (x : ↥M) ∈ ⁅U.subgroupOf M, U.subgroupOf M⁆ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, hCeq] at hx
    have hmap : (⁅U.subgroupOf M, U.subgroupOf M⁆).map M.subtype = ⁅U, U⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUM]
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = (x : ↥M) := Subtype.ext hyx
    rwa [← this]
  set Λ : ↥M → ℂ := indClassFun (derivedOf M) θ with hΛdef
  have hΛS : Λ ∈ S₂ := by
    rw [hS₂def, indFamDetectKer_eq, mem_indFam]
    refine ⟨θ, ⟨by rw [← Irr_eq_irrChar]; exact hθIrr, fun x hx => hθker x (hCsub x hx), ?_⟩, rfl⟩
    obtain ⟨x, hx, hne⟩ := hθdet
    exact ⟨x, by rw [Subgroup.mem_subgroupOf, Prep06.hallCoreIn_eq]; exact ⟨_, hx, rfl⟩, hne⟩
  have hθa : θ 1 = (a : ℂ) := by
    rw [hθ1, lineFixer_hallCoreLineFamily hEH, Subgroup.relIndex_subgroupOf hUM, hidx]
  have hΛ1 : Λ 1 = (Nat.card W₁ : ℂ) * a := by
    rw [hΛdef, hcfg.indClassFun_apply_one_eq, hθa]
  obtain ⟨j, hj⟩ := exists_ne_principalIrr h.right_ne_bot h.isCyclic_right
  set uu : ℕ := C.relIndex U with huu
  have hMj1 : h.primeTIrow σ j 1 = (Nat.card W₁ : ℂ) * uu := by
    rw [← hrowsum j]; exact (hrd j hj).2.2.2.2.2.1
  obtain ⟨j', ε, hε, hνMj⟩ := exists_sign_col_of_isUniformBridgeData
    (CrossedRowData.map_subtype_subgroupOf_sup hc.le_M_W₁ hc.le_M_W₂)
    (Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₁) (Subgroup.map_subgroupOf_eq_of_le hc.le_M_W₂)
    hodd hB hA hD (CrossedRowData.setOf_conj_eq_of_isWitnessedPConfiguration hc)
    (CrossedRowData.inter_eq_empty_of_isWitnessedPConfiguration hc) hW hω hS₂ind hS₂star hν₂
    (fun f F hfF => TypeVTwoFamilyJoining.coe_subDadeHom hD hS₂ind hAb f F hfF.symm)
    hrows hΛS hθind hj
  set x : Submodule.span ℤ S₂ := ⟨h.primeTIrow σ j, Submodule.subset_span (hrows j hj)⟩ with hx
  set y : Submodule.span ℤ S₂ := ⟨Λ, Submodule.subset_span hΛS⟩ with hy
  set f : Submodule.span ℤ S₂ := (a : ℤ) • x - (uu : ℤ) • y with hfdef
  have hfval : (f : ↥M → ℂ) = (a : ℤ) • h.primeTIrow σ j - (uu : ℤ) • Λ := rfl
  have hf1 : (f : ↥M → ℂ) 1 = 0 := by
    rw [hfval, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, zsmul_eq_mul, zsmul_eq_mul, hMj1, hΛ1]
    push_cast; ring
  have hsub : indFam (derivedOf M) (Irr ↥(derivedOf M) \ {1})
      ⊆ indFam (derivedOf M) (Irr ↥(derivedOf M)) := indFam_mono _ Set.sdiff_subset
  have hfD : (f : ↥M → ℂ) ∈ dadeDomain M (dadeA0 M W₁ W₂) :=
    PrimeDadePivot.mem_dadeDomain_of_mem_span_indFam hA0 (hS₂ind.trans hsub) f.2 hf1
  set fz : charSpanZero S₂ := ⟨(f : ↥M → ℂ), mem_charSpanZero.2 ⟨f.2, hf1⟩⟩ with hfz
  have hνf : ((ν₂ f : virtualChars G) : G → ℂ)
      = ((dadeMap hD ⟨_, hfD⟩ : classFun G) : G → ℂ) := by
    have h1 := hν₂.eq_on_zero fz
    have h2 : Submodule.inclusion (charSpanZero_le S₂) fz = f := Subtype.ext rfl
    rw [h2] at h1
    rw [h1]
    exact TypeVTwoFamilyJoining.coe_subDadeHom hD hS₂ind hAb fz ⟨_, hfD⟩ rfl
  have hzero : cfInner ψ ((ν₂ f : virtualChars G) : G → ℂ) = 0 := by
    rw [hνf, hψdef, cfInner_dadeMap hD]
    change cfInner (h.primeTIrow σ (principalIrr ↥(W₂.subgroupOf M)) - ζ) (f : ↥M → ℂ) = 0
    rw [hfval, h.primeTIrow_principal hσ]
    have e1 : cfInner (indClassFun (derivedOf M) 1) (h.primeTIrow σ j) = 0 :=
      NormalInducedFamily.cfInner_indClassFun_one_left_of_mem_indFam_sdiff (hS₂ind (hrows j hj))
    have e2 : cfInner (indClassFun (derivedOf M) 1) Λ = 0 :=
      NormalInducedFamily.cfInner_indClassFun_one_left_of_mem_indFam_sdiff (hS₂ind hΛS)
    have e3 : cfInner ζ (h.primeTIrow σ j) = 0 :=
      NormalInducedFamily.cfInner_eq_zero_of_mem_indFam _
        (hsub (hS₁ind hζ)) (hsub (hS₂ind (hrows j hj)))
        (fun he => Set.disjoint_left.1 hdisj12 hζ (he ▸ hrows j hj))
    have e4 : cfInner ζ Λ = 0 := NormalInducedFamily.cfInner_eq_zero_of_mem_indFam _
      (hsub (hS₁ind hζ)) (hsub (hS₂ind hΛS)) (fun he => Set.disjoint_left.1 hdisj12 hζ (he ▸ hΛS))
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_zsmul_right,
      cfInner_zsmul_right, cfInner_zsmul_right, cfInner_zsmul_right, e1, e2, e3, e4]
    ring
  obtain ⟨m, hm⟩ := exists_int_cfInner_of_mem_span_Irr hψspan (coe_mem_span_Irr (ν₂ y))
  have hsplit : ((ν₂ f : virtualChars G) : G → ℂ)
      = (a : ℤ) • ((ν₂ x : virtualChars G) : G → ℂ)
        - (uu : ℤ) • ((ν₂ y : virtualChars G) : G → ℂ) := by
    rw [hfdef, map_sub, map_zsmul, map_zsmul]; rfl
  rw [hsplit, cfInner_sub_right, cfInner_zsmul_right, cfInner_zsmul_right, hνMj,
    cfInner_smul_right, hψP, hm] at hzero
  have ha0 : 0 < a := by omega
  have i₀ : Fin (Nat.card W₁) := ⟨0, Nat.card_pos⟩
  have hdvd : a ∣ uu := by
    rw [← hidx i₀]
    exact dvd_relIndex_centralizer_of_le (hEH i₀)
  refine ⟨m, ?_⟩
  obtain ⟨c, hc'⟩ := hdvd
  rw [hc', Nat.mul_div_cancel_left _ ha0]
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha0.ne'
  rw [hc'] at hzero
  rcases hε with rfl | rfl
  · left
    have h3 : ((a : ℤ) : ℂ) = ((a * c : ℕ) : ℤ) * (m : ℂ) := by
      simp only [map_one, mul_one] at hzero; linear_combination hzero
    have h2 : (a : ℤ) = ((a * c : ℕ) : ℤ) * m := by exact_mod_cast h3
    push_cast at h2
    apply mul_left_cancel₀ ha'; linear_combination -h2
  · right
    have h3 : -((a : ℤ) : ℂ) = ((a * c : ℕ) : ℤ) * (m : ℂ) := by
      simp only [map_neg, map_one, mul_neg, mul_one] at hzero; linear_combination hzero
    have h2 : -(a : ℤ) = ((a * c : ℕ) : ℤ) * m := by exact_mod_cast h3
    push_cast at h2
    apply mul_left_cancel₀ ha'; linear_combination -h2

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson

universe u

theorem FPF_type_iii_iv_scalar_coordinate_index_collapse
    (h₁ : Statements.FPF_type_iii_iv_core_elementary_chief_kernel_trivial.{u})
    (h₂ : Statements.FPF_type_iii_iv_second_derived_fitting.{u})
    (h₃ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₄ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₅ : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_iv_scalar_coordinate_index_collapse.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc E a b hEH hcard hsup hindep hUnorm hb hconj hscalar ha
    hidx
  obtain ⟨k, hk⟩ := indexCollapse_residual h₁ h₂ h₃ h₄ h₅ G hG M U W₁ W₂ hM htype hc E a b hEH
    hcard hsup hindep hUnorm hb hconj hscalar ha hidx
  have i₀ : Fin (Nat.card W₁) := ⟨0, Nat.card_pos⟩
  have hdvd : a ∣ (U ⊓ centralizer
      ((CFSG.FeitThompson.Prep06.hallCoreIn M : Subgroup G) : Set G)).relIndex U := by
    rw [← hidx i₀]
    exact dvd_relIndex_centralizer_of_le (hEH i₀)
  exact eq_of_dvd_of_mul_int_eq_one_or_neg_one hdvd hk

end CFSG.FeitThompson.Proofs

end
