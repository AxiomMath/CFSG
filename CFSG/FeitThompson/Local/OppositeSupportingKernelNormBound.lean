module

public import CFSG.FeitThompson.Local.OppositeSupportingKernelGrowth
public import CFSG.FeitThompson.Representations.PairedSupportingKernelCollapse
public import CFSG.FeitThompson.Representations.PairedFieldArrayValueCover
public import CFSG.FeitThompson.Representations.ActualTypeICrossedControl
public import CFSG.FeitThompson.Representations.DadePacketInverseNormBound
public import CFSG.FeitThompson.Local.TwoCoreMixedSaturationMeasure

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace OppositeSupportingKernelNormBound

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Proofs.CrossedTypeI

universe u

variable {G : Type*} [Group G]

theorem prep03_hallCoreIn_eq' (M : Subgroup G) :
    CFSG.FeitThompson.Prep03.hallCoreIn M = hallCoreIn M := (rfl)

theorem prep05_hallCoreOf_eq [Finite G] (M : Subgroup G) :
    CFSG.FeitThompson.Prep05.hallCoreOf M = hallCoreIn M := (rfl)

theorem sigR_eq [Finite G] : (CFSG.FeitThompson.Prep03.sigR : G → Subgroup G) = sigCoreSignalizer :=
  funext _root_.CFSG.FeitThompson.Proofs.prep03_sigR_eq_sigCoreSignalizer

theorem natCard_mul_relIndex [Finite G] {H M : Subgroup G} (h : H ≤ M) :
    Nat.card ↥H * H.relIndex M = Nat.card ↥M := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv,
    Subgroup.card_mul_index]

theorem isClassFun_of_mem_classFun' {f : G → ℂ} (h : f ∈ classFun G) : IsClassFun f :=
  isClassFun_iff.2 fun x g => mem_classFun.1 h _ _ (isConj_iff.2 ⟨x⁻¹, by group⟩)

theorem normal_hallCoreIn_subgroupOf (M : Subgroup G) :
    ((hallCoreIn M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hallCoreIn_le M)).2
    (le_normalizer_map_subtype_hallCore M)

@[expose]
noncomputable def rho [Fintype G] (M : Subgroup G) (χ : G → ℂ) : ↥M → ℂ :=
  fun y => dadeAverage ((hallCoreIn M : Set G) \ {1}) sigCoreSignalizer χ (y : G)

theorem rho_def [Fintype G] (M : Subgroup G) (χ : G → ℂ) :
    rho M χ = fun y : ↥M =>
      dadeAverage ((hallCoreIn M : Set G) \ {1}) sigCoreSignalizer χ (y : G) := (rfl)

theorem dadeAverage_neg [Fintype G] (A : Set G) (H : G → Subgroup G) (χ : G → ℂ) :
    dadeAverage A H (-χ) = -dadeAverage A H χ := by
  have h : (-χ) = ((-1 : ℂ) • χ) := by funext x; simp
  rw [h, dadeAverage_smul]
  funext x
  simp

theorem rho_neg [Fintype G] (M : Subgroup G) (χ : G → ℂ) : rho M (-χ) = -rho M χ := by
  funext y
  rw [rho_def, rho_def, dadeAverage_neg]
  simp

theorem cfInner_rho_neg [Fintype G] (M : Subgroup G) [Fintype ↥M] (χ : G → ℂ) :
    cfInner (rho M (-χ)) (rho M (-χ)) = cfInner (rho M χ) (rho M χ) := by
  rw [rho_neg, cfInner_neg_left, cfInner_neg_right, neg_neg]

theorem one_sub_le_re_cfInner_rho
    (G : Type u) [Group G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    (hD : IsDadeData M ((hallCoreIn M : Set G) \ {1}) sigCoreSignalizer)
    (hIrr : calLFam M ⊆ Irr ↥M) (hnt : (calLFam M).Nontrivial)
    (hbd : 2 * (hallCoreIn M).relIndex M ≤ Nat.card ↥(hallCoreIn M) - 1)
    {ν : (↥M → ℂ) → (G → ℂ)} (hν : IsCoherentDade M ν)
    {φ : ↥M → ℂ} (hφ : φ ∈ calLFam M)
    (hφ1 : φ 1 = ((hallCoreIn M).relIndex M : ℂ)) :
    1 - ((hallCoreIn M).relIndex M : ℝ) / (Nat.card ↥(hallCoreIn M) : ℝ)
      ≤ (cfInner (rho M (ν φ)) (rho M (ν φ))).re := by
  classical
  have key := NormalInducedFamily.one_sub_index_div_card_le_cfInner_self_dadeAverage_coherentImage
    (L := M) (A := ((hallCoreIn M : Set G) \ {1})) (R := sigCoreSignalizer)
    (H := hallCore ↥M) (ξ := calLEnum M)
    (τ := baselineDadeHom hν) (ν := coherentDadeHom hν) (k₀ := ⟨φ, hφ⟩)
    hD (image_coe_hallCore_sdiff_one M).symm
    (range_calLEnum_eq_indFam M)
    (injective_calLEnum M) (isCoherentWith_coherentDadeHom hν)
    (fun f F hfF => coe_baselineDadeHom_eq_dadeMap hν
      hD f F hfF)
    (hIrr hφ)
    (by rw [calLEnum_mk, hφ1, index_hallCore_eq_relIndex])
    (by rw [range_calLEnum]; exact hnt)
    (two_mul_index_add_one_le hbd)
  rw [coherentImage_coherentDadeHom hν ⟨φ, hφ⟩, natCard_hallCore_eq, index_hallCore_eq_relIndex] at key
  rw [rho_def]
  exact key

theorem re_cfInner_rho_le
    (G : Type u) [Group G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    (hD : IsDadeData M ((hallCoreIn M : Set G) \ {1}) sigCoreSignalizer)
    (E : Set G) {χ : G → ℂ} (hcf : χ ∈ classFun G) (hone : cfInner χ χ = 1)
    (hge : ∀ g ∉ CFSG.FeitThompson.dadeSupportDomain M ∪ E, 1 ≤ ‖χ g‖ ^ 2) :
    (cfInner (rho M χ) (rho M χ)).re
      ≤ ((((hallCoreIn M : Set G) \ {1}).ncard : ℝ)) / (Nat.card ↥M : ℝ)
        + (E.ncard : ℝ) / (Nat.card G : ℝ) := by
  have hone' : ∀ g ∉ totalDadeSupport ((hallCoreIn M : Set G) \ {1}) sigCoreSignalizer ∪ E,
      1 ≤ ‖((⟨χ, hcf⟩ : ↥(classFun G)) : G → ℂ) g‖ ^ 2 := by
    intro g hg
    exact hge g (by rwa [CFSG.FeitThompson.dadeSupportDomain_eq M])
  have key := cfInner_self_dadeAverage_le_add_of_one_le_norm_sq hD E ⟨χ, hcf⟩ hone hone'
  have hre := (Complex.le_def.1 key).1
  rw [rho_def]
  simpa using hre

theorem mem_classFun_and_cfInner_eq_one [Fintype G] {χ : G → ℂ}
    (h : χ ∈ Irr G ∨ -χ ∈ Irr G) : χ ∈ classFun G ∧ cfInner χ χ = 1 := by
  rcases h with h | h
  · exact ⟨Irr_subset_classFun h, cfInner_self_of_mem_Irr h⟩
  · refine ⟨?_, ?_⟩
    · have hmem := Irr_subset_classFun h
      have h2 : χ = -(-χ) := by funext x; simp
      rw [h2]; exact neg_mem hmem
    · have h1 := cfInner_self_of_mem_Irr h
      rw [cfInner_neg_left, cfInner_neg_right, neg_neg] at h1
      exact h1

theorem coe_cyclicTIset (W₁ W₂ : Subgroup G) :
    cyclicTIset W₁ W₂ = ((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)) := by
  ext z; rw [mem_cyclicTIset]; simp [not_or]

theorem satSet_eq_conjugatesOfSet (A : Set G) : satSet A = Group.conjugatesOfSet A := by
  rw [conjugatesOfSet_eq_iUnion_image_conj_inv]; rfl

def exceptionSet (S T W₁ W₂ : Subgroup G) : Set G :=
  satSet ((hallCoreIn S : Set G) \ {1}) ∪ satSet ((hallCoreIn T : Set G) \ {1})
    ∪ satSet (cyclicTIset W₁ W₂)

theorem natCard_eq_mul_mul
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (G : Type u) [Group G] [Finite G] (hG : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G)
    {S U W₁ W₂ : Subgroup G} (hS : IsCoatom S)
    (hcfg : IsWitnessedPConfiguration S U W₁ W₂) :
    Nat.card ↥S = Nat.card ↥(hallCoreIn S) * Nat.card ↥U * Nat.card ↥W₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, hsemi1, hsemi2, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₅ G hG S U W₁ W₂ hS hcfg _ _ rfl rfl
  rw [hsemi1.natCard_eq_mul, hsemi2.natCard_eq_mul, prep05_hallCoreOf_eq, mul_assoc]

theorem measure_exceptionSet_le
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (G : Type u) [Group G] [Finite G] (hG : IsFBGAmbient G)
    {S T U V W₁ W₂ : Subgroup G} {p q : ℕ}
    (hsetup : IsOppositeSupportingSetup S T U V W₁ W₂ p q) :
    ((exceptionSet S T W₁ W₂).ncard : ℝ) / (Nat.card G : ℝ)
      ≤ 1 / ((Nat.card ↥U : ℝ) * q) + 1 / ((Nat.card ↥V : ℝ) * p)
        + ((p : ℝ) - 1) * ((q : ℝ) - 1) / ((p : ℝ) * q) := by
  have hG5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hcfgS := hsetup.pconfig_S
  have hcfgT := hsetup.pconfig_T
  have hTI : ∀ g ∉ (W₁ ⊔ W₂ : Subgroup G),
      (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) ∩
        ((fun x => g⁻¹ * x * g) ''
          (((W₁ ⊔ W₂ : Subgroup G) : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G)))) = ∅ := by
    intro g hg
    have hg' : g⁻¹ ∉ (W₁ ⊔ W₂ : Subgroup G) := fun hc => hg (by simpa using inv_mem hc)
    have hd := hcfgS.disjoint_cyclicTIset_conj hg'
    rw [Set.disjoint_iff_inter_eq_empty, coe_cyclicTIset] at hd
    refine Eq.trans (congrArg _ ?_) hd
    exact Set.image_congr' fun x => by simp only [MulAut.conj_apply, inv_inv]
  have hmain := two_core_mixed_saturation_measure (G := G)
    (P := hallCoreIn S) (S := S) (Q := hallCoreIn T) (T := T) (W₁ := W₁) (W₂ := W₂)
    (u := Nat.card ↥U) (v := Nat.card ↥V) (p := p) (q := q)
    hcfgS.hallCore_ne_bot hcfgT.hallCore_ne_bot
    (hallCoreIn_le S) (normal_hallCoreIn_subgroupOf S)
    (hallCoreIn_le T) (normal_hallCoreIn_subgroupOf T)
    Nat.card_pos Nat.card_pos hsetup.prime_p.one_lt hsetup.prime_q.one_lt
    (by rw [natCard_eq_mul_mul h₅ G hG5 hsetup.isCoatom_S hcfgS, hsetup.natCard_W₁])
    (by rw [natCard_eq_mul_mul h₅ G hG5 hsetup.isCoatom_T hcfgT, hsetup.natCard_W₂])
    (fun x hx y hy => hcfgS.commute_W₁_W₂ hx hy)
    hsetup.natCard_W₁ hsetup.natCard_W₂ hcfgS.inf_W₁_W₂
    (by rw [← coe_cyclicTIset]; exact hcfgS.normalizer_cyclicTIset) hTI
  rw [exceptionSet, satSet_eq_conjugatesOfSet, satSet_eq_conjugatesOfSet,
    satSet_eq_conjugatesOfSet, coe_cyclicTIset]
  exact hmain.2.2.2

theorem typeI_data
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (G : Type u) [Group G] [Fintype G] (hamb : CFSG.FeitThompson.Prep03.IsAmbient G)
    {M : Subgroup G} (hM : IsCoatom M) (hMI : IsTypeI M) :
    IsDadeData M ((hallCoreIn M : Set G) \ {1}) sigCoreSignalizer ∧
      calLFam M ⊆ Irr ↥M ∧ (calLFam M).Nontrivial ∧
      1 < Nat.card ↥(hallCoreIn M) ∧ 1 < (hallCoreIn M).relIndex M ∧
      2 * (hallCoreIn M).relIndex M ≤ Nat.card ↥(hallCoreIn M) - 1 ∧
      (∀ f ∈ calLFam M, (fun x => (starRingEnd ℂ) (f x)) ∈ calLFam M) ∧
      ∃ ν : (↥M → ℂ) → (G → ℂ), IsCoherentDade M ν ∧
        ∃ φ ∈ calLFam M, φ 1 = ((hallCoreIn M).relIndex M : ℂ) := by
  obtain ⟨-, -, hk1, he1, hbd, hD, -, -, -, hIrr, hclosed, -, ⟨ν, hν⟩, φ, hφ, hφ1⟩ :=
    h₃ G hamb M hM hMI
  have hIrr' : calLFam M ⊆ Irr ↥M := by
    rwa [_root_.CFSG.FeitThompson.Proofs.hallIndFamily_eq_calLFam] at hIrr
  have hfin : Finite ↥(calLFam M) := (Set.Finite.subset finite_Irr hIrr').to_subtype
  have hnt : (calLFam M).Nontrivial := by
    have h2 : 2 ≤ (calLFam M).ncard := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h2, -⟩ := h₃ G hamb M hM hMI
      rwa [_root_.CFSG.FeitThompson.Proofs.hallIndFamily_eq_calLFam] at h2
    exact Set.one_lt_ncard_iff_nontrivial.1 (by omega)
  refine ⟨by rwa [prep03_hallCoreIn_eq', sigR_eq] at hD, hIrr', hnt, hk1, he1, hbd, ?_,
    ν, (_root_.CFSG.FeitThompson.Proofs.isCoherentDade_iff_isCoherentOn M ν).2 hν,
    φ, by rwa [_root_.CFSG.FeitThompson.Proofs.hallIndFamily_eq_calLFam] at hφ, hφ1⟩
  intro f hf
  rw [← _root_.CFSG.FeitThompson.Proofs.hallIndFamily_eq_calLFam] at hf ⊢
  exact hclosed f hf

theorem one_le_sq_norm_of_eq_array
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsFBGAmbient G)
    {S T U V W₁ W₂ : Subgroup G} {p q : ℕ}
    (hsetup : IsOppositeSupportingSetup S T U V W₁ W₂ p q)
    {M : Subgroup G} {I J : Type u} [Fintype I] [Fintype J]
    {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)}
    {σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
    {η : I → J → (G → ℂ)} {δ : J → ℂ} {μ : J → (↥S → ℂ)} {γ : ↥S → ℂ}
    {bfam : J → (↥S → ℂ)}
    (hdata : IsPBridgeData S M U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    {χ : G → ℂ} (hcf : IsClassFun χ) {ε : I → J → ℂ} (hsigns : ∀ i j, ε i j = 1 ∨ ε i j = -1)
    (hval : ∀ g : G, g ∉ CFSG.FeitThompson.dadeSupportDomain M →
      χ g = ∑ i : I, ∑ j : J, ε i j * η i j g) :
    ∀ g : G, g ∉ CFSG.FeitThompson.dadeSupportDomain M ∪ exceptionSet S T W₁ W₂ → 1 ≤ ‖χ g‖ ^ 2 := by
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨helem, hirr⟩ := hsetup.irreducible
  exact _root_.CFSG.FeitThompson.Proofs.FBG_paired_field_array_value_cover h₄ h₅ G hG2
    S T U V W₁ W₂ hsetup.isCoatom_S hsetup.isCoatom_T hsetup.ne hsetup.pconfig_S hsetup.pconfig_T
    _ _ rfl rfl _ _ _ _ hsetup.natCard_W₂.symm hsetup.natCard_W₁.symm rfl rfl
    hsetup.prime_p hsetup.prime_q hsetup.odd_p hsetup.odd_q hsetup.lt helem hirr
    I J inferInstance inferInstance α β i₀ j₀ hdata.isIrrIndexing_W₁ hdata.isIrrIndexing_W₂
    w hdata.isProductCharFamily ω hdata.isOmegaMap η hdata.eta_eq _ rfl
    (CFSG.FeitThompson.dadeSupportDomain M) χ hcf ε hsigns hval

theorem final_arithmetic {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {k u v : ℝ}
    (h : 1 - p * q / k ≤ 1 / (p * q) + 1 / (u * q) + 1 / (v * p) + (p - 1) * (q - 1) / (p * q)) :
    1 / p + 1 / q ≤ p * q / k + 2 / (p * q) + 1 / (u * q) + 1 / (v * p) := by
  have hexp : (p - 1) * (q - 1) / (p * q) = 1 - 1 / q - 1 / p + 1 / (p * q) := by
    field_simp; ring
  have h2 : 2 / (p * q) = 1 / (p * q) + 1 / (p * q) := by ring
  rw [hexp] at h
  rw [h2]
  linarith

theorem le_one_div_of_norm_bounds {k e : ℕ} {a x : ℝ} (hk : 0 < k) (he : 0 < e)
    (hlow : 1 - (e : ℝ) / (k : ℝ) ≤ a)
    (hup : a ≤ (((k : ℝ) - 1)) / ((k : ℝ) * (e : ℝ)) + x) :
    1 - (e : ℝ) / (k : ℝ) ≤ 1 / (e : ℝ) + x := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hstep : ((k : ℝ) - 1) / ((k : ℝ) * (e : ℝ)) ≤ 1 / (e : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) he']
    nlinarith
  linarith

theorem main
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FCH_actual_paired_support_saturation.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_opposite_supporting_kernel_norm_bound.{u} := by
  intro G _ _ hG S T U V W₁ W₂ p q hpair M hM hVM hlt
  have _iF : Fintype G := Fintype.ofFinite G
  have _iM : Fintype ↥M := Fintype.ofFinite ↥M
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hamb : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hsetup := hpair.base
  have hp : Nat.card ↥W₂ = p := hsetup.natCard_W₂
  have hq : Nat.card ↥W₁ = q := hsetup.natCard_W₁
  obtain ⟨hMI, hVK, hecases, -, -, -, hgrowth⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FBG_opposite_supporting_kernel_growth h₁ h₄ h₅ G hG S T U V W₁ W₂
      p q hpair M hM hVM
  obtain ⟨-, hthrUV, hthrVK⟩ := hgrowth hlt
  obtain ⟨hD, hIrr, hnt, hk1, he1, hbd, hclosed, ν, hν, φ, hφ, hφ1⟩ :=
    typeI_data h₃ G hamb hM hMI
  have hidx : hallCoreIndex M = (hallCoreIn M).relIndex M := hallCoreIndex_eq M
  have hφ1' : φ 1 = (hallCoreIndex M : ℂ) := by rw [hidx]; exact hφ1
  obtain ⟨I, J, _, _, α, β, i₀, j₀, w, σ, ω, η, δ, μ, γ, bfam, hdata⟩ :=
    PairedSupportingKernel.exists_isPBridgeData hG.odd_natCard hsetup.isCoatom_S
      hsetup.pconfig_S hM hMI
  have hle : hallCoreIndex M ≤ Nat.card ↥W₂ * Nat.card ↥W₁ := by
    rw [hidx, hp, hq]
    rcases hecases with h | h
    · rw [h]; nlinarith [hsetup.prime_q.one_lt, hsetup.prime_p.pos]
    · rw [h]
  have hthr1 : ((Nat.card ↥U : ℚ) - 1) / (Nat.card ↥W₁ : ℚ)
      < ((Nat.card ↥(hallCoreIn M) : ℚ) - 1) / (hallCoreIndex M : ℚ) := by
    rw [hq, hidx]; exact lt_trans hthrUV hthrVK
  have hthr2 : ((Nat.card ↥V : ℚ) - 1) / (Nat.card ↥W₂ : ℚ)
      < ((Nat.card ↥(hallCoreIn M) : ℚ) - 1) / (hallCoreIndex M : ℚ) := by
    rw [hp, hidx]; exact hthrVK
  obtain ⟨hepq, ε, χ, hsigns, hχalt, hχirr, hβexp, -⟩ :=
    h₂ G hG2 S M U W₁ W₂ I J inferInstance inferInstance α β i₀ j₀ w σ ω η δ μ γ bfam hdata
      T V hsetup.isCoatom_T hsetup.pconfig_T _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl
      ν hν φ hφ hφ1' _ rfl hle hthr1 hthr2
  have he : (hallCoreIn M).relIndex M = p * q := by rw [← hidx, hepq, hp, hq]
  obtain ⟨hχcf, hχone⟩ := mem_classFun_and_cfInner_eq_one hχirr
  have hval : ∀ g : G, g ∉ CFSG.FeitThompson.dadeSupportDomain M →
      χ g = ∑ i : I, ∑ j : J, ε i j * η i j g := by
    intro g hg
    have h0 : CFSG.FeitThompson.tauDade M
        (CFSG.FeitThompson.indBetween (hallCoreIn M) M 1 - φ) g = 0 :=
      CFSG.FeitThompson.tauDade_eq_zero_of_notMem_dadeSupportDomain hg
    rw [hβexp] at h0
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
    exact (sub_eq_zero.1 h0).symm
  have hge := one_le_sq_norm_of_eq_array h₄ h₅ G hG hsetup hdata
    (isClassFun_of_mem_classFun' hχcf) hsigns hval
  have hup := re_cfInner_rho_le G hD (exceptionSet S T W₁ W₂) hχcf hχone hge
  have hlow : 1 - ((hallCoreIn M).relIndex M : ℝ) / (Nat.card ↥(hallCoreIn M) : ℝ)
      ≤ (cfInner (rho M χ) (rho M χ)).re := by
    rcases hχalt with rfl | rfl
    · exact one_sub_le_re_cfInner_rho G hD hIrr hnt hbd hν hφ hφ1
    · rw [cfInner_rho_neg]
      refine one_sub_le_re_cfInner_rho G hD hIrr hnt hbd hν (hclosed φ hφ) ?_
      simp [hφ1]
  have hkpos : 0 < Nat.card ↥(hallCoreIn M) := Nat.card_pos
  have hcardM : (Nat.card ↥M : ℝ)
      = (Nat.card ↥(hallCoreIn M) : ℝ) * ((hallCoreIn M).relIndex M : ℝ) := by
    rw [← Nat.cast_mul, natCard_mul_relIndex (hallCoreIn_le M)]
  have hsdiff : ((((hallCoreIn M : Set G) \ {1}).ncard : ℝ))
      = (Nat.card ↥(hallCoreIn M) : ℝ) - 1 := by
    have h := ncard_sdiff_singleton_one_add_one (G := G) (hallCoreIn M)
    linarith
  rw [hsdiff, hcardM] at hup
  have hcomb := le_one_div_of_norm_bounds hkpos
    (he ▸ Nat.mul_pos hsetup.prime_p.pos hsetup.prime_q.pos) hlow hup
  have hEle := measure_exceptionSet_le h₅ G hG hsetup
  rw [he] at hcomb
  have hpr : (0 : ℝ) < p := by exact_mod_cast hsetup.prime_p.pos
  have hqr : (0 : ℝ) < q := by exact_mod_cast hsetup.prime_q.pos
  have hmul : ((p * q : ℕ) : ℝ) = (p : ℝ) * (q : ℝ) := by push_cast; ring
  rw [hmul] at hcomb
  have hstep : 1 - (p : ℝ) * q / (Nat.card ↥(hallCoreIn M) : ℝ)
      ≤ 1 / ((p : ℝ) * q) + 1 / ((Nat.card ↥U : ℝ) * q) + 1 / ((Nat.card ↥V : ℝ) * p)
        + ((p : ℝ) - 1) * ((q : ℝ) - 1) / ((p : ℝ) * q) := by
    linarith [hcomb, hEle]
  have hfinal := final_arithmetic hpr hqr hstep
  have hcast : ((1 / (p : ℚ) + 1 / (q : ℚ) : ℚ) : ℝ)
      ≤ (((p : ℚ) * q / (Nat.card ↥(hallCoreIn M) : ℚ) + 2 / ((p : ℚ) * q) +
        1 / ((Nat.card ↥U : ℚ) * q) + 1 / ((Nat.card ↥V : ℚ) * p) : ℚ) : ℝ) := by
    push_cast
    exact hfinal
  exact_mod_cast hcast

end OppositeSupportingKernelNormBound

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

universe u

theorem FBG_opposite_supporting_kernel_norm_bound
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_type_II_supporting_maximal_configuration.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FCH_actual_paired_support_saturation.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_opposite_supporting_kernel_norm_bound.{u} :=
  CFSG.FeitThompson.OppositeSupportingKernelNormBound.main.{u} h₁ h₂ h₃ h₄ h₅

end

end CFSG.FeitThompson.Proofs
