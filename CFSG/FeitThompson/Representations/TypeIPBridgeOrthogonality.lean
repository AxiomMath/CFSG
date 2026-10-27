module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Representations.DisjointCyclicTISupportSeparatesFamily
public import CFSG.FeitThompson.Representations.ProductCharactersFullBasis
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson CFSG.FeitThompson
open scoped Pointwise

universe u

noncomputable local instance subgroupFintype {H : Type*} [Group H] [Fintype H] (X : Subgroup H) :
    Fintype ↥X := Fintype.ofFinite _

variable {G : Type*} [Group G]

theorem extendSub_eq_extendByZero (K : Subgroup G) (θ : ↥K → ℂ) :
    extendSub K θ = extendByZero K θ := by
  funext x
  by_cases hx : x ∈ K
  · rw [show x = ((⟨x, hx⟩ : ↥K) : G) from rfl, extendSub_apply_coe, extendByZero_apply_coe]
  · rw [extendSub_apply_of_notMem K θ hx, extendByZero_of_notMem K θ hx]

theorem prep03_sat_eq_satSet (A : Set G) : Prep03.sat A = satSet A :=
  Set.iUnion_congr fun _ => (rfl)

theorem prep03_hallCoreIn_eq (M : Subgroup G) : Prep03.hallCoreIn M = hallCoreIn M := (rfl)

theorem prep03_sigR_eq_sigCoreSignalizer [Finite G] (a : G) :
    Prep03.sigR a = sigCoreSignalizer a := (rfl)

theorem tauDade_eq_tauHall [Finite G] (L : Subgroup G) (f : ↥L → ℂ) :
    tauDade L f = Prep03.tauHall L f := by
  rw [tauDade, Prep03.tauHall, extendSub_eq_extendByZero]
  rfl

theorem dadeDomain_eq_hallDadeSupport [Finite G] (L : Subgroup G) :
    CFSG.FeitThompson.dadeSupportDomain L = Prep03.hallDadeSupport L := (rfl)

theorem indTop_eq_indG [Fintype G] (K : Subgroup G) (θ : ↥K → ℂ) :
    indTop K θ = Prep03.indG K θ := by
  classical
  funext y
  rw [indTop_apply, Prep03.indG, indClassFun_apply, extendSub_eq_extendByZero]
  simp only [extendByZero_apply_dite]

theorem indBetween_eq_indClassFun_subgroupOf [Fintype G] {K S : Subgroup G} (hKS : K ≤ S)
    (θ : ↥K → ℂ) :
    indBetween K S θ
      = indClassFun (K.subgroupOf S) (fun y : ↥(K.subgroupOf S) => θ ⟨((y : ↥S) : G), y.2⟩) := by
  classical
  funext y
  rw [indBetween_apply, indClassFun_apply]
  have hcard : Nat.card ↥(K.subgroupOf S) = Nat.card ↥K :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hKS).bijective
  rw [hcard, extendSub_eq_extendByZero]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [extendByZero_apply_dite]
  by_cases hz : ((t : G)⁻¹ * (y : G) * (t : G)) ∈ K
  · have hz' : (t⁻¹ * y * t : ↥S) ∈ K.subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hz
    rw [dif_pos hz, dif_pos hz']
    congr 1
  · have hz' : (t⁻¹ * y * t : ↥S) ∉ K.subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hz
    rw [dif_neg hz, dif_neg hz']

theorem isPConfigSetup_of_isPBridgeData [Fintype G] (hG : IsOddOrderMinimalSimple G)
    {S L U W₁ W₂ : Subgroup G} {I J : Type u} [Fintype I] [Fintype J]
    {α : I → (↥W₁ → ℂ)} {β : J → (↥W₂ → ℂ)} {i₀ : I} {j₀ : J}
    {w : I → J → (↥(W₁ ⊔ W₂) → ℂ)}
    {σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)} {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)}
    {η : I → J → (G → ℂ)} {δ : J → ℂ} {μ : J → (↥S → ℂ)} {γ : ↥S → ℂ}
    {bfam : J → (↥S → ℂ)}
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    Prep03.IsPConfigSetup G S U W₁ W₂ :=
  { ambient := ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative,
      hG.isSolvable_of_ne_top⟩
    isCoatom := hdata.isCoatom_S
    config := hdata.isPConfig }

omit [Group G] in
theorem cfInnerFin_eq_zero_of_support_disjoint [Finite G] {A B : G → ℂ} {D : Set G}
    (hA : ∀ x ∉ D, A x = 0) (hB : ∀ x ∈ D, B x = 0) : cfInnerFin A B = 0 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  rw [cfInnerFin_eq_cfInner, cfInner_def]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun x _ => ?_)
  by_cases hx : x ∈ D
  · rw [hB x hx]; simp
  · rw [hA x hx]; simp

theorem memClassFun_of_isClassFun {H : Type*} [Group H] {f : H → ℂ} (h : IsClassFun f) :
    f ∈ classFun H := by
  rw [mem_classFun]
  intro x y hxy
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  rw [isClassFun_iff] at h
  rw [← hc, h]

theorem cfInner_top_eq {H : Type*} [Group H] [Fintype H] (f g : H → ℂ) :
    cfInner (fun x : ↥(⊤ : Subgroup H) => f ↑x) (fun x : ↥(⊤ : Subgroup H) => g ↑x)
      = cfInner f g := by
  rw [cfInner_def, cfInner_def, Subgroup.card_top]
  congr 1
  exact Fintype.sum_equiv (Subgroup.topEquiv (G := H)).toEquiv _ _ (fun x => rfl)

theorem irr_comp_mulEquiv {A B : Type*} [Group A] [Group B] {χ : B → ℂ} (hχ : χ ∈ Irr B)
    (e : A ≃* B) : χ ∘ e ∈ Irr A := by
  have := NormalInduction.mem_irrChars_comp_mulEquiv
    (by rwa [normalInduction_irrChars_eq_Irr] : χ ∈ NormalInduction.irrChars B) e
  rwa [normalInduction_irrChars_eq_Irr] at this

theorem irr_restrict_top {H : Type*} [Group H] {χ : H → ℂ} (hχ : χ ∈ Irr H) :
    (fun x : ↥(⊤ : Subgroup H) => χ ↑x) ∈ Irr ↥(⊤ : Subgroup H) :=
  irr_comp_mulEquiv hχ (Subgroup.topEquiv (G := H))

theorem virtualChars_restrict_top {H : Type*} [Group H] {f : H → ℂ} (hf : f ∈ virtualChars H) :
    (fun x : ↥(⊤ : Subgroup H) => f ↑x) ∈ virtualChars ↥(⊤ : Subgroup H) := by
  classical
  set T : (H → ℂ) →ₗ[ℤ] (↥(⊤ : Subgroup H) → ℂ) :=
    LinearMap.funLeft ℤ ℂ (fun x : ↥(⊤ : Subgroup H) => (x : H)) with hT
  have hmap : Submodule.map T (virtualChars H) ≤ virtualChars ↥(⊤ : Subgroup H) := by
    rw [virtualChars_eq_span_Irr, virtualChars_eq_span_Irr, Submodule.map_span, Submodule.span_le]
    rintro g ⟨χ, hχ, rfl⟩
    exact Submodule.subset_span (irr_restrict_top hχ)
  exact hmap ⟨f, hf, rfl⟩

theorem indTop_eq_indBetween_top [Fintype G] (K : Subgroup G) (θ : ↥K → ℂ)
    (x : ↥(⊤ : Subgroup G)) : indTop K θ ↑x = indBetween K ⊤ θ x := by
  rw [indTop_apply, indBetween_apply]
  congr 1
  exact (Fintype.sum_equiv (Subgroup.topEquiv (G := G)).toEquiv _ _ (fun t => rfl)).symm

theorem isTIExtension_sigma [Fintype G] {S W₁ W₂ : Subgroup G} (hWS : W₁ ⊔ W₂ ≤ S)
    {σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)} (hσ : IsSigmaMap S W₁ W₂ σ) :
    Prep03.IsTIExtension W₁ W₂ S (⇑σ) := by
  refine ⟨fun f g => σ.map_add f g, fun c f => σ.map_smul c f, ?_, ?_, ?_, hσ.map_principal, ?_⟩
  · intro f _; exact memClassFun_of_isClassFun (hσ.isClassFun f)
  · intro f g
    rw [← cfInnerFin_eq_cfInner, ← cfInnerFin_eq_cfInner]
    exact hσ.inner_eq f g
  · intro f hf; exact hσ.maps_virtualChars f hf
  · intro f hf
    rw [hσ.eq_ind f hf, indBetween_eq_indClassFun_subgroupOf hWS]

theorem isTIExtension_omega [Fintype G] {W₁ W₂ : Subgroup G}
    {ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)} (hω : IsOmegaMap W₁ W₂ ω) :
    Prep03.IsTIExtension W₁ W₂ ⊤ (fun f x => ω f ↑x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g; funext x; simp [ω.map_add]
  · intro c f; funext x; simp [ω.map_smul]
  · intro f _
    refine memClassFun_of_isClassFun ?_
    rw [isClassFun_iff]
    intro x g
    have := (isClassFun_iff.1 (hω.isClassFun f)) (x : G) (g : G)
    simpa using this
  · intro f g
    rw [cfInner_top_eq, ← cfInnerFin_eq_cfInner, ← cfInnerFin_eq_cfInner]
    exact hω.inner_eq f g
  · intro f hf
    exact virtualChars_restrict_top (hω.maps_virtualChars f hf)
  · funext x; rw [hω.map_principal]; rfl
  · intro f hf
    funext x
    rw [hω.eq_ind f hf, indTop_eq_indBetween_top,
      indBetween_eq_indClassFun_subgroupOf (le_top : W₁ ⊔ W₂ ≤ ⊤)]

theorem sup_le_of_isWitnessedPConfiguration [Finite G] {S U W₁ W₂ : Subgroup G}
    (h : IsWitnessedPConfiguration S U W₁ W₂) : W₁ ⊔ W₂ ≤ S := by
  refine sup_le ?_ ?_
  · rw [← h.sup_commutator_W₁]; exact le_sup_right
  · exact le_trans h.le_W₂ (le_trans inf_le_left (Subgroup.map_subtype_le _))

theorem cyclicTIDiff_eq_cyclicTIset (W₁ W₂ : Subgroup G) :
    cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂ = cyclicTIset W₁ W₂ := by
  ext x; rw [mem_cyclicTIDiff, mem_cyclicTIset]

theorem indTop_eq_indClassFun [Fintype G] (K : Subgroup G) (θ : ↥K → ℂ) :
    indTop K θ = indClassFun K θ := indTop_eq_indG K θ

@[expose] noncomputable def omegaCF [Fintype G] {W₁ W₂ : Subgroup G}
    (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)) (hω : IsOmegaMap W₁ W₂ ω) :
    ↥(classFun ↥(W₁ ⊔ W₂)) →ₗ[ℂ] ↥(classFun G) :=
  LinearMap.restrict ω (p := classFun ↥(W₁ ⊔ W₂)) (q := classFun G)
    (fun f _ => memClassFun_of_isClassFun (hω.isClassFun f))

theorem coe_omegaCF [Fintype G] {W₁ W₂ : Subgroup G}
    (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)) (hω : IsOmegaMap W₁ W₂ ω)
    (f : ↥(classFun ↥(W₁ ⊔ W₂))) :
    ((omegaCF ω hω f : ↥(classFun G)) : G → ℂ) = ω (f : ↥(W₁ ⊔ W₂) → ℂ) := rfl

theorem isCyclicTIIsometry_omegaCF [Fintype G] {W₁ W₂ : Subgroup G}
    (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ)) (hω : IsOmegaMap W₁ W₂ ω) :
    IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ (omegaCF ω hω) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g
    rw [coe_omegaCF, coe_omegaCF, ← cfInnerFin_eq_cfInner, ← cfInnerFin_eq_cfInner]
    exact hω.inner_eq _ _
  · intro f hf; rw [coe_omegaCF]; exact hω.maps_virtualChars _ hf
  · apply Subtype.ext
    rw [coe_omegaCF, coe_principalClassFun, coe_principalClassFun]
    exact hω.map_principal
  · intro f hf
    rw [coe_omegaCF, hω.eq_ind _ (fun z hz => hf z (by rwa [cyclicTIDiff_eq_cyclicTIset])),
      indTop_eq_indClassFun]

theorem conj_image_inv_eq (D : Set G) (g : G) :
    (MulAut.conj g⁻¹) '' D = (fun x => g⁻¹ * x * g) '' D := by
  apply Set.image_congr'; intro x; simp [MulAut.conj]

theorem isCyclicTIPair_of_isWitnessedPConfiguration [Finite G] (hodd : Odd (Nat.card G))
    {S E W₁ W₂ : Subgroup G} (h : IsWitnessedPConfiguration S E W₁ W₂) :
    IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ := by
  have hW₂le : W₂ ≤ ⁅S, S⁆ :=
    le_trans h.le_W₂ (le_trans inf_le_right (Subgroup.commutator_le_self _))
  have hcop : (Nat.card ↥W₁).Coprime (Nat.card ↥W₂) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hW₂le)
      h.coprime_natCard_W₁_natCard_commutator
  have hcyc : IsCyclic ↥(W₁ ⊔ W₂) := by
    refine (MulEquiv.isCyclic h.isInternalDirectProduct_sup.mulEquivProd).mp ?_
    exact Group.isCyclic_prod_iff.2 ⟨h.isCyclic_W₁, h.isCyclic_W₂, hcop⟩
  refine ⟨h.ne_bot_W₁, h.ne_bot_W₂, h.coe_sup_W₁_W₂.symm, h.inf_W₁_W₂,
    fun x hx y hy => (h.commute_W₁_W₂ hx hy), hcyc, ?_, ?_, ?_⟩
  · exact hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  · rw [cyclicTIDiff_eq_cyclicTIset]
    ext g
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe]
    have hn := h.normalizer_cyclicTIset
    constructor
    · intro hg
      have hmem : g⁻¹ ∈ Subgroup.normalizer (cyclicTIset W₁ W₂) := by
        rw [Subgroup.mem_normalizer_iff_conj_image_eq, conj_image_inv_eq]; exact hg
      rw [hn] at hmem
      simpa using hmem
    · intro hg
      have hg' : g⁻¹ ∈ Subgroup.normalizer (cyclicTIset W₁ W₂) := by
        rw [hn]; exact inv_mem hg
      rw [Subgroup.mem_normalizer_iff_conj_image_eq, conj_image_inv_eq] at hg'
      exact hg'
  · intro g hg
    rw [cyclicTIDiff_eq_cyclicTIset]
    have hg' : g⁻¹ ∉ W₁ ⊔ W₂ := fun hcon => hg (by simpa using inv_mem hcon)
    have hd := h.disjoint_cyclicTIset_conj hg'
    rw [Set.disjoint_iff_inter_eq_empty, conj_image_inv_eq] at hd
    rw [Set.inter_comm]
    exact hd

theorem indBetween_eq_indClassFun_of_map [Fintype G] (L : Subgroup G) (K : Subgroup ↥L)
    (M : Subgroup G) (e : ↥K ≃* ↥M) (he : ∀ x : ↥K, ((e x : ↥M) : G) = ((x : ↥L) : G))
    (hmem : ∀ z : ↥L, ((z : G) ∈ M) ↔ z ∈ K) (θ : ↥M → ℂ) :
    indBetween M L θ = indClassFun K (θ ∘ e) := by
  classical
  funext y
  rw [indBetween_apply, indClassFun_apply]
  have hcard : Nat.card ↥M = Nat.card ↥K := (Nat.card_eq_of_bijective _ e.bijective).symm
  rw [hcard, extendSub_eq_extendByZero]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [extendByZero_apply_dite]
  have hcoe : (((t : ↥L)⁻¹ * y * t : ↥L) : G)
      = ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G) := by simp
  by_cases hz : ((t : ↥L)⁻¹ * y * t) ∈ K
  · have hz' : ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G) ∈ M := by
      rw [← hcoe]; exact (hmem _).2 hz
    rw [dif_pos hz, dif_pos hz']
    have heq : e ⟨(t : ↥L)⁻¹ * y * t, hz⟩
        = ⟨((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G), hz'⟩ := by
      apply Subtype.ext; rw [he]; exact hcoe
    simp only [Function.comp_apply, heq]
  · have hz' : ((t : ↥L) : G)⁻¹ * ((y : ↥L) : G) * ((t : ↥L) : G) ∉ M := by
      intro hcon
      rw [← hcoe] at hcon
      exact hz ((hmem _).1 hcon)
    rw [dif_neg hz, dif_neg hz']

@[expose] noncomputable def hallCoreEquiv (L : Subgroup G) :
    ↥(hallCore ↥L) ≃* ↥(hallCoreIn L) :=
  ((hallCore ↥L).equivMapOfInjective L.subtype (Subgroup.subtype_injective L)).trans
    (MulEquiv.subgroupCongr (hallCoreIn_eq L).symm)

theorem hallCoreEquiv_coe (L : Subgroup G) (x : ↥(hallCore ↥L)) :
    ((hallCoreEquiv L x : ↥(hallCoreIn L)) : G) = ((x : ↥L) : G) := rfl

theorem mem_hallCoreIn_iff (L : Subgroup G) (z : ↥L) :
    ((z : G) ∈ hallCoreIn L) ↔ z ∈ hallCore ↥L := by
  rw [hallCoreIn_eq]
  constructor
  · intro h
    exact (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective L)).1 (by simpa using h)
  · intro h
    have := Subgroup.mem_map_of_mem (L.subtype) h
    simpa using this

theorem indBetween_hallCoreIn [Fintype G] (L : Subgroup G) (θ : ↥(hallCoreIn L) → ℂ) :
    indBetween (hallCoreIn L) L θ = indClassFun (hallCore ↥L) (θ ∘ hallCoreEquiv L) :=
  indBetween_eq_indClassFun_of_map L (hallCore ↥L) (hallCoreIn L) (hallCoreEquiv L)
    (hallCoreEquiv_coe L) (mem_hallCoreIn_iff L) θ

theorem calLFam_eq_indFam [Fintype G] (L : Subgroup G) :
    calLFam L = indFam (hallCore ↥L) (Irr ↥(hallCore ↥L) \ {1}) := by
  ext f
  rw [mem_calLFam, mem_indFam]
  constructor
  · rintro ⟨θ, ⟨hθirr, hθne⟩, rfl⟩
    refine ⟨θ ∘ hallCoreEquiv L, ⟨irr_comp_mulEquiv hθirr (hallCoreEquiv L), ?_⟩,
      (indBetween_hallCoreIn L θ).symm⟩
    intro hcon
    refine hθne ?_
    funext y
    have hy : (θ ∘ hallCoreEquiv L) ((hallCoreEquiv L).symm y)
        = (1 : ↥(hallCore ↥L) → ℂ) ((hallCoreEquiv L).symm y) := by
      rw [Set.mem_singleton_iff] at hcon; rw [hcon]
    simpa using hy
  · rintro ⟨φ, ⟨hφirr, hφne⟩, rfl⟩
    refine ⟨φ ∘ (hallCoreEquiv L).symm,
      ⟨irr_comp_mulEquiv hφirr (hallCoreEquiv L).symm, ?_⟩, ?_⟩
    · intro hcon
      refine hφne ?_
      funext y
      have hy : (φ ∘ (hallCoreEquiv L).symm) (hallCoreEquiv L y)
          = (1 : ↥(hallCoreIn L) → ℂ) (hallCoreEquiv L y) := by rw [hcon]
      simpa using hy
    · rw [indBetween_hallCoreIn]
      congr 1
      funext x
      simp

theorem hallIndFamily_eq_calLFam [Fintype G] (L : Subgroup G) :
    Prep03.hallIndFamily L = calLFam L := by
  rw [calLFam_eq_indFam]
  ext f
  rw [mem_indFam]
  constructor
  · rintro ⟨θ, hθ, hne, rfl⟩; exact ⟨θ, ⟨hθ, hne⟩, rfl⟩
  · rintro ⟨θ, ⟨hθ, hne⟩, rfl⟩; exact ⟨θ, hθ, hne, rfl⟩

theorem hallSharp_eq_image (L : Subgroup G) :
    (hallCoreIn L : Set G) \ {1}
      = (fun x : ↥L => (x : G)) '' ((hallCore ↥L : Set ↥L) \ {1}) := by
  ext x
  constructor
  · rintro ⟨hx, hx1⟩
    have hxL : x ∈ L := hallCoreIn_le L hx
    refine ⟨⟨x, hxL⟩, ⟨(mem_hallCoreIn_iff L ⟨x, hxL⟩).1 hx, ?_⟩, rfl⟩
    simp only [Set.mem_singleton_iff] at hx1 ⊢
    intro hcon
    exact hx1 (by rw [← Subgroup.coe_one L, ← hcon])
  · rintro ⟨y, ⟨hy, hy1⟩, rfl⟩
    refine ⟨(mem_hallCoreIn_iff L y).2 hy, ?_⟩
    simp only [Set.mem_singleton_iff] at hy1 ⊢
    intro hcon
    exact hy1 (Subtype.ext (by rw [hcon]; rfl))

theorem coe_dadeMap_eq_tauDade [Finite G] (L : Subgroup G)
    (hD : IsDadeData L ((hallCoreIn L : Set G) \ {1}) Prep03.sigR)
    (f : ↥(CFSG.FeitThompson.dadeDomain L ((hallCoreIn L : Set G) \ {1}))) :
    ((dadeMap hD f : ↥(classFun G)) : G → ℂ) = tauDade L (f : ↥L → ℂ) := by
  rw [dadeMap_apply_coe, tauDade, extendSub_eq_extendByZero]
  rfl

theorem cfInner_nu_eta_eq_zero
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsOddOrderMinimalSimple G)
    (S L U W₁ W₂ : Subgroup G) (I J : Type u) [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (bfam : J → (↥S → ℂ))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam)
    (ν : (↥L → ℂ) → (G → ℂ)) (hν : IsCoherentDade L ν) :
    ∀ ξ ∈ calLFam L, ∀ (i : I) (j : J), cfInnerFin (ν ξ) (η i j) = 0 := by
  classical
  intro ξ hξ i j
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hconf := isPConfigSetup_of_isPBridgeData hG hdata
  obtain ⟨-, -, hsep⟩ := h₁ G hamb S U W₁ W₂ hconf L hdata.isCoatom_L hdata.isTypeI_L
  obtain ⟨-, -, -, -, -, hD, -, -, -, hIrrFam, -⟩ :=
    h₂ G hamb L hdata.isCoatom_L hdata.isTypeI_L
  have hDD : IsDadeData L ((hallCoreIn L : Set G) \ {1}) Prep03.sigR := hD
  set κ := ↑(calLFam L) with hκ
  set ζ : κ → (↥L → ℂ) := fun χ => (χ : ↥L → ℂ) with hζ
  have hrange : Set.range ζ = calLFam L := Subtype.range_coe
  obtain ⟨hadd, hvc, hiso, hcoh⟩ := hν
  have hspan : Submodule.span ℤ (Set.range ζ) = Submodule.span ℤ (calLFam L) := by rw [hrange]
  have hmem : ∀ f : ↥(Submodule.span ℤ (Set.range ζ)),
      (f : ↥L → ℂ) ∈ Submodule.span ℤ (calLFam L) := fun f => by rw [← hspan]; exact f.2
  set μ' : ↥(Submodule.span ℤ (Set.range ζ)) →+ ↥(virtualChars G) :=
    AddMonoidHom.mk' (fun f => ⟨ν (f : ↥L → ℂ), hvc _ (hmem f)⟩)
      (fun f g => Subtype.ext (hadd _ (hmem f) _ (hmem g))) with hμdef
  have hle : charSpanZero (Set.range ζ) ≤ Submodule.span ℤ (Set.range ζ) := fun f hf =>
    (mem_charSpanZero.1 hf).1
  set t : ↥(charSpanZero (Set.range ζ)) →+ ↥(virtualChars G) :=
    μ'.comp (Submodule.inclusion hle).toAddMonoidHom with htdef
  have hcoher : IsCoherentWith (Set.range ζ) t μ' := by
    refine ⟨?_, ?_⟩
    · intro f g
      have h2 := hiso _ (hmem f) _ (hmem g)
      rw [cfInnerFin_eq_cfInner, cfInnerFin_eq_cfInner] at h2
      exact h2
    · intro f; rfl
  have ht : ∀ (f : ↥(charSpanZero (Set.range ζ)))
      (hf : (f : ↥L → ℂ) ∈ CFSG.FeitThompson.dadeDomain L
        ((hallCoreIn L : Set G) \ {1})),
      ((t f : ↥(virtualChars G)) : G → ℂ)
        = ((dadeMap hDD ⟨(f : ↥L → ℂ), hf⟩ : ↥(classFun G)) : G → ℂ) := by
    intro f hf
    rw [coe_dadeMap_eq_tauDade]
    have h1 : (f : ↥L → ℂ) ∈ Submodule.span ℤ (calLFam L) := by
      rw [← hspan]; exact (mem_charSpanZero.1 f.2).1
    exact hcoh _ h1 (mem_charSpanZero.1 f.2).2
  have hW : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂ :=
    isCyclicTIPair_of_isWitnessedPConfiguration hG.odd_natCard hdata.isPConfig
  have hωiso := isCyclicTIIsometry_omegaCF ω hdata.isOmegaMap
  have hV : ∀ (F : ↥(CFSG.FeitThompson.dadeDomain L
        ((hallCoreIn L : Set G) \ {1}))),
      ∀ v ∈ cyclicTIDiff (W₁ ⊔ W₂) W₁ W₂,
        ((dadeMap hDD F : ↥(classFun G)) : G → ℂ) v = 0 := by
    intro F v hv
    rw [coe_dadeMap_eq_tauDade, tauDade_eq_tauHall]
    refine hsep (F : ↥L → ℂ) (fun x hx => (mem_dadeDomain.1 F.2).2 x hx) v ?_
    exact Or.inr (Set.mem_iUnion.2 ⟨1, ⟨v, (mem_cyclicTIDiff.1 hv).1, by simp⟩⟩)
  have hwij : w i j = hW.prodChar (α i) (β j) := by
    funext z
    have hz2 : (z : G) ∈ ((W₁ : Set G) * (W₂ : Set G)) := by rw [hW.mul_eq]; exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.1 hz2
    have hz : z = ⟨x * y, by rw [hxy]; exact z.2⟩ := Subtype.ext hxy.symm
    rw [hz, hdata.isProductCharFamily i j ⟨x, hx⟩ ⟨y, hy⟩, hW.prodChar_apply_mul]
  have hwirr : w i j ∈ Irr ↥(W₁ ⊔ W₂) := by
    rw [hwij]
    refine hW.prodChar_mem_Irr ?_ ?_
    · rw [← hdata.isIrrIndexing_W₁.2.1]; exact Set.mem_range_self _
    · rw [← hdata.isIrrIndexing_W₂.2.1]; exact Set.mem_range_self _
  set ψ : ↥(classFun ↥(W₁ ⊔ W₂)) := ⟨w i j, Irr_subset_classFun hwirr⟩ with hψ
  have key := DisjointCoherentFamilies.isOrthogonal_coherentVal_apply_of_isDadeData
    (H := hallCore ↥L) (ζ := ζ) (t := t) (μ := μ') (σ := omegaCF ω hdata.isOmegaMap)
    hG.odd_natCard hDD (hallSharp_eq_image L) (by rw [hrange, calLFam_eq_indFam])
    (by rw [hrange, ← hallIndFamily_eq_calLFam]; exact hIrrFam)
    ht hcoher hW hωiso hV ⟨ξ, by rw [hrange]; exact hξ⟩ (ψ := ψ) hwirr
  rw [isOrthogonal_iff] at key
  rw [cfInnerFin_eq_cfInner, hdata.eta_eq i j]
  rw [coherentVal_apply] at key
  convert key using 2
  · rfl
  · rw [coe_omegaCF]

theorem cfInner_indTop_tauDade_eq_zero
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u})
    (G : Type u) [Group G] [Fintype G] (hG : IsOddOrderMinimalSimple G)
    (S L U W₁ W₂ : Subgroup G) (I J : Type u) [Fintype I] [Fintype J]
    (α : I → (↥W₁ → ℂ)) (β : J → (↥W₂ → ℂ)) (i₀ : I) (j₀ : J)
    (w : I → J → (↥(W₁ ⊔ W₂) → ℂ))
    (σ : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (↥S → ℂ)) (ω : (↥(W₁ ⊔ W₂) → ℂ) →ₗ[ℂ] (G → ℂ))
    (η : I → J → (G → ℂ)) (δ : J → ℂ) (μ : J → (↥S → ℂ)) (γ : ↥S → ℂ)
    (bfam : J → (↥S → ℂ))
    (hdata : IsPBridgeData S L U W₁ W₂ α β i₀ j₀ w σ ω η δ μ γ bfam) :
    ∀ j : J, j ≠ j₀ → ∀ f : ↥L → ℂ, IsClassFun f →
      (∀ x : ↥L, (x : G) ∉ (hallCoreIn L : Set G) \ {1} → f x = 0) →
      cfInnerFin (indTop S (bfam j)) (tauDade L f) = 0 := by
  classical
  intro j hj f hf hfsupp
  have hamb : Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hconf := isPConfigSetup_of_isPBridgeData hG hdata
  obtain ⟨-, -, hsep⟩ := h₁ G hamb S U W₁ W₂ hconf L hdata.isCoatom_L hdata.isTypeI_L
  set eI := Fintype.equivFin I with heI
  set eJ := Fintype.equivFin J with heJ
  have hWS : W₁ ⊔ W₂ ≤ S := sup_le_of_isWitnessedPConfiguration hdata.isPConfig
  have hcoreS : hallCoreIn S ⊔ W₁ ≤ S :=
    sup_le (Subgroup.map_subtype_le _) (le_trans le_sup_left hWS)
  have hirr₁ := hdata.isIrrIndexing_W₁
  have hirr₂ := hdata.isIrrIndexing_W₂
  have key := h₃ G hamb S U W₁ W₂ hconf (Nat.card ↥U) (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl rfl
    (Fin (Fintype.card I)) (Fin (Fintype.card J)) inferInstance inferInstance
    (eI i₀) (eJ j₀) (fun i => α (eI.symm i)) (fun j => β (eJ.symm j))
    (fun i => by rw [← hirr₁.2.1]; exact Set.mem_range_self _)
    (fun j => by rw [← hirr₂.2.1]; exact Set.mem_range_self _)
    (fun a b hab => by
      have := hirr₁.1 hab
      simpa using this)
    (fun a b hab => by
      have := hirr₂.1 hab
      simpa using this)
    (fun χ hχ => by
      rw [← hirr₁.2.1] at hχ
      obtain ⟨i, hi⟩ := hχ
      exact ⟨eI i, by simpa using hi⟩)
    (fun χ hχ => by
      rw [← hirr₂.2.1] at hχ
      obtain ⟨jj, hjj⟩ := hχ
      exact ⟨eJ jj, by simpa using hjj⟩)
    (by simpa using hirr₁.2.2) (by simpa using hirr₂.2.2)
    (fun i jj => w (eI.symm i) (eJ.symm jj))
    (fun i jj x y z hz => by
      have hprod := hdata.isProductCharFamily (eI.symm i) (eJ.symm jj) x y (hz ▸ z.2)
      rw [← hprod]
      congr 1
      exact Subtype.ext hz)
    (⇑σ) (⇑ω) (isTIExtension_sigma hWS hdata.isSigmaMap) (isTIExtension_omega hdata.isOmegaMap)
    (fun jj => δ (eJ.symm jj)) (fun jj => μ (eJ.symm jj))
    (fun i jj => η (eI.symm i) (eJ.symm jj))
    (fun jj => hdata.delta_sign _) (fun jj => by simpa using hdata.mu_eq (eJ.symm jj))
    (fun jj => hdata.mu_irr _) (fun i jj => hdata.eta_eq _ _)
    (fun _ => γ) (fun jj => bfam (eJ.symm jj))
    (fun jj => by
      rw [hdata.gamma_eq, indBetween_eq_indClassFun_subgroupOf hcoreS]
      rfl)
    (fun jj => by simpa using hdata.b_eq (eJ.symm jj))
  obtain ⟨-, -, hrest⟩ := key
  have hjne : eJ j ≠ eJ j₀ := fun hcon => hj (eJ.injective hcon)
  obtain ⟨-, -, -, hlast⟩ := hrest (eJ j) hjne _ rfl
  obtain ⟨-, -, hsupp⟩ := hlast (eJ j) hjne
  refine cfInnerFin_eq_zero_of_support_disjoint
    (D := Prep03.sat ((Prep03.hallCoreIn S : Set G)) ∪ Prep03.sat ((W₁ ⊔ W₂ : Subgroup G) : Set G))
    ?_ ?_
  · intro x hx
    have hz := hsupp x hx
    rw [← indTop_eq_indG] at hz
    simpa using hz
  · intro x hx
    rw [tauDade_eq_tauHall]
    exact hsep f hfsupp x hx

theorem FCH_type_I_P_bridge_orthogonality
    (h₁ : Statements.FCH_type_I_P_packet_separation.{u})
    (h₂ : Statements.FCH_type_I_frobenius_coherent_family.{u})
    (h₃ : Statements.FCH_type_p_actual_bridge_remainder.{u}) :
    Statements.FCH_type_I_P_bridge_orthogonality.{u} := by
  intro G _ _ hG S L U W₁ W₂ I J _ _ α β i₀ j₀ w σ ω η δ μ γ bfam hdata ν hν φ _ _ βL _
  exact ⟨cfInner_nu_eta_eq_zero h₁ h₂ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ μ γ bfam hdata ν hν,
    cfInner_indTop_tauDade_eq_zero h₁ h₃ G hG S L U W₁ W₂ I J α β i₀ j₀ w σ ω η δ μ γ bfam hdata⟩

end CFSG.FeitThompson.Proofs

end
