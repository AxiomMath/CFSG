module

public import CFSG.FeitThompson.Representations.LargeLinearLayerUniformBridge
public import CFSG.FeitThompson.Representations.PrimeDadePrincipalRowSmallComplement
public import CFSG.FeitThompson.Representations.DegreeZeroBridgeJoinsCoherentFamilies
public import CFSG.FeitThompson.Representations.CoherentSubfamilyCyclicArrayOrthogonal
public import CFSG.FeitThompson.Representations.PrimeFixedTIPGroupCoherence
public import CFSG.FeitThompson.Representations.CoherentReferenceImageOddNonzeroOffCore
public import CFSG.FeitThompson.Representations.FreeCentralSectionJointCoherence
public import Mathlib.Tactic.Monotonicity.Lemmas

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace TypeVTwoFamilyJoining

structure IsTypeVTwoFamilyData {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
    {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ζ : ↥L → ℂ) (d δ : ℤ) (A₀ : Set G) (T : G → Subgroup G)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (T₁ : Set (↥L → ℂ)) : Prop where
  local_data : h.IsUniformBridgeData σ ζ d 2 δ
  odd : Odd (Nat.card G)
  isDadeData : IsDadeData L A₀ T
  image_subset :
    (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀
  stabilizer_eq : {g : G | (fun x => g⁻¹ * x * g) ''
      cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
    = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G)
  inter_eq_empty : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
    (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅
  omega_isometry : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
    (W₂.map L.subtype) ω
  card_lt : Nat.card ↥W₁ < Nat.card ↥W₂
  union_eq : indFam K (Irr ↥K \ {1}) = T₁ ∪ primeTIrowFam h σ
  subset_Irr : T₁ ⊆ Irr ↥L
  star_mem : ∀ χ ∈ T₁, star χ ∈ T₁
  zeta_mem : ζ ∈ T₁
  eight_le : 8 ≤ T₁.ncard
  degree_eq : ∀ χ ∈ T₁, χ 1 = (Nat.card ↥W₁ : ℂ)

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K : Subgroup ↥L} [K.Normal] {W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d n δ : ℤ}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {A₀ : Set G} {T : G → Subgroup G} {P T₁ : Set (↥L → ℂ)}

omit [Fintype G] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)] in
theorem charSpanZero_le_dadeZDomain (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀) :
    charSpanZero P ≤ dadeZDomain L A₀ := by
  intro f hf
  obtain ⟨hfspan, hf1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeZDomain.2 ⟨span_indFam_le_virtualChars K (Submodule.span_mono hPS hfspan),
    fun x hx => ?_⟩
  by_cases hxK : (x : ↥L) ∈ K
  · have hx1 : x = 1 := by
      by_contra hne
      exact hx (hA₀ ⟨x, subset_bridgeSupport_left ⟨hxK, hne⟩, rfl⟩)
    rw [hx1]; exact hf1
  · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem K hPS hfspan hxK

noncomputable def subDadeHom (hD : IsDadeData L A₀ T) (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀) :
    charSpanZero P →+ virtualChars G :=
  (spanIrrToVirtualChars G).comp
    (((Submodule.inclusion (charSpanZero_le (Irr G))).toAddMonoidHom).comp
      ((dadeZMap hD).comp
        (Submodule.inclusion (charSpanZero_le_dadeZDomain hPS hA₀)).toAddMonoidHom))

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem coe_subDadeHom_eq_dadeZMap (hD : IsDadeData L A₀ T)
    (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f : charSpanZero P) :
    ((subDadeHom hD hPS hA₀ f : virtualChars G) : G → ℂ)
      = ((dadeZMap hD ⟨(f : ↥L → ℂ), charSpanZero_le_dadeZDomain hPS hA₀ f.2⟩ :
        charSpanZero (Irr G)) : G → ℂ) := by
  rw [subDadeHom]
  simp only [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, coe_spanIrrToVirtualChars]
  rfl

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem coe_subDadeHom (hD : IsDadeData L A₀ T) (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f : charSpanZero P) (F : dadeDomain L A₀) (hF : (F : ↥L → ℂ) = (f : ↥L → ℂ)) :
    ((subDadeHom hD hPS hA₀ f : virtualChars G) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
  have harg : (⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain
      (charSpanZero_le_dadeZDomain hPS hA₀ f.2)⟩ : dadeDomain L A₀) = F := Subtype.ext hF.symm
  rw [coe_subDadeHom_eq_dadeZMap, coe_dadeZMap, harg]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_subDadeHom (hD : IsDadeData L A₀ T) (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f g : charSpanZero P) :
    cfInner ((subDadeHom hD hPS hA₀ f : virtualChars G) : G → ℂ)
        ((subDadeHom hD hPS hA₀ g : virtualChars G) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := by
  rw [coe_subDadeHom_eq_dadeZMap, coe_subDadeHom_eq_dadeZMap, cfInner_dadeZMap]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem subDadeHom_apply_one (hD : IsDadeData L A₀ T) (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f : charSpanZero P) :
    ((subDadeHom hD hPS hA₀ f : virtualChars G) : G → ℂ) 1 = 0 := by
  rw [coe_subDadeHom_eq_dadeZMap, dadeZMap_apply_one]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem isCoherent_of_subset_Irr (hD : IsDadeData L A₀ T) (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (hPIrr : P ⊆ Irr ↥L) {e : ℂ} (hdeg : ∀ χ ∈ P, χ 1 = e) :
    IsCoherent P (subDadeHom hD hPS hA₀) :=
  isCoherent_of_forall_apply_one_eq (Set.Finite.subset finite_Irr hPIrr) hPIrr hdeg _
    (cfInner_subDadeHom hD hPS hA₀) (subDadeHom_apply_one hD hPS hA₀)

theorem isCoherent_congr {S : Set (↥L → ℂ)} {τ τ' : charSpanZero S →+ virtualChars G}
    (heq : ∀ f : charSpanZero S,
      ((τ f : virtualChars G) : G → ℂ) = ((τ' f : virtualChars G) : G → ℂ))
    (hc : IsCoherent S τ) : IsCoherent S τ' := by
  have hone : τ = τ' := AddMonoidHom.ext fun f => Subtype.ext (heq f)
  rwa [hone] at hc

theorem isCoherent_primeTIrowFam_subDadeHom (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω) :
    IsCoherent (primeTIrowFam h σ)
      (subDadeHom hD (primeTIrowFam_subset_indFam hB) hA₀) := by
  refine isCoherent_congr (τ := (spanIrrToVirtualChars G).comp (rowDadeHom hD hB hA₀)) ?_
    (isCoherent_primeTIrowFam hB hA₀ hD hstab hdisj hω)
  intro f
  have hmem : (f : ↥L → ℂ) ∈ dadeDomain L A₀ :=
    mem_dadeDomain_of_mem_dadeZDomain
      (charSpanZero_le_dadeZDomain (primeTIrowFam_subset_indFam hB) hA₀ f.2)
  rw [AddMonoidHom.comp_apply, coe_spanIrrToVirtualChars,
    coe_rowDadeHom hD hB hA₀ f ⟨(f : ↥L → ℂ), hmem⟩ rfl,
    coe_subDadeHom hD (primeTIrowFam_subset_indFam hB) hA₀ f ⟨(f : ↥L → ℂ), hmem⟩ rfl]

omit [Fintype G] [K.Normal] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_self_primeTIrow (hB : h.IsUniformBridgeData σ ζ d n δ) (j : Irr ↥W₂) :
    cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = (Nat.card ↥W₁ : ℂ) := by
  classical
  rw [cfInner_primeTIrow_primeTIrow h hB.isometry j j, if_pos rfl]

omit [Fintype G] [K.Normal] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem disjoint_of_subset_Irr (hB : h.IsUniformBridgeData σ ζ d n δ) (hT₁ : T₁ ⊆ Irr ↥L) :
    Disjoint T₁ (primeTIrowFam h σ) := by
  rw [Set.disjoint_left]
  intro f hf hf'
  obtain ⟨j, -, rfl⟩ := mem_primeTIrowFam.1 hf'
  have h1 : cfInner (h.primeTIrow σ j) (h.primeTIrow σ j) = 1 :=
    cfInner_self_of_mem_Irr (hT₁ hf)
  rw [cfInner_self_primeTIrow hB j] at h1
  have h3 : 3 ≤ Nat.card ↥W₁ := h.isCyclicTIPair.three_le_natCard_left
  have hcast : (Nat.card ↥W₁ : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact h1
  have := Nat.cast_injective (R := ℂ) hcast
  omega

omit [Fintype G] [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem conjugatesOfSet_cyclicTIset_eq (W₁ W₂ : Subgroup ↥L) :
    Group.conjugatesOfSet (cyclicTIset W₁ W₂) = cyclicTIsetConj W₁ W₂ := by
  ext x
  rw [Group.mem_conjugatesOfSet_iff, mem_cyclicTIsetConj]
  constructor
  · rintro ⟨v, hv, hc⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    exact ⟨c⁻¹, v, hv, by simpa using hc⟩
  · rintro ⟨t, v, hv, hvt⟩
    exact ⟨v, hv, isConj_iff.2 ⟨t⁻¹, by simpa using hvt⟩⟩

omit [Fintype G] [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem primeTIbridgeSupport_eq_bridgeSupport (K W₁ W₂ : Subgroup ↥L) :
    primeTIbridgeSupport K W₁ W₂ = bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ := by
  rw [primeTIbridgeSupport_eq, conjugatesOfSet_cyclicTIset_eq, bridgeSupport_eq]

omit [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↑(Irr ↥W₁)] in
theorem coe_subDadeHom_eq_dadeMapFun (hD : IsDadeData L A₀ T)
    (hPS : P ⊆ indFam K (Irr ↥K \ {1}))
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f : charSpanZero P) :
    ((subDadeHom hD hPS hA₀ f : virtualChars G) : G → ℂ)
      = dadeMapFun L A₀ T (f : ↥L → ℂ) := by
  rw [coe_subDadeHom_eq_dadeZMap, coe_dadeZMap, coe_dadeMap]

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem coe_rowDadeHom_eq_dadeMapFun (hD : IsDadeData L A₀ T)
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (f : charSpanZero (primeTIrowFam h σ)) :
    (((spanIrrToVirtualChars G).comp (rowDadeHom hD hB hA₀) f : virtualChars G) : G → ℂ)
      = dadeMapFun L A₀ T (f : ↥L → ℂ) := by
  rw [AddMonoidHom.comp_apply, coe_spanIrrToVirtualChars,
    coe_rowDadeHom hD hB hA₀ f ⟨(f : ↥L → ℂ), mem_dadeDomain_of_mem_dadeZDomain
      (charSpanZero_primeTIrowFam_le_dadeZDomain hB hA₀ f.2)⟩ rfl, coe_dadeMap]

omit [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)] in
theorem dadeMapFun_eq_coe_dadeZMap (hD : IsDadeData L A₀ T) {f : ↥L → ℂ}
    (hf : f ∈ dadeZDomain L A₀) :
    dadeMapFun L A₀ T f = ((dadeZMap hD ⟨f, hf⟩ : charSpanZero (Irr G)) : G → ℂ) := by
  rw [coe_dadeZMap, coe_dadeMap]

theorem exists_isCoherentWith_of_eq_of_coe_eq {X Y : Set (↥L → ℂ)} {tau : (↥L → ℂ) → (G → ℂ)}
    (hXY : X = Y) {τ : charSpanZero X →+ virtualChars G}
    {τ' : charSpanZero Y →+ virtualChars G}
    (hval : ∀ f, ((τ f : virtualChars G) : G → ℂ) = tau (f : ↥L → ℂ))
    (hval' : ∀ f, ((τ' f : virtualChars G) : G → ℂ) = tau (f : ↥L → ℂ))
    {ν : Submodule.span ℤ X →+ virtualChars G} (hν : IsCoherentWith X τ ν) :
    ∃ ν' : Submodule.span ℤ Y →+ virtualChars G, IsCoherentWith Y τ' ν' ∧
      ∀ (v : ↥L → ℂ) (hv : v ∈ Submodule.span ℤ X) (hv' : v ∈ Submodule.span ℤ Y),
        ((ν' ⟨v, hv'⟩ : virtualChars G) : G → ℂ)
          = ((ν ⟨v, hv⟩ : virtualChars G) : G → ℂ) := by
  subst hXY
  refine ⟨ν, ⟨hν.inner_eq, fun f => Subtype.ext ?_⟩, fun v hv hv' => rfl⟩
  rw [hν.eq_on_zero f, hval f, hval' f]

omit [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [Fintype ↑(Irr ↥W₁)] in
theorem eq_of_cfInner_eq_one {ρ χ : G → ℂ} (hρ : cfInner ρ ρ = 1) (hχ : cfInner χ χ = 1)
    (hρχ : cfInner ρ χ = 1) : ρ = χ := by
  have hz : cfInner (ρ - χ) (ρ - χ) = 0 := by
    rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, hρ, hχ, hρχ,
      ← conj_cfInner ρ χ, hρχ]
    simp
  exact sub_eq_zero.1 (cfInner_self_eq_zero.1 hz)

omit [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_primeTIbridge_primeTIrow_principal_sub
    [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] (hB : h.IsUniformBridgeData σ ζ d n δ)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ δ n i j)
        (h.primeTIrow σ (principalIrr ↥W₂) - ζ) = (n : ℂ) - (δ : ℂ) := by
  classical
  rw [cfInner_sub_right, h.cfInner_primeTIbridge_zeta hB i j,
    h.cfInner_primeTIbridge_primeTIrow hB i j (principalIrr ↥W₂), if_neg hj, if_pos rfl]
  ring

section Array
variable [Fintype ↑(Irr ↥(W₁.map L.subtype))]

omit [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_prodCharEta_principal_prodCharEtaColSum
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (i : Irr ↥(W₁.map L.subtype)) :
    cfInner (hW.prodCharEta ω i (principalIrr ↥(W₂.map L.subtype)))
        (hW.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype))) = 1 := by
  classical
  rw [hW.prodCharEtaColSum_eq_sum, cfInner_sum_right,
    Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun l _ hli => by
      rw [hW.cfInner_prodCharEta hω, if_neg (by rintro ⟨h1, -⟩; exact hli h1.symm)]),
    hW.cfInner_prodCharEta hω, if_pos ⟨rfl, rfl⟩]

omit [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_prodCharEta_prodCharEtaColSum_eq_zero
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (i : Irr ↥(W₁.map L.subtype)) {j : Irr ↥(W₂.map L.subtype)}
    (hj : j ≠ principalIrr ↥(W₂.map L.subtype)) :
    cfInner (hW.prodCharEta ω i j)
        (hW.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype))) = 0 := by
  classical
  rw [hW.prodCharEtaColSum_eq_sum, cfInner_sum_right, Finset.sum_eq_zero]
  intro l _
  rw [hW.cfInner_prodCharEta hω, if_neg (by rintro ⟨-, h2⟩; exact hj h2)]

end Array

omit [Fintype ↥L] [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem sum_prodCharEta_eq_prodCharEtaColSum
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (j : Irr ↥W₂) :
    ∑ i : Irr ↥W₁, hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
      = hW.prodCharEtaColSum ω (irrMapSubtype L W₂ j) := by
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  rw [hW.prodCharEtaColSum_eq_sum]
  exact Fintype.sum_bijective (irrMapSubtype L W₁) (irrMapSubtype_bijective L W₁) _ _ fun _ => rfl

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem primeTIrow_principal_sub_mem_dadeDomain (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀) :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ ∈ dadeDomain L A₀ :=
  mem_dadeDomain_of_mem_dadeZDomain (mem_dadeZDomain.2
    ⟨mem_virtualChars_of_mem_span_Irr
      (h.primeTIrow_sub_mem_span_Irr hB.isometry hB.mem_indFam), fun x hx =>
    h.primeTIrow_sub_apply_eq_zero hB.isometry hB.mem_indFam hB.apply_one fun hmem =>
      hx (hA₀ ⟨x, subset_bridgeSupport_left hmem, rfl⟩)⟩)

theorem exists_virtualChar_norm_one_dadeMap_primeTIrow_sub
    (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport ((K : Set ↥L) \ {1}) W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hm : Nat.card ↥W₁ < Nat.card ↥W₂) :
    ∃ χ ∈ Submodule.span ℤ (Irr G), cfInner χ χ = 1 ∧
      (∀ (i : Irr ↥(W₁.map L.subtype)) (j : Irr ↥(W₂.map L.subtype)),
        IsOrthogonal χ ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω i j)) ∧
      ((dadeMap hD ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
            primeTIrow_principal_sub_mem_dadeDomain hB hA₀⟩ : classFun G) : G → ℂ)
        = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
            (principalIrr ↥(W₂.map L.subtype)) - χ := by
  classical
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set β : ↥L → ℂ := h.primeTIrow σ (principalIrr ↥W₂) - ζ with hβ
  have hβdom : β ∈ dadeDomain L A₀ := primeTIrow_principal_sub_mem_dadeDomain hB hA₀
  set f : G → ℂ := ((dadeMap hD ⟨β, hβdom⟩ : classFun G) : G → ℂ) with hf
  have hfint : f ∈ Submodule.span ℤ (Irr G) :=
    hD.dadeMap_mem_span_Irr hβdom (h.primeTIrow_sub_mem_span_Irr hB.isometry hB.mem_indFam)
  have hfnorm : cfInner f f = (Nat.card ↥(W₁.map L.subtype) : ℂ) + 1 := by
    rw [hf, cfInner_self_dadeMap hD ⟨β, hβdom⟩,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact h.cfInner_self_primeTIrow_sub hB.isometry hB.mem_indFam hB.mem_Irr
  have hf1 : cfInner f (1 : G → ℂ) = 1 := by
    rw [hf, NormalInducedFamily.cfInner_dadeMap_one hD ⟨β, hβdom⟩]
    exact h.cfInner_primeTIrow_sub_one hB.isometry hB.mem_indFam
  have hfV : ∀ x ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), f x = 0 := by
    intro x hx
    rw [← image_cyclicTIset_eq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyA : (y : G) ∈ A₀ :=
      hA₀ ⟨y, cyclicTIsetConj_subset_bridgeSupport
        (cyclicTIset_subset_cyclicTIsetConj W₁ W₂ hy), rfl⟩
    rw [hf, dadeMap_apply_mem hD ⟨β, hβdom⟩ hyA]
    have hyK : (⟨(y : G), hD.mem_of_mem hyA⟩ : ↥L) ∉ (K : Set ↥L) \ {1} := by
      rintro ⟨hmem, -⟩
      exact h.notMem_of_mem_cyclicTIset hy (by simpa using hmem)
    simpa [hβ] using h.primeTIrow_sub_apply_eq_zero hB.isometry hB.mem_indFam hB.apply_one hyK
  have hcard : Nat.card ↥(W₁.map L.subtype) < Nat.card ↥(W₂.map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact hm
  obtain ⟨χ, hχmem, hχnorm, hχorth, hfeq⟩ :=
    hW.exists_virtualChar_norm_one_prodCharEta hω hfint hfnorm hf1 hfV hcard
  exact ⟨χ, hχmem, hχnorm, hχorth, by rw [hfeq, hW.prodCharEtaColSum_eq_sum]⟩

namespace IsTypeVTwoFamilyData

variable (hC : IsTypeVTwoFamilyData h σ ζ d δ A₀ T ω T₁)

omit [K.Normal] in
include hC in
theorem subset_indFam : T₁ ⊆ indFam K (Irr ↥K \ {1}) := by
  rw [hC.union_eq]; exact Set.subset_union_left

include hC in
theorem primeTIrowFam_subset : primeTIrowFam h σ ⊆ indFam K (Irr ↥K \ {1}) :=
  primeTIrowFam_subset_indFam hC.local_data

include hC in
theorem disjoint : Disjoint T₁ (primeTIrowFam h σ) :=
  disjoint_of_subset_Irr hC.local_data hC.subset_Irr

include hC in
theorem isCoherent_linearLayer :
    IsCoherent T₁ (subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset) :=
  isCoherent_of_subset_Irr hC.isDadeData hC.subset_indFam hC.image_subset hC.subset_Irr
    hC.degree_eq

include hC in
theorem isCoherent_rowFamily :
    IsCoherent (primeTIrowFam h σ)
      (subDadeHom hC.isDadeData hC.primeTIrowFam_subset hC.image_subset) :=
  isCoherent_primeTIrowFam_subDadeHom hC.local_data hC.image_subset hC.isDadeData
    hC.stabilizer_eq hC.inter_eq_empty hC.omega_isometry

include hC in
theorem finite_linearLayer : T₁.Finite := Set.Finite.subset finite_Irr hC.subset_Irr

omit [Fintype G] [K.Normal] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem finite_rowFamily (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) : (primeTIrowFam h σ).Finite := by
  rw [primeTIrowFam_eq_range h]
  have : Finite ↑(Irr ↥W₂) := Set.Finite.to_subtype finite_Irr
  exact Set.finite_range _

noncomputable def linFinset : Finset (↥L → ℂ) := hC.finite_linearLayer.toFinset

noncomputable def rowFinset (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) : Finset (↥L → ℂ) :=
  (finite_rowFamily h σ).toFinset

include hC in
theorem coe_linFinset : (hC.linFinset : Set (↥L → ℂ)) = T₁ := Set.Finite.coe_toFinset _

omit [Fintype G] [K.Normal] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem coe_rowFinset (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) :
    ((rowFinset h σ : Finset (↥L → ℂ)) : Set (↥L → ℂ)) = primeTIrowFam h σ :=
  Set.Finite.coe_toFinset _

include hC in
theorem coe_rowFinset_union_linFinset :
    ((rowFinset h σ ∪ hC.linFinset : Finset (↥L → ℂ)) : Set (↥L → ℂ))
      = indFam K (Irr ↥K \ {1}) := by
  rw [Finset.coe_union, coe_rowFinset, hC.coe_linFinset, Set.union_comm, ← hC.union_eq]

include hC in
theorem rowFinset_union_linFinset_subset_fullFamily :
    (rowFinset h σ ∪ hC.linFinset) ⊆ CentralSectionFullExtension.fullFamily K := by
  rw [← Finset.coe_subset, hC.coe_rowFinset_union_linFinset,
    PrimeFixedTIPGroupCoherence.coe_fullFamily_eq_indFam_sdiff K]

include hC in
theorem rowFinset_subset_fullFamily :
    rowFinset h σ ⊆ CentralSectionFullExtension.fullFamily K :=
  Finset.subset_union_left.trans hC.rowFinset_union_linFinset_subset_fullFamily

include hC in
theorem linFinset_subset_fullFamily :
    hC.linFinset ⊆ CentralSectionFullExtension.fullFamily K :=
  Finset.subset_union_right.trans hC.rowFinset_union_linFinset_subset_fullFamily

include hC in
theorem disjoint_rowFinset_linFinset : Disjoint (rowFinset h σ) hC.linFinset := by
  rw [← Finset.disjoint_coe, coe_rowFinset, hC.coe_linFinset]
  exact hC.disjoint.symm

include hC in
theorem linFinset_nonempty : hC.linFinset.Nonempty := by
  refine ⟨ζ, ?_⟩
  rw [← Finset.mem_coe, hC.coe_linFinset]
  exact hC.zeta_mem

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem rowFinset_nonempty (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) : (rowFinset h σ).Nonempty := by
  classical
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  obtain ⟨j, -, hj⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h (principalIrr ↥W₂)
  refine ⟨h.primeTIrow σ j, ?_⟩
  rw [← Finset.mem_coe, coe_rowFinset]
  exact primeTIrow_mem_primeTIrowFam hj

include hC in
theorem exists_isSubcoherent_fullFamily :
    ∃ R : (↥L → ℂ) → Finset (G → ℂ),
      IsSubcoherent (CentralSectionFullExtension.fullFamily K) (dadeMapFun L A₀ T) R := by
  obtain ⟨R, hR, -⟩ := PrimeDadeSubcoherence.exists_isSubcoherent_indFamDetect
    (ω := ω) (A₀ := A₀) (T := T) hC.odd h hC.local_data.isometry
    (H := K) h.right_le le_rfl (A := (K : Set ↥L) \ {1})
    (fun t => PrimeFixedTIPGroupCoherence.conj_image_punctured_eq K t)
    (fun y _ _ => PrimeFixedTIPGroupCoherence.centralizer_sdiff_subset_punctured K y)
    hC.image_subset hC.isDadeData hC.stabilizer_eq hC.inter_eq_empty
    hC.omega_isometry (PrimeFixedTIPGroupCoherence.coe_fullFamily_eq_indFamDetect_self K)
  exact ⟨R, hR⟩

include hC in
theorem image_primeTIbridgeSupport_subset :
    (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀ := by
  rw [primeTIbridgeSupport_eq_bridgeSupport]; exact hC.image_subset

include hC in
theorem isCyclicTIPair_map :
    IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) :=
  h.isCyclicTIPair_map_subtype hC.stabilizer_eq hC.inter_eq_empty

theorem isLargeLinearLayerData
    {ν : Submodule.span ℤ T₁ →+ virtualChars G}
    (hν : IsCoherentWith T₁ (subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset) ν) :
    LargeLinearLayer.IsLargeLinearLayerData h σ ζ d δ A₀ T ω T₁
      (subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset) ν where
  local_data := hC.local_data
  odd := hC.odd
  isDadeData := hC.isDadeData
  image_subset := hC.image_primeTIbridgeSupport_subset
  isCyclicTIPair := hC.isCyclicTIPair_map
  omega_isometry := hC.omega_isometry
  subset_indFam := hC.subset_indFam
  subset_Irr := hC.subset_Irr
  star_mem := hC.star_mem
  eight_le := hC.eight_le
  zeta_mem := hC.zeta_mem
  degree_eq := hC.degree_eq
  coherent := hν
  tau_eq := fun f F hfF =>
    coe_subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset f F hfF.symm

include hC in
theorem primeTIrow_principal_sub_mem_dadeZDomain :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ ∈ dadeZDomain L A₀ :=
  mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
    (h.primeTIrow_sub_mem_span_Irr hC.local_data.isometry hC.local_data.mem_indFam),
    fun x hx => h.primeTIrow_sub_apply_eq_zero hC.local_data.isometry
      hC.local_data.mem_indFam hC.local_data.apply_one fun hmem =>
        hx (hC.image_subset ⟨x, subset_bridgeSupport_left hmem, rfl⟩)⟩

include hC in
theorem primeTIrow_sub_smul_zeta_mem_dadeZDomain {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIrow σ j - (d : ℂ) • ζ ∈ dadeZDomain L A₀ :=
  charSpanZero_le_dadeZDomain (subset_refl (indFam K (Irr ↥K \ {1}))) hC.image_subset
    (primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hj)

include hC in
theorem cfInner_nu_prodCharEtaColSum_eq_zero
    {ν : Submodule.span ℤ T₁ →+ virtualChars G}
    (hν : IsCoherentWith T₁ (subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset) ν)
    (j : Irr ↥(W₂.map L.subtype)) :
    cfInner ((ν ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ)
      (hC.isCyclicTIPair_map.prodCharEtaColSum ω j) = 0 := by
  classical
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  have hKA : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A₀ :=
    (Set.image_mono subset_bridgeSupport_left).trans hC.image_subset
  have hVA : cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ⊆ A₀ := by
    rw [← image_cyclicTIset_eq]
    exact (Set.image_mono fun x hx => cyclicTIsetConj_subset_bridgeSupport
      (cyclicTIset_subset_cyclicTIsetConj W₁ W₂ hx)).trans hC.image_subset
  have hW2K : W₂.map L.subtype ≤ K.map L.subtype := Subgroup.map_mono h.right_le
  have hW1K : W₁.map L.subtype ⊓ K.map L.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]
  rw [hC.isCyclicTIPair_map.prodCharEtaColSum_eq_sum, cfInner_sum_right, Finset.sum_eq_zero]
  intro i _
  exact PartialCoherent.cfInner_nu_prodCharEta_eq_zero hC.odd hC.isCyclicTIPair_map hW2K hW1K
    hC.omega_isometry hC.isDadeData hKA hVA hC.subset_indFam hC.star_mem hν
    (fun f F hfF => coe_subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset f F hfF.symm)
    hC.zeta_mem (hC.subset_Irr hC.zeta_mem) i j

include hC in
theorem dadeZMap_primeTIrow_principal_sub_eq
    {ν : Submodule.span ℤ T₁ →+ virtualChars G}
    (hν : IsCoherentWith T₁ (subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset) ν) :
    ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
        hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ)
      = hC.isCyclicTIPair_map.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype))
        - ((ν ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ) := by
  classical
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  have hfinJ : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  set hL := hC.isLargeLinearLayerData hν with hLdef
  have hρ : hL.nuOf hL.zeta_mem
      = ((ν ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ) :=
    LargeLinearLayer.IsLargeLinearLayerData.nuOf_def hL hL.zeta_mem
  have hWL : hL.isCyclicTIPair = hC.isCyclicTIPair_map := rfl
  obtain ⟨χ, -, hχnorm, hχorth, hfeq⟩ :=
    exists_virtualChar_norm_one_dadeMap_primeTIrow_sub hC.local_data hC.image_subset
      hC.isDadeData hC.stabilizer_eq hC.inter_eq_empty hC.omega_isometry hC.card_lt
  have hdZ : ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
      hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ)
      = hC.isCyclicTIPair_map.prodCharEtaColSum ω
          (principalIrr ↥(W₂.map L.subtype)) - χ := by
    rw [coe_dadeZMap]
    exact hfeq
  rw [hdZ, ← hρ]
  obtain ⟨j, -, hj⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h (principalIrr ↥W₂)
  refine congrArg (fun z => hC.isCyclicTIPair_map.prodCharEtaColSum ω
    (principalIrr ↥(W₂.map L.subtype)) - z) ?_
  have hiso : cfInner (hL.tauBridge (principalIrr ↥W₁) hj)
      ((dadeZMap hL.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
          hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ)
      = cfInner (h.primeTIbridge σ ζ δ 2 (principalIrr ↥W₁) j)
        (h.primeTIrow σ (principalIrr ↥W₂) - ζ) := by
    rw [LargeLinearLayer.IsLargeLinearLayerData.tauBridge_def, cfInner_dadeZMap]
  rw [cfInner_primeTIbridge_primeTIrow_principal_sub hL.local_data (principalIrr ↥W₁) hj, hdZ,
    hL.tau_primeTIbridge_eq (principalIrr ↥W₁) hj, hWL] at hiso
  have hjmap : irrMapSubtype L W₂ j ≠ principalIrr ↥(W₂.map L.subtype) := fun hc =>
    hj (irrMapSubtype_injective L W₂ (hc.trans (irrMapSubtype_principal L W₂).symm))
  simp only [cfInner_sub_left, cfInner_sub_right, cfInner_smul_left,
    cfInner_prodCharEta_prodCharEtaColSum_eq_zero hC.isCyclicTIPair_map hC.omega_isometry _ hjmap,
    cfInner_prodCharEta_principal_prodCharEtaColSum hC.isCyclicTIPair_map hC.omega_isometry,
    hρ, hC.cfInner_nu_prodCharEtaColSum_eq_zero hν,
    show ∀ (i : Irr ↥(W₁.map L.subtype)) (l : Irr ↥(W₂.map L.subtype)),
        cfInner (hC.isCyclicTIPair_map.prodCharEta ω i l) χ = 0 from
      fun i l => by rw [← conj_cfInner, isOrthogonal_iff.1 (hχorth i l), map_zero]] at hiso
  have hone : cfInner ((ν ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ) χ = 1 := by
    push_cast at hiso ⊢
    linear_combination hiso / 2
  rw [hρ]
  refine (eq_of_cfInner_eq_one ?_ hχnorm hone).symm
  rw [← hρ]
  exact hL.cfInner_self_nuOf hL.zeta_mem

include hC in
theorem dadeZMap_primeTIrow_sub_smul_zeta_eq
    {ν : Submodule.span ℤ T₁ →+ virtualChars G}
    (hν : IsCoherentWith T₁ (subDadeHom hC.isDadeData hC.subset_indFam hC.image_subset) ν)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ j - (d : ℂ) • ζ,
        hC.primeTIrow_sub_smul_zeta_mem_dadeZDomain hj⟩ : charSpanZero (Irr G)) : G → ℂ)
      = rowEtaSum hC.isCyclicTIPair_map ω δ j
        - (d : ℂ) • ((ν ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ) := by
  classical
  set hL := hC.isLargeLinearLayerData hν with hLdef
  set hW := hC.isCyclicTIPair_map with hWdef
  have hWL : hL.isCyclicTIPair = hW := rfl
  set ρ := ((ν ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ) with hρdef
  have hρ : hL.nuOf hL.zeta_mem = ρ :=
    LargeLinearLayer.IsLargeLinearLayerData.nuOf_def hL hL.zeta_mem
  set P₀ := hW.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype)) with hP₀
  set hβ := hC.primeTIrow_principal_sub_mem_dadeZDomain with hβdef
  have key : (⟨h.primeTIrow σ j - (d : ℂ) • ζ,
        hC.primeTIrow_sub_smul_zeta_mem_dadeZDomain hj⟩ : dadeZDomain L A₀)
      = (∑ i : Irr ↥W₁, (⟨h.primeTIbridge σ ζ δ 2 i j,
            primeTIbridge_mem_dadeZDomain hL.local_data hL.image_subset i hj⟩ :
              dadeZDomain L A₀))
        + δ • (⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ, hβ⟩ : dadeZDomain L A₀) := by
    refine Subtype.ext ?_
    push_cast
    rw [sum_primeTIbridge_eq hL.local_data j,
      show (δ : ℂ) • (h.primeTIrow σ (principalIrr ↥W₂) - ζ)
        = δ • (h.primeTIrow σ (principalIrr ↥W₂) - ζ) from Int.cast_smul_eq_zsmul _ _ _]
    abel
  have hmap := congrArg (fun z : charSpanZero (Irr G) => (z : G → ℂ))
    (congrArg (dadeZMap hC.isDadeData) key)
  simp only [map_add, map_sum, map_zsmul, Submodule.coe_add, AddSubmonoidClass.coe_finsetSum,
    SetLike.val_smul] at hmap
  have hb : ∀ i : Irr ↥W₁,
      ((dadeZMap hC.isDadeData ⟨h.primeTIbridge σ ζ δ 2 i j,
          primeTIbridge_mem_dadeZDomain hL.local_data hL.image_subset i hj⟩ :
            charSpanZero (Irr G)) : G → ℂ)
        = (δ : ℂ) • (hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype)))
          - (2 : ℂ) • ρ := fun i => by
    rw [← LargeLinearLayer.IsLargeLinearLayerData.tauBridge_def hL i hj, ← hρ]
    exact hL.tau_primeTIbridge_eq i hj
  have hψ : ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ, hβ⟩ :
      charSpanZero (Irr G)) : G → ℂ) = P₀ - ρ := hC.dadeZMap_primeTIrow_principal_sub_eq hν
  have hcolj := sum_prodCharEta_eq_prodCharEtaColSum (ω := ω) hW j
  have hcol0 : ∑ i : Irr ↥W₁,
      hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype)) = P₀ := by
    rw [hP₀, ← irrMapSubtype_principal L W₂]
    exact sum_prodCharEta_eq_prodCharEtaColSum (ω := ω) hW (principalIrr ↥W₂)
  have hcard : (Fintype.card ↑(Irr ↥W₁) : ℂ) = (Nat.card ↥W₁ : ℂ) := by
    rw [← Nat.card_eq_fintype_card, h.isCyclicTIPair.card_Irr_left]
  have hd := hL.local_data.sub_eq_complex
  rw [hmap, Finset.sum_congr rfl fun i _ => hb i, hψ, rowEtaSum_def]
  funext x
  have hcj := congrFun hcolj x
  have hc0 := congrFun hcol0 x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply,
    Finset.sum_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard] at hcj hc0 ⊢
  rw [hcj, hc0]
  push_cast at hd ⊢
  linear_combination (ρ x) * hd

include hC in
theorem exists_isCoherent_indFam :
    IsCoherent (indFam K (Irr ↥K \ {1}))
      (subDadeHom hC.isDadeData (subset_refl (indFam K (Irr ↥K \ {1}))) hC.image_subset) := by
  classical
  have hfinJ : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  obtain ⟨R, hR⟩ := hC.exists_isSubcoherent_fullFamily
  obtain ⟨ν₂, hν₂, hν₂val⟩ := exists_isCoherentWith_primeTIrowFam hC.local_data hC.image_subset
    hC.isDadeData hC.stabilizer_eq hC.inter_eq_empty hC.omega_isometry
  have hrowsub : ((rowFinset h σ : Finset (↥L → ℂ)) : Set (↥L → ℂ))
      ⊆ indFam K (Irr ↥K \ {1}) := by
    rw [coe_rowFinset]; exact hC.primeTIrowFam_subset
  obtain ⟨ν₂', hν₂', hν₂'val⟩ := exists_isCoherentWith_of_eq_of_coe_eq
    (tau := dadeMapFun L A₀ T) (coe_rowFinset h σ).symm
    (coe_rowDadeHom_eq_dadeMapFun hC.isDadeData hC.local_data hC.image_subset)
    (τ' := subDadeHom hC.isDadeData hrowsub hC.image_subset)
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData hrowsub hC.image_subset f) hν₂
  obtain ⟨ν₁, hν₁⟩ := isCoherent_iff.1 hC.isCoherent_linearLayer
  have hlinsub : ((hC.linFinset : Finset (↥L → ℂ)) : Set (↥L → ℂ))
      ⊆ indFam K (Irr ↥K \ {1}) := by
    rw [hC.coe_linFinset]; exact hC.subset_indFam
  obtain ⟨ν₁', hν₁', hν₁'val⟩ := exists_isCoherentWith_of_eq_of_coe_eq
    (tau := dadeMapFun L A₀ T) hC.coe_linFinset.symm
    (coe_subDadeHom_eq_dadeMapFun hC.isDadeData hC.subset_indFam hC.image_subset)
    (τ' := subDadeHom hC.isDadeData hlinsub hC.image_subset)
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData hlinsub hC.image_subset f) hν₁
  obtain ⟨j, -, hj⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h (principalIrr ↥W₂)
  have hχmem : h.primeTIrow σ j ∈ rowFinset h σ := by
    rw [← Finset.mem_coe, coe_rowFinset]
    exact primeTIrow_mem_primeTIrowFam hj
  have hζlin : ζ ∈ (hC.linFinset : Set (↥L → ℂ)) := by
    rw [hC.coe_linFinset]; exact hC.zeta_mem
  set φ : Submodule.span ℤ ((hC.linFinset : Finset (↥L → ℂ)) : Set (↥L → ℂ)) :=
    d • ⟨ζ, Submodule.subset_span hζlin⟩ with hφ
  have hφcoe : (φ : ↥L → ℂ) = (d : ℂ) • ζ := by
    rw [hφ, SetLike.val_smul, Int.cast_smul_eq_zsmul]
  have hdeg : h.primeTIrow σ j 1 = (φ : ↥L → ℂ) 1 := by
    rw [hφcoe, primeTIrow_apply_one hC.local_data hj]
    simp only [Pi.smul_apply, smul_eq_mul, hC.local_data.apply_one]
    ring
  have hν₂val' : ((ν₂' ⟨h.primeTIrow σ j, CoherentAntirealBlock.mem_span_of_mem hχmem⟩ : virtualChars G) : G → ℂ)
      = rowEtaSum hC.isCyclicTIPair_map ω δ j := by
    rw [hν₂'val (h.primeTIrow σ j)
      (Submodule.subset_span (primeTIrow_mem_primeTIrowFam hj)) (CoherentAntirealBlock.mem_span_of_mem hχmem)]
    exact hν₂val j hj _ rfl
  have hν₁val' : ((ν₁' φ : virtualChars G) : G → ℂ)
      = (d : ℂ) • ((ν₁ ⟨ζ, Submodule.subset_span hC.zeta_mem⟩ : virtualChars G) : G → ℂ) := by
    rw [hφ, map_zsmul, SetLike.val_smul, Int.cast_smul_eq_zsmul]
    congr 1
    exact hν₁'val ζ (Submodule.subset_span hC.zeta_mem) _
  have hbridge : dadeMapFun L A₀ T (h.primeTIrow σ j - (φ : ↥L → ℂ))
      = ((ν₂' ⟨h.primeTIrow σ j, CoherentAntirealBlock.mem_span_of_mem hχmem⟩ : virtualChars G) : G → ℂ)
        - ((ν₁' φ : virtualChars G) : G → ℂ) := by
    rw [hφcoe, hν₂val', hν₁val', dadeMapFun_eq_coe_dadeZMap hC.isDadeData
      (hC.primeTIrow_sub_smul_zeta_mem_dadeZDomain hj)]
    exact hC.dadeZMap_primeTIrow_sub_smul_zeta_eq hν₁ hj
  have hstar₂ : ∀ ψ ∈ rowFinset h σ, star ψ ∈ rowFinset h σ := by
    intro ψ hψ
    rw [← Finset.mem_coe, coe_rowFinset] at hψ ⊢
    exact star_mem_primeTIrowFam hC.local_data hψ
  have hstar₁ : ∀ ψ ∈ hC.linFinset, star ψ ∈ hC.linFinset := by
    intro ψ hψ
    rw [← Finset.mem_coe, hC.coe_linFinset] at hψ ⊢
    exact hC.star_mem ψ hψ
  have hunionsub : ((rowFinset h σ ∪ hC.linFinset : Finset (↥L → ℂ)) : Set (↥L → ℂ))
      ⊆ indFam K (Irr ↥K \ {1}) := hC.coe_rowFinset_union_linFinset.le
  have hjoin := (CoherentJoin.isCoherentWith_joinHom hR hC.rowFinset_subset_fullFamily hstar₂
    (rowFinset_nonempty h σ) hν₂'
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData hrowsub hC.image_subset f)
    hC.linFinset_subset_fullFamily hstar₁ hC.linFinset_nonempty hν₁'
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData hlinsub hC.image_subset f)
    hC.disjoint_rowFinset_linFinset
    (τU := subDadeHom hC.isDadeData hunionsub hC.image_subset)
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData hunionsub hC.image_subset f)
    hχmem φ hdeg hbridge).isCoherent
  exact FreeCentralSectionJointCoherence.isCoherent_of_eq_of_coe_eq
    (tau := dadeMapFun L A₀ T) hC.coe_rowFinset_union_linFinset
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData hunionsub hC.image_subset f)
    (fun f => coe_subDadeHom_eq_dadeMapFun hC.isDadeData _ hC.image_subset f) hjoin

end IsTypeVTwoFamilyData

end TypeVTwoFamilyJoining

end CFSG.FeitThompson

end
