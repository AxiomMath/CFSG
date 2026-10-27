module

public import CFSG.FeitThompson.Representations.UniformLocalBridgePuncturedSupportNorm
import CFSG.FeitThompson.Definitions.KappaPrimes
import CFSG.FeitThompson.Representations.BridgeNormBoundProjectionVanishes
import CFSG.FeitThompson.Representations.CoherentInducedImageVanishesMixedTI
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters
import CFSG.FeitThompson.Representations.InducedFamilyIrreducibleRowOrthogonal
import CFSG.FeitThompson.Representations.DadeInverseConstantOffExceptionalFamily
import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate Pointwise

section Transport

variable {G : Type*} [Group G] {L : Subgroup G} {K W₁ W₂ : Subgroup ↥L}

noncomputable def mapSubtypeEquiv (L : Subgroup G) (W : Subgroup ↥L) :
    ↥W ≃* ↥(W.map L.subtype) :=
  Subgroup.equivMapOfInjective W L.subtype L.subtype_injective

@[simp] theorem coe_mapSubtypeEquiv (L : Subgroup G) (W : Subgroup ↥L) (x : ↥W) :
    ((mapSubtypeEquiv L W x : ↥(W.map L.subtype)) : G) = ((x : ↥L) : G) := (rfl)

noncomputable def irrMapSubtype (L : Subgroup G) (W : Subgroup ↥L) (i : Irr ↥W) :
    Irr ↥(W.map L.subtype) :=
  ⟨(i : ↥W → ℂ) ∘ (mapSubtypeEquiv L W).symm,
    FrobeniusInduction.mem_Irr_comp_mulEquiv i.2 (mapSubtypeEquiv L W).symm⟩

theorem coe_irrMapSubtype (L : Subgroup G) (W : Subgroup ↥L) (i : Irr ↥W) :
    ((irrMapSubtype L W i : Irr ↥(W.map L.subtype)) : ↥(W.map L.subtype) → ℂ)
      = (i : ↥W → ℂ) ∘ (mapSubtypeEquiv L W).symm := (rfl)

@[simp] theorem irrMapSubtype_apply (L : Subgroup G) (W : Subgroup ↥L) (i : Irr ↥W) (x : ↥W) :
    ((irrMapSubtype L W i : Irr ↥(W.map L.subtype)) : ↥(W.map L.subtype) → ℂ)
      (mapSubtypeEquiv L W x) = (i : ↥W → ℂ) x := by
  rw [coe_irrMapSubtype]; simp

@[simp] theorem irrMapSubtype_principal (L : Subgroup G) (W : Subgroup ↥L) :
    irrMapSubtype L W (principalIrr ↥W) = principalIrr ↥(W.map L.subtype) := by
  refine Subtype.ext ?_
  rw [coe_irrMapSubtype, coe_principalIrr, coe_principalIrr]
  rfl

theorem irrMapSubtype_injective (L : Subgroup G) (W : Subgroup ↥L) :
    Function.Injective (irrMapSubtype L W) := by
  intro i j hij
  refine Subtype.ext (funext fun x => ?_)
  have := congrFun (congrArg (fun c : Irr ↥(W.map L.subtype) => (c : _ → ℂ)) hij)
    (mapSubtypeEquiv L W x)
  simpa using this

theorem image_cyclicTIset_eq (L : Subgroup G) (W₁ W₂ : Subgroup ↥L) :
    (fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) := by
  ext g
  simp only [Set.mem_image, mem_cyclicTIset, mem_cyclicTIDiff, Subgroup.mem_map]
  constructor
  · rintro ⟨x, ⟨hx, hx1, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => hx1 (by rwa [← L.subtype_injective hyx]),
      fun ⟨y, hy, hyx⟩ => hx2 (by rwa [← L.subtype_injective hyx])⟩
  · rintro ⟨⟨x, hx, rfl⟩, h1, h2⟩
    exact ⟨x, ⟨hx, fun hc => h1 ⟨x, hc, rfl⟩, fun hc => h2 ⟨x, hc, rfl⟩⟩, rfl⟩

theorem prodChar_irrMapSubtype (hL : IsCyclicTIPair (W₁ ⊔ W₂) W₁ W₂)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (i : Irr ↥W₁) (j : Irr ↥W₂) (z : ↥(W₁ ⊔ W₂)) :
    hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
        ((irrMapSubtype L W₂ j : Irr ↥(W₂.map L.subtype)) : _ → ℂ)
        (mapSubtypeEquiv L (W₁ ⊔ W₂) z)
      = hL.prodChar (i : ↥W₁ → ℂ) (j : ↥W₂ → ℂ) z := by
  obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ W₁, ∃ y ∈ W₂, x * y = (z : ↥L) := by
    have hz : (z : ↥L) ∈ (W₁ : Set ↥L) * (W₂ : Set ↥L) := by rw [hL.mul_eq]; exact z.2
    obtain ⟨x, hx, y, hy, hxy⟩ := hz
    exact ⟨x, hx, y, hy, hxy⟩
  have hzeq : z = ⟨x * y, mul_mem (hL.left_le hx) (hL.right_le hy)⟩ := Subtype.ext hxy.symm
  have hmap : mapSubtypeEquiv L (W₁ ⊔ W₂) z
      = ⟨((x : G)) * ((y : G)),
          mul_mem (hW.left_le ⟨x, hx, rfl⟩) (hW.right_le ⟨y, hy, rfl⟩)⟩ := by
    refine Subtype.ext ?_
    rw [coe_mapSubtypeEquiv, ← hxy]
    rfl
  rw [hmap, hW.prodChar_apply_mul _ _ (⟨x, hx, rfl⟩ : (x : G) ∈ W₁.map L.subtype)
      (⟨y, hy, rfl⟩ : (y : G) ∈ W₂.map L.subtype), hzeq,
    hL.prodChar_apply_mul _ _ hx hy]
  congr 1
  · have h1 : (⟨(x : G), (⟨x, hx, rfl⟩ : (x : G) ∈ W₁.map L.subtype)⟩ :
        ↥(W₁.map L.subtype)) = mapSubtypeEquiv L W₁ ⟨x, hx⟩ := Subtype.ext (rfl)
    rw [h1, irrMapSubtype_apply]
  · have h2 : (⟨(y : G), (⟨y, hy, rfl⟩ : (y : G) ∈ W₂.map L.subtype)⟩ :
        ↥(W₂.map L.subtype)) = mapSubtypeEquiv L W₂ ⟨y, hy⟩ := Subtype.ext (rfl)
    rw [h2, irrMapSubtype_apply]

theorem IsPrimeCyclicTIHyp.isCyclicTIPair_map_subtype (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅) :
    IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) where
  left_ne_bot := fun hc =>
    h.left_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hc)
  right_ne_bot := fun hc =>
    h.right_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 hc)
  mul_eq := by
    rw [Subgroup.coe_map, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul,
      ← h.coe_sup_eq_mul]
  inf_eq_bot := by
    rw [← Subgroup.map_inf_eq W₁ W₂ L.subtype L.subtype_injective, h.inf_left_right_eq_bot,
      Subgroup.map_bot]
  commute := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    exact congrArg (fun c : ↥L => (c : G)) (h.commute_left_right a ha b hb)
  isCyclic := (isCyclic_map_subtype_iff _).2 h.isCyclicTIPair.isCyclic
  odd_natCard := by
    rw [← Nat.card_congr
      (Subgroup.equivMapOfInjective (W₁ ⊔ W₂) L.subtype L.subtype_injective).toEquiv]
    exact h.isCyclicTIPair.odd_natCard
  setOf_conj_eq_self := hstab
  inter_eq_empty := hdisj

end Transport

section Domain

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L}
  [Fintype ↥(W₁ ⊔ W₂)] {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n δ : ℤ}
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {A : Set G}

theorem primeTIbridge_mem_dadeZDomain (hB : h.IsUniformBridgeData σ ζ d n δ)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIbridge σ ζ δ n i j ∈ dadeZDomain L A :=
  mem_dadeZDomain.2 ⟨h.primeTIbridge_mem_virtualChars hB i j, fun x hx =>
    h.primeTIbridge_eq_zero_of_notMem hB i hj (fun hmem => hx (hA ⟨x, hmem, rfl⟩))⟩

end Domain

section Rows

variable {L : Type*} [Group L] [Fintype L] {K W₁ W₂ : Subgroup L} [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↑(Irr ↥W₁)] {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} {ζ : L → ℂ} {d n δ : ℤ}
  {h : IsPrimeCyclicTIHyp K W₁ W₂}

theorem primeTIrow_mem_indFam_sdiff (hB : h.IsUniformBridgeData σ ζ d n δ)
    {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    h.primeTIrow σ k ∈ indFam K (Irr ↥K \ {1}) := by
  have hKn := h.normal
  rw [← h.indClassFun_primeTIres hB.isometry k]
  refine indClassFun_mem_indFam K ⟨h.primeTIres_mem_Irr hB.isometry k, ?_⟩
  intro hc
  have h1 : h.primeTIres σ k 1 = (d : ℂ) := by
    rw [IsPrimeCyclicTIHyp.primeTIres_def, resClassFun_apply,
      show ((1 : ↥K) : L) = 1 from rfl, hB.primeTIirr_one _ k hk]
  rw [Set.mem_singleton_iff] at hc
  rw [hc] at h1
  have hd1 : (1 : ℂ) = (d : ℂ) := by simpa using h1
  have hd : d = 1 := by exact_mod_cast hd1.symm
  exact absurd hB.one_lt (by omega)

theorem primeTIrow_sub_smul_zeta_mem_charSpanZero (hB : h.IsUniformBridgeData σ ζ d n δ)
    {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    h.primeTIrow σ k - (d : ℂ) • ζ ∈ charSpanZero (indFam K (Irr ↥K \ {1})) := by
  have hKn := h.normal
  refine mem_charSpanZero.2 ⟨?_, ?_⟩
  · have hMk := primeTIrow_mem_indFam_sdiff hB hk
    rw [show (d : ℂ) • ζ = d • ζ from Int.cast_smul_eq_zsmul _ _ _]
    exact sub_mem (Submodule.subset_span hMk)
      (Submodule.smul_mem _ _ (Submodule.subset_span hB.mem_indFam))
  · have hM1 : h.primeTIrow σ k 1 = (Nat.card ↥W₁ : ℂ) * (d : ℂ) := by
      rw [h.primeTIrow_one, IsPrimeCyclicTIHyp.primeTIres_def, resClassFun_apply,
        show ((1 : ↥K) : L) = 1 from rfl, hB.primeTIirr_one _ k hk]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hM1, hB.apply_one]
    ring

theorem exists_ne_ne_of_isPrimeCyclicTIHyp (h : IsPrimeCyclicTIHyp K W₁ W₂) (j : Irr ↥W₂) :
    ∃ k : Irr ↥W₂, k ≠ j ∧ k ≠ principalIrr ↥W₂ := by
  classical
  have hW := h.isCyclicTIPair
  have hcard : 3 ≤ Nat.card (Irr ↥W₂) := by
    rw [hW.card_Irr_right]; exact hW.three_le_natCard_right
  have hfin : Finite (Irr ↥W₂) := Nat.finite_of_card_ne_zero (by omega)
  by_contra hcon
  push Not at hcon
  have hsub : (Set.univ : Set (Irr ↥W₂)) ⊆ {j, principalIrr ↥W₂} := by
    intro k _
    rcases eq_or_ne k j with rfl | hkj
    · exact Or.inl rfl
    · exact Or.inr (hcon k hkj)
  have h2 : Nat.card (Irr ↥W₂) ≤ 2 := by
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_univ] at hle
    exact hle.trans ((Set.ncard_insert_le _ _).trans (by simp))
  omega

theorem cfInner_self_primeTIrow' (hB : h.IsUniformBridgeData σ ζ d n δ) (k : Irr ↥W₂) :
    cfInner (h.primeTIrow σ k) (h.primeTIrow σ k) = (Nat.card ↥W₁ : ℂ) :=
  h.cfInner_self_primeTIrow hB.isometry k

theorem cfInner_primeTIbridge_primeTIrow_eq_zero (hB : h.IsUniformBridgeData σ ζ d n δ)
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hkj : k ≠ j) (hk0 : k ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ δ n i j) (h.primeTIrow σ k) = 0 := by
  classical
  rw [h.cfInner_primeTIbridge_primeTIrow hB i j k, if_neg (fun hc => hkj hc.symm),
    if_neg (fun hc => hk0 hc.symm)]
  ring

theorem cfInner_primeTIbridge_test (hB : h.IsUniformBridgeData σ ζ d n δ)
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hkj : k ≠ j) (hk0 : k ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ δ n i j) (h.primeTIrow σ k - (d : ℂ) • ζ)
      = (d : ℂ) * (n : ℂ) := by
  rw [cfInner_sub_right, cfInner_smul_right,
    cfInner_primeTIbridge_primeTIrow_eq_zero hB i hkj hk0,
    h.cfInner_primeTIbridge_zeta hB i j]
  simp

end Rows

theorem sq_le_mul_of_cfInner_eq_intCast {X : Type*} [Fintype X] {f g : X → ℂ} {c p q : ℤ}
    (hc : cfInner f g = (c : ℂ)) (hp : cfInner f f = (p : ℂ)) (hq : cfInner g g = (q : ℂ)) :
    c ^ 2 ≤ p * q := by
  have hcs := CauchySchwarzProjection.norm_classFunInner_sq_le_re f g
  rw [classFunInner_eq_cfInner, classFunInner_eq_cfInner, classFunInner_eq_cfInner,
    hc, hp, hq] at hcs
  simp only [Complex.intCast_re] at hcs
  rw [Complex.norm_intCast] at hcs
  have hR : ((c ^ 2 : ℤ) : ℝ) ≤ ((p * q : ℤ) : ℝ) := by
    push_cast
    calc ((c : ℝ)) ^ 2 = |(c : ℝ)| ^ 2 := (sq_abs _).symm
      _ ≤ (p : ℝ) * (q : ℝ) := hcs
  exact_mod_cast hR

structure IsUniformBridgeCoherenceData {G : Type*} [Group G] [Fintype G] {L : Subgroup G}
    [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L)
    (ζ : ↥L → ℂ) (d n δ : ℤ) (A : Set G) (T : G → Subgroup G)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G) : Prop where
  local_data : h.IsUniformBridgeData σ ζ d n δ
  odd : Odd (Nat.card G)
  isDadeData : IsDadeData L A T
  image_subset : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A
  isCyclicTIPair :
    IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
  omega_isometry : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
    (W₂.map L.subtype) ω
  nu_inner : ∀ f g : Submodule.span ℤ (indFam K (Irr ↥K \ {1})),
    cfInner (ν f : G → ℂ) (ν g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ)
  nu_eq_tau : ∀ (f : Submodule.span ℤ (indFam K (Irr ↥K \ {1}))) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap isDadeData F : classFun G) : G → ℂ)

section Span

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype ↥L]

theorem span_indFam_le_virtualChars (K : Subgroup ↥L) [K.Normal] :
    Submodule.span ℤ (indFam K (Irr ↥K \ {1})) ≤ virtualChars ↥L :=
  Submodule.span_le.2 ((indFam_mono K Set.sdiff_subset).trans
    (NormalInducedFamily.indFam_subset_virtualChars K))

end Span

namespace IsUniformBridgeCoherenceData

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d n δ : ℤ} {A : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G}
  (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)

noncomputable def tauBridge (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  ((dadeZMap hC.isDadeData
      ⟨h.primeTIbridge σ ζ δ n i j,
        primeTIbridge_mem_dadeZDomain hC.local_data hC.image_subset i hj⟩ :
    charSpanZero (Irr G)) : G → ℂ)

omit [Fintype ↑(Irr ↥W₁)] in
theorem tauBridge_def (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridge i hj = ((dadeZMap hC.isDadeData
      ⟨h.primeTIbridge σ ζ δ n i j,
        primeTIbridge_mem_dadeZDomain hC.local_data hC.image_subset i hj⟩ :
    charSpanZero (Irr G)) : G → ℂ) := (rfl)

omit [Fintype ↑(Irr ↥W₁)] in
theorem cfInner_self_tauBridge (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridge i hj) (hC.tauBridge i hj) = 2 + (n : ℂ) ^ 2 := by
  rw [tauBridge, cfInner_dadeZMap]
  exact h.cfInner_self_primeTIbridge hC.local_data i hj

omit [Fintype ↑(Irr ↥W₁)] in
theorem tauBridge_mem_virtualChars (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : hC.tauBridge i hj ∈ virtualChars G :=
  dadeZMap_mem_virtualChars hC.isDadeData _

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem mem_dadeZDomain_of_mem_charSpanZero {f : ↥L → ℂ}
    (hf : f ∈ charSpanZero (indFam K (Irr ↥K \ {1}))) : f ∈ dadeZDomain L A := by
  obtain ⟨hfspan, hf1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeZDomain.2 ⟨span_indFam_le_virtualChars K hfspan, fun y hy => ?_⟩
  by_cases hyK : y ∈ K
  · have hy1 : y = 1 := by
      by_contra hne
      exact hy (hC.image_subset ⟨y, mem_primeTIbridgeSupport_of_mem_of_ne_one hyK hne, rfl⟩)
    rw [hy1]; exact hf1
  · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem K
      (indFam_mono K Set.sdiff_subset) hfspan hyK

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem cfInner_tauBridge_nu (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero (indFam K (Irr ↥K \ {1}))) :
    cfInner (hC.tauBridge i hj) (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = cfInner (h.primeTIbridge σ ζ δ n i j) f := by
  have hfZ : f ∈ dadeZDomain L A := hC.mem_dadeZDomain_of_mem_charSpanZero hf
  have hnu : (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = ((dadeZMap hC.isDadeData ⟨f, hfZ⟩ : charSpanZero (Irr G)) : G → ℂ) := by
    rw [coe_dadeZMap]
    exact hC.nu_eq_tau _ ⟨f, mem_dadeDomain_of_mem_dadeZDomain hfZ⟩ rfl
  rw [tauBridge, hnu, cfInner_dadeZMap]

noncomputable def nuZeta (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν) : G → ℂ :=
  (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ)

theorem nuZeta_def : hC.nuZeta
    = (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ) := (rfl)

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem cfInner_self_nuZeta : cfInner hC.nuZeta hC.nuZeta = 1 := by
  rw [nuZeta, hC.nu_inner]
  exact cfInner_self_of_mem_Irr hC.local_data.mem_Irr

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem nuZeta_mem_virtualChars : hC.nuZeta ∈ virtualChars G :=
  (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩).2

noncomputable def nuRow (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)
    {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) : G → ℂ :=
  (ν ⟨h.primeTIrow σ k, Submodule.subset_span
    (primeTIrow_mem_indFam_sdiff hC.local_data hk)⟩ : G → ℂ)

include hC in
theorem cfInner_self_nuRow {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    cfInner (hC.nuRow hk) (hC.nuRow hk) = (Nat.card ↥W₁ : ℂ) := by
  rw [nuRow, hC.nu_inner]
  exact h.cfInner_self_primeTIrow hC.local_data.isometry k

include hC in
theorem nuRow_sub_smul_nuZeta {k : Irr ↥W₂} (hk : k ≠ principalIrr ↥W₂) :
    hC.nuRow hk - (d : ℂ) • hC.nuZeta
      = (ν ⟨h.primeTIrow σ k - (d : ℂ) • ζ,
          charSpanZero_le _ (primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hk)⟩
        : G → ℂ) := by
  have hMk : h.primeTIrow σ k ∈ indFam K (Irr ↥K \ {1}) :=
    primeTIrow_mem_indFam_sdiff hC.local_data hk
  have hkey : (⟨h.primeTIrow σ k - (d : ℂ) • ζ,
      charSpanZero_le _ (primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hk)⟩ :
        Submodule.span ℤ (indFam K (Irr ↥K \ {1})))
      = ⟨h.primeTIrow σ k, Submodule.subset_span hMk⟩
        - d • ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ := by
    refine Subtype.ext ?_
    simp only [Submodule.coe_sub, SetLike.val_smul]
    rw [show (d : ℂ) • ζ = d • ζ from Int.cast_smul_eq_zsmul _ _ _]
  rw [hkey, map_sub, map_zsmul, nuRow, nuZeta]
  simp only [Submodule.coe_sub, SetLike.val_smul]
  rw [show (d : ℂ) • (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ)
    = d • (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ) from
      Int.cast_smul_eq_zsmul _ _ _]

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem cfInner_tauBridge_nuZeta (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridge i hj) hC.nuZeta = -(n : ℂ) := by
  classical
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  obtain ⟨c, hc⟩ := exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (hC.tauBridge_mem_virtualChars i hj))
    (mem_span_Irr_of_mem_virtualChars hC.nuZeta_mem_virtualChars)
  set a : ℤ := c + n with ha
  obtain ⟨k, hkj, hk0⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h j
  have hb := primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hk0
  have hcoh : cfInner (hC.tauBridge i hj) (hC.nuRow hk0 - (d : ℂ) • hC.nuZeta)
      = (d : ℂ) * (n : ℂ) := by
    rw [hC.nuRow_sub_smul_nuZeta hk0, hC.cfInner_tauBridge_nu i hj hb]
    exact cfInner_primeTIbridge_test hC.local_data i hkj hk0
  have hrow : cfInner (hC.tauBridge i hj) (hC.nuRow hk0) = ((d * a : ℤ) : ℂ) := by
    rw [cfInner_sub_right, cfInner_smul_right] at hcoh
    rw [ha]; push_cast; rw [← hc]
    simp only [map_intCast] at hcoh
    linear_combination hcoh
  have hbound : (d * a) ^ 2 ≤ (n ^ 2 + 2) * (Nat.card ↥W₁ : ℤ) :=
    sq_le_mul_of_cfInner_eq_intCast hrow
      (p := n ^ 2 + 2) (by rw [hC.cfInner_self_tauBridge i hj]; push_cast; ring)
      (q := (Nat.card ↥W₁ : ℤ)) (by rw [hC.cfInner_self_nuRow hk0]; push_cast; ring)
  have hd : d = n * (Nat.card ↥W₁ : ℤ) + δ := by
    have hsub := hC.local_data.sub_eq; omega
  have hm3 : 3 ≤ (Nat.card ↥W₁ : ℤ) := by
    have h3 := h.isCyclicTIPair.three_le_natCard_left; exact_mod_cast h3
  have ha0 : a = 0 :=
    eq_zero_of_sq_mul_sq_le_of_eq_mul_add hm3 hC.local_data.two_le hC.local_data.sign hd
      (by rw [← mul_pow]; exact hbound)
  have hcn : c = -n := by omega
  rw [hc, hcn]
  push_cast
  ring

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem star_zeta_mem_indFam : star ζ ∈ indFam K (Irr ↥K \ {1}) :=
  NormalInducedFamily.star_mem_of_mem rfl hC.local_data.mem_indFam

noncomputable def nuStarZeta (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν) : G → ℂ :=
  (ν ⟨star ζ, Submodule.subset_span hC.star_zeta_mem_indFam⟩ : G → ℂ)

omit [Fintype ↑(Irr ↥W₁)] in
theorem nuStarZeta_def : hC.nuStarZeta
    = (ν ⟨star ζ, Submodule.subset_span hC.star_zeta_mem_indFam⟩ : G → ℂ) := (rfl)

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem zeta_sub_star_mem_charSpanZero :
    ζ - star ζ ∈ charSpanZero (indFam K (Irr ↥K \ {1})) := by
  refine mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span hC.local_data.mem_indFam)
    (Submodule.subset_span hC.star_zeta_mem_indFam), ?_⟩
  simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, hC.local_data.apply_one]
  simp

include hC in
theorem nuZeta_sub_nuStarZeta :
    hC.nuZeta - hC.nuStarZeta
      = (ν ⟨ζ - star ζ, charSpanZero_le _ hC.zeta_sub_star_mem_charSpanZero⟩ : G → ℂ) := by
  have hsplit : (⟨ζ - star ζ, charSpanZero_le _ hC.zeta_sub_star_mem_charSpanZero⟩ :
      Submodule.span ℤ (indFam K (Irr ↥K \ {1})))
    = ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩
      - ⟨star ζ, Submodule.subset_span hC.star_zeta_mem_indFam⟩ := rfl
  rw [hsplit, map_sub, hC.nuZeta_def, hC.nuStarZeta_def, Submodule.coe_sub]

include hC in
theorem cfInner_primeTIbridge_star_zeta (i : Irr ↥W₁) (j : Irr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ δ n i j) (star ζ) = 0 := by
  have hKn := h.normal
  have hsub : indFam K (Irr ↥K \ {1}) ⊆ indFam K (Irr ↥K) := indFam_mono K Set.sdiff_subset
  have hstarIrr : star ζ ∈ Irr ↥L := star_mem_Irr hC.local_data.mem_Irr
  have hstarne : star ζ ≠ ζ := NormalInducedFamily.star_ne_self_of_odd hC.odd rfl
    hC.local_data.mem_indFam hC.local_data.mem_Irr
  have h0 : ∀ m : Irr ↥W₂, cfInner (h.primeTIirr σ i m) (star ζ) = 0 := by
    intro m
    have hz := h.cfInner_primeTIirr_eq_zero_of_mem_indFam hC.local_data.isometry
      (hsub hC.star_zeta_mem_indFam) hstarIrr i m
    rw [← conj_cfInner, hz, map_zero]
  have hz : cfInner ζ (star ζ) = 0 :=
    cfInner_eq_zero_of_mem_Irr hC.local_data.mem_Irr hstarIrr (Ne.symm hstarne)
  rw [h.cfInner_primeTIbridge_left, h0 j, h0 (principalIrr ↥W₂), hz]
  ring

include hC in
theorem cfInner_tauBridge_nuStarZeta (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : cfInner (hC.tauBridge i hj) hC.nuStarZeta = 0 := by
  have hdiff : cfInner (hC.tauBridge i hj) (hC.nuZeta - hC.nuStarZeta) = -(n : ℂ) := by
    rw [hC.nuZeta_sub_nuStarZeta,
      hC.cfInner_tauBridge_nu i hj hC.zeta_sub_star_mem_charSpanZero, cfInner_sub_right,
      h.cfInner_primeTIbridge_zeta hC.local_data i j,
      hC.cfInner_primeTIbridge_star_zeta i j]
    ring
  rw [cfInner_sub_right, hC.cfInner_tauBridge_nuZeta i hj] at hdiff
  linear_combination -hdiff

noncomputable def tauBridgeCorrected
    (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  hC.tauBridge i hj + (n : ℂ) • hC.nuZeta

omit [Fintype ↑(Irr ↥W₁)] in
theorem tauBridgeCorrected_def (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridgeCorrected i hj = hC.tauBridge i hj + (n : ℂ) • hC.nuZeta := (rfl)

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem tauBridgeCorrected_mem_virtualChars (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : hC.tauBridgeCorrected i hj ∈ virtualChars G := by
  rw [tauBridgeCorrected_def, show (n : ℂ) • hC.nuZeta = n • hC.nuZeta from
    Int.cast_smul_eq_zsmul _ _ _]
  exact add_mem (hC.tauBridge_mem_virtualChars i hj)
    (Submodule.smul_mem _ _ hC.nuZeta_mem_virtualChars)

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem cfInner_self_tauBridgeCorrected (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hC.tauBridgeCorrected i hj) (hC.tauBridgeCorrected i hj) = 2 := by
  have hzn : cfInner hC.nuZeta (hC.tauBridge i hj) = -(n : ℂ) := by
    rw [← conj_cfInner, hC.cfInner_tauBridge_nuZeta i hj]; simp
  rw [tauBridgeCorrected_def, cfInner_add_left, cfInner_add_right, cfInner_add_right,
    cfInner_smul_left, cfInner_smul_left, cfInner_smul_right, cfInner_smul_right,
    hC.cfInner_self_tauBridge i hj, hC.cfInner_tauBridge_nuZeta i hj, hzn,
    hC.cfInner_self_nuZeta]
  simp only [map_intCast]
  ring

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem cyclicTIDiff_subset_param :
    cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ⊆ A := by
  intro g hg
  rw [← image_cyclicTIset_eq] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact hC.image_subset ⟨x, mem_primeTIbridgeSupport_of_isConj hx (IsConj.refl _), rfl⟩

include hC in
theorem nuZeta_apply_eq_zero_of_mem_cyclicTIDiff {v : G}
    (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)) :
    hC.nuZeta v = 0 := by
  have hKA : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A := by
    rintro g ⟨x, ⟨hxK, hx1⟩, rfl⟩
    exact hC.image_subset ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hxK
      (by simpa using hx1), rfl⟩
  have hW2K : W₂.map L.subtype ≤ K.map L.subtype := Subgroup.map_mono h.right_le
  have hW1K : W₁.map L.subtype ⊓ K.map L.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]
  rw [hC.nuZeta_def]
  exact ExtendedDade.nu_apply_eq_zero_of_mem_cyclicTIDiff hC.odd hC.isDadeData hKA
    hC.cyclicTIDiff_subset_param rfl hC.nu_inner hC.nu_eq_tau hC.local_data.mem_indFam
    hC.local_data.mem_Irr hC.isCyclicTIPair (Subgroup.map_subtype_le _) hW2K hW1K
    hC.omega_isometry hv

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem tauBridge_apply_of_mem_cyclicTIDiff (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) {v : G}
    (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype)) :
    hC.tauBridge i hj v = h.primeTIbridge σ ζ δ n i j
      ⟨v, hC.isDadeData.mem_of_mem (hC.cyclicTIDiff_subset_param hv)⟩ := by
  rw [hC.tauBridge_def i hj]
  exact dadeZMap_apply_mem hC.isDadeData _ (hC.cyclicTIDiff_subset_param hv)

include hC in
theorem tauBridgeCorrected_apply_of_mem_cyclicTIDiff (i : Irr ↥W₁) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) (v : ↥((W₁ ⊔ W₂).map L.subtype))
    (hv : (v : G) ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype)) :
    hC.tauBridgeCorrected i hj (v : G)
      = (δ : ℂ) * (hC.isCyclicTIPair.prodChar
            ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((irrMapSubtype L W₂ j : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v
          - hC.isCyclicTIPair.prodChar
            ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((principalIrr ↥(W₂.map L.subtype) : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v) := by
  have hvL : (v : G) ∈ L := Subgroup.map_subtype_le _ v.2
  have humem : (⟨(v : G), hvL⟩ : ↥L) ∈ W₁ ⊔ W₂ := by
    obtain ⟨x, hx, hxv⟩ := v.2
    have hxe : (⟨(v : G), hvL⟩ : ↥L) = x := Subtype.ext hxv.symm
    rw [hxe]; exact hx
  set u : ↥(W₁ ⊔ W₂) := ⟨⟨(v : G), hvL⟩, humem⟩ with hu
  have hveq : mapSubtypeEquiv L (W₁ ⊔ W₂) u = v :=
    Subtype.ext (by rw [coe_mapSubtypeEquiv])
  have huV : ((u : ↥L)) ∈ cyclicTIset W₁ W₂ := by
    rw [mem_cyclicTIset]
    obtain ⟨hvW, hv1, hv2⟩ := mem_cyclicTIDiff.1 hv
    exact ⟨u.2, fun hc => hv1 ⟨(u : ↥L), hc, rfl⟩, fun hc => hv2 ⟨(u : ↥L), hc, rfl⟩⟩
  rw [tauBridgeCorrected_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    hC.nuZeta_apply_eq_zero_of_mem_cyclicTIDiff hv, mul_zero, add_zero,
    hC.tauBridge_apply_of_mem_cyclicTIDiff i hj hv,
    show (⟨(v : G), hC.isDadeData.mem_of_mem (hC.cyclicTIDiff_subset_param hv)⟩ : ↥L)
      = ((u : ↥L)) from rfl,
    h.primeTIbridge_apply_of_mem_cyclicTIset hC.local_data i hj (v := u) huV]
  congr 2
  · rw [← hveq, prodChar_irrMapSubtype h.isCyclicTIPair hC.isCyclicTIPair]
  · rw [← irrMapSubtype_principal L W₂, ← hveq,
      prodChar_irrMapSubtype h.isCyclicTIPair hC.isCyclicTIPair]

include hC in
theorem tau_primeTIbridge_eq (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    hC.tauBridge i hj
      = (δ : ℂ) • (hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
          - hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i)
              (principalIrr ↥(W₂.map L.subtype)))
        - (n : ℂ) • hC.nuZeta := by
  have hne : (irrMapSubtype L W₁ i, irrMapSubtype L W₂ j)
      ≠ (irrMapSubtype L W₁ i, principalIrr ↥(W₂.map L.subtype)) := by
    intro hc
    have h2 : irrMapSubtype L W₂ j = principalIrr ↥(W₂.map L.subtype) := congrArg Prod.snd hc
    exact hj (irrMapSubtype_injective L W₂
      (h2.trans (irrMapSubtype_principal L W₂).symm))
  have hkey := hC.isCyclicTIPair.eq_signed_sub_prodCharEta hC.omega_isometry hne
    (ε := (δ : ℂ)) (by rcases hC.local_data.sign with hd | hd <;> rw [hd] <;> norm_num)
    (mem_span_Irr_of_mem_virtualChars (hC.tauBridgeCorrected_mem_virtualChars i hj))
    (hC.cfInner_self_tauBridgeCorrected i hj)
    (fun v hv => hC.tauBridgeCorrected_apply_of_mem_cyclicTIDiff i hj v hv)
  rw [tauBridgeCorrected_def] at hkey
  rw [← hkey]
  abel

end IsUniformBridgeCoherenceData

end CFSG.FeitThompson
