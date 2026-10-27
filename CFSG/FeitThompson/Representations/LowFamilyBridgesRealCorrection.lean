module

import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.PrincipalColumnProjectionNormalizedPivot
import CFSG.FeitThompson.Representations.DegreeZeroNormalInductionsPuncturedSupport
public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.PrimeDadeFourFamilyAntirealBlocks
import CFSG.FeitThompson.Representations.PSideBridgesCommonAmbientRemainder

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Rectangle

variable {G : Type*} [Group G] [Fintype G] {W W1 W2 : Subgroup G} [Fintype ↥W]
  {σ : classFun ↥W →ₗ[ℂ] classFun G}

theorem IsCyclicTIPair.eq_prodCharEta_rectangle (hW : IsCyclicTIPair W W1 W2)
    (hσ : IsCyclicTIIsometry W W1 W2 σ) {i k : Irr ↥W1} {j l : Irr ↥W2}
    (hik : i ≠ k) (hjl : j ≠ l) {f : G → ℂ}
    (hf : f ∈ Submodule.span ℤ (Irr G)) (hnorm : cfInner f f = 4)
    (hV : ∀ v : ↥W, (v : G) ∈ cyclicTIDiff W W1 W2 →
      f (v : G) = hW.prodChar (i : ↥W1 → ℂ) (j : ↥W2 → ℂ) v
          - hW.prodChar (i : ↥W1 → ℂ) (l : ↥W2 → ℂ) v
          - hW.prodChar (k : ↥W1 → ℂ) (j : ↥W2 → ℂ) v
          + hW.prodChar (k : ↥W1 → ℂ) (l : ↥W2 → ℂ) v) :
    f = hW.prodCharEta σ i j - hW.prodCharEta σ i l - hW.prodCharEta σ k j
      + hW.prodCharEta σ k l := by
  classical
  set ρ : G → ℂ := hW.prodCharEta σ i j - hW.prodCharEta σ i l - hW.prodCharEta σ k j
    + hW.prodCharEta σ k l with hρ
  have hηmem : ∀ (p : Irr ↥W1) (q : Irr ↥W2),
      hW.prodCharEta σ p q ∈ Submodule.span ℤ (Irr G) := fun p q =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hσ p q)
  have hρmem : ρ ∈ Submodule.span ℤ (Irr G) := by
    rw [hρ]
    exact add_mem (sub_mem (sub_mem (hηmem i j) (hηmem i l)) (hηmem k j)) (hηmem k l)
  set Φ : G → ℂ := f - ρ with hΦ
  have hΦmem : Φ ∈ Submodule.span ℤ (Irr G) := sub_mem hf hρmem
  have hΦcf : Φ ∈ classFun G := mem_classFun_of_mem_span_Irr hΦmem
  have hΦ0 : ∀ x ∈ cyclicTIDiff W W1 W2, Φ x = 0 := by
    intro x hx
    have hfx := hV ⟨x, cyclicTIDiff_subset hx⟩ hx
    simp only [hΦ, hρ, Pi.sub_apply, Pi.add_apply,
      hW.prodCharEta_apply_of_mem_cyclicTIDiff hσ _ _ hx, hfx]
    ring
  have hexch := hW.cfInner_prodCharEta_exchange' hσ hΦcf hΦ0 i k j l
  have hΦρ : cfInner Φ ρ = 0 := by
    rw [hρ, cfInner_add_right, cfInner_sub_right, cfInner_sub_right]
    linear_combination hexch
  have hρρ : cfInner ρ ρ = 4 := by
    have e := hW.cfInner_prodCharEta_pair hσ
    rw [hρ]
    simp only [cfInner_add_left, cfInner_add_right, cfInner_sub_left, cfInner_sub_right]
    simp only [show ∀ (p : Irr ↥W1) (q : Irr ↥W2) (p' : Irr ↥W1) (q' : Irr ↥W2),
      cfInner (hW.prodCharEta σ p q) (hW.prodCharEta σ p' q')
        = if (p, q) = (p', q') then 1 else 0 from fun p q p' q' => e (p, q) (p', q')]
    norm_num [Prod.ext_iff, hik, Ne.symm hik, hjl, Ne.symm hjl]
  have hfρ : cfInner f ρ = 4 := by
    have hsplit : f = Φ + ρ := by rw [hΦ]; ring
    rw [hsplit, cfInner_add_left, hΦρ, hρρ, zero_add]
  have hfΦ : cfInner f Φ = 0 := by
    have h1 : Φ = f - ρ := hΦ
    rw [h1, cfInner_sub_right, hnorm, hfρ, sub_self]
  have hΦf : cfInner Φ f = 0 := by rw [← conj_cfInner, hfΦ, map_zero]
  have hΦΦ : cfInner Φ Φ = 0 := by
    have h1 : Φ = f - ρ := hΦ
    nth_rewrite 2 [h1]
    rw [cfInner_sub_right, hΦf, hΦρ, sub_self]
  have hz := cfInner_self_eq_zero.1 hΦΦ
  rw [hΦ] at hz
  exact sub_eq_zero.1 hz

end Rectangle

section StarBridge

variable {G : Type*} [Group G] {L : Subgroup G} [Fintype ↥L] {K W₁ W₂ : Subgroup ↥L}
  [Fintype ↥(W₁ ⊔ W₂)] {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n : ℤ}
  {h : IsPrimeCyclicTIHyp K W₁ W₂}

theorem star_primeTIbridge (hB : h.IsUniformBridgeData σ ζ d n 1) (i : Irr ↥W₁) (j : Irr ↥W₂) :
    star (h.primeTIbridge σ ζ 1 n i j)
      = h.primeTIbridge σ ζ 1 n (starIrr i) (starIrr j) + (n : ℂ) • (ζ - star ζ) := by
  have hsign : h.primeTISign σ j = h.primeTISign σ (starIrr j) :=
    (h.primeTISign_starIrr_eq hB.isometry j).symm
  have hsign0 : h.primeTISign σ (principalIrr ↥W₂)
      = h.primeTISign σ (starIrr (principalIrr ↥W₂)) := by rw [starIrr_principalIrr]
  have hμ := star_primeTIirr h hB.isometry i j hsign
  have hμ0 := star_primeTIirr h hB.isometry i (principalIrr ↥W₂) hsign0
  rw [starIrr_principalIrr] at hμ0
  funext x
  simp only [Pi.star_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    RCLike.star_def]
  rw [IsPrimeCyclicTIHyp.primeTIbridge_apply, IsPrimeCyclicTIHyp.primeTIbridge_apply]
  have e1 : (starRingEnd ℂ) (h.primeTIirr σ i j x)
      = h.primeTIirr σ (starIrr i) (starIrr j) x := by
    have := congrFun hμ x; simpa [Pi.star_apply, RCLike.star_def] using this
  have e2 : (starRingEnd ℂ) (h.primeTIirr σ i (principalIrr ↥W₂) x)
      = h.primeTIirr σ (starIrr i) (principalIrr ↥W₂) x := by
    have := congrFun hμ0 x; simpa [Pi.star_apply, RCLike.star_def] using this
  simp only [map_sub, map_mul, map_intCast, e1, e2]
  ring

end StarBridge

namespace PrimeDadeCommonError

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [Fintype ↥(W₁ ⊔ W₂)]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ} {d n : ℤ}
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {A₀ : Set G} {T : G → Subgroup G}

omit [Fintype G] in
theorem primeTIbridge_mem_dadeDomain (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    h.primeTIbridge σ ζ 1 n i j ∈ dadeDomain L A₀ :=
  mem_dadeDomain_of_mem_dadeZDomain (primeTIbridge_mem_dadeZDomain hB hA i hj)

variable [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {S₁ : Set (↥L → ℂ)} {ν₁ : Submodule.span ℤ S₁ →+ virtualChars G}
  {τ₁ : charSpanZero S₁ →+ virtualChars G}

noncomputable def bridgeError (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G)
    (ν₁ : Submodule.span ℤ S₁ →+ virtualChars G) (hζS₁ : ζ ∈ S₁)
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
        primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ)
    - hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
    + hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype))
    + (n : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem bridgeError_apply (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hζS₁ : ζ ∈ S₁) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    bridgeError hB hA hD hW ω ν₁ hζS₁ i hj
      = ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
            primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ)
        - hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
        + hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype))
        + (n : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := (rfl)

theorem bridgeError_mem_virtualChars (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hζS₁ : ζ ∈ S₁) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    bridgeError hB hA hD hW ω ν₁ hζS₁ i hj ∈ virtualChars G := by
  have hτ : ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
        primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ) ∈ virtualChars G := by
    have hz := dadeZMap_mem_virtualChars hD ⟨h.primeTIbridge σ ζ 1 n i j,
      primeTIbridge_mem_dadeZDomain hB hA i hj⟩
    rwa [coe_dadeZMap] at hz
  have h1 := hW.prodCharEta_mem_virtualChars hω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
  have h2 := hW.prodCharEta_mem_virtualChars hω (irrMapSubtype L W₁ i)
    (principalIrr ↥(W₂.map L.subtype))
  have h3 : (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) ∈ virtualChars G :=
    (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩).2
  rw [bridgeError_apply, show (n : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)
    = n • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) from Int.cast_smul_eq_zsmul _ _ _]
  exact add_mem (add_mem (sub_mem hτ h1) h2) (Submodule.smul_mem _ _ h3)

omit [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cyclicTIDiff_subset_param
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀) :
    cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ⊆ A₀ := by
  intro g hg
  rw [← image_cyclicTIset_eq] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact hA ⟨x, mem_primeTIbridgeSupport_of_isConj hx (IsConj.refl _), rfl⟩

omit [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem primeTIbridge_sub_eq_primeTIirr_sub (i : Irr ↥W₁) (j k : Irr ↥W₂) :
    h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n i k
      = h.primeTIirr σ i j - h.primeTIirr σ i k := by
  funext x
  rw [Pi.sub_apply, IsPrimeCyclicTIHyp.primeTIbridge_apply,
    IsPrimeCyclicTIHyp.primeTIbridge_apply, Pi.sub_apply]
  ring

theorem bridgeError_eq_of_ne_principal_right (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
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
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H) {A : Set ↥L}
    (hAA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hAsub : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (hζS₁ : ζ ∈ S₁) (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (hk : k ≠ principalIrr ↥W₂) :
    bridgeError hB hA hD (h.isCyclicTIPair_map_subtype hstab hdisj) ω ν₁ hζS₁ i hj
      = bridgeError hB hA hD (h.isCyclicTIPair_map_subtype hstab hdisj) ω ν₁ hζS₁ i hk := by
  have hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1 := by
    rw [hB.primeTIirr_one i j hj, hB.primeTIirr_one i k hk]
  have hsign : h.primeTISign σ j = (1 : ℂ) := by
    have hs := hB.primeTISign_eq j hj
    simpa using hs
  have htransfer := h.dadeMap_primeTIirr_sub_eq hB.isometry hWH hAA hAsub hD hstab hdisj hω
    i hj hk hone
  rw [hsign, one_smul] at htransfer
  have hsplit : (⟨h.primeTIirr σ i j - h.primeTIirr σ i k,
        h.primeTIirr_sub_mem_dadeDomain hB.isometry hWH hAA hAsub i hj hk hone⟩ :
        dadeDomain L A₀)
      = ⟨h.primeTIbridge σ ζ 1 n i j, primeTIbridge_mem_dadeDomain hB hA i hj⟩
        - ⟨h.primeTIbridge σ ζ 1 n i k, primeTIbridge_mem_dadeDomain hB hA i hk⟩ :=
    Subtype.ext (primeTIbridge_sub_eq_primeTIirr_sub i j k).symm
  rw [hsplit, map_sub, Submodule.coe_sub] at htransfer
  rw [bridgeError_apply, bridgeError_apply]
  rw [sub_eq_iff_eq_add] at htransfer
  rw [htransfer]
  abel

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_self_primeTIbridge_sub_col (hB : h.IsUniformBridgeData σ ζ d n 1) (i : Irr ↥W₁)
    {j k : Irr ↥W₂} (hjk : j ≠ k) :
    cfInner (h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n i k)
      (h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n i k) = 2 := by
  classical
  have e := h.cfInner_primeTIirr hB.isometry
  rw [primeTIbridge_sub_eq_primeTIirr_sub]
  simp only [cfInner_sub_left, cfInner_sub_right, e]
  norm_num [hjk, Ne.symm hjk]

theorem dadeMap_primeTIbridge_sub_col_eq (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂) :
    ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
          primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ)
      - ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i k,
          primeTIbridge_mem_dadeDomain hB hA i hk⟩ : classFun G) : G → ℂ)
      = hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
        - hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k) := by
  classical
  rcases eq_or_ne j k with rfl | hjk
  · simp
  set F : dadeDomain L A₀ :=
    ⟨h.primeTIbridge σ ζ 1 n i j, primeTIbridge_mem_dadeDomain hB hA i hj⟩
      - ⟨h.primeTIbridge σ ζ 1 n i k, primeTIbridge_mem_dadeDomain hB hA i hk⟩ with hF
  have hFcoe : (F : ↥L → ℂ)
      = h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n i k := rfl
  have hsub : ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
        primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ)
      - ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i k,
        primeTIbridge_mem_dadeDomain hB hA i hk⟩ : classFun G) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
    rw [hF, map_sub]; rfl
  rw [hsub]
  have hne : (irrMapSubtype L W₁ i, irrMapSubtype L W₂ j)
      ≠ (irrMapSubtype L W₁ i, irrMapSubtype L W₂ k) := fun hc =>
    hjk (irrMapSubtype_injective L W₂ (congrArg Prod.snd hc))
  have hkey : ((dadeMap hD F : classFun G) : G → ℂ)
      = (1 : ℂ) • (hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
        - hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k)) := by
    refine hW.eq_signed_sub_prodCharEta hω hne (Or.inl rfl) ?_ ?_ ?_
    · have hvc : (F : ↥L → ℂ) ∈ Submodule.span ℤ (Irr ↥L) := by
        rw [hFcoe]
        exact sub_mem (mem_span_Irr_of_mem_virtualChars
            (h.primeTIbridge_mem_virtualChars hB i j))
          (mem_span_Irr_of_mem_virtualChars (h.primeTIbridge_mem_virtualChars hB i k))
      have hres := hD.dadeMap_mem_span_Irr F.2 hvc
      convert hres using 3
    · rw [cfInner_self_dadeMap hD F, hFcoe]
      exact cfInner_self_primeTIbridge_sub_col hB i hjk
    · intro v hv
      have hVA := cyclicTIDiff_subset_param (K := K) hA
      have hvL : (v : G) ∈ L := Subgroup.map_subtype_le _ v.2
      have humem : (⟨(v : G), hvL⟩ : ↥L) ∈ W₁ ⊔ W₂ := by
        obtain ⟨x, hx, hxv⟩ := v.2
        have hxe : (⟨(v : G), hvL⟩ : ↥L) = x := Subtype.ext hxv.symm
        rw [hxe]; exact hx
      set u : ↥(W₁ ⊔ W₂) := ⟨⟨(v : G), hvL⟩, humem⟩ with hu
      have hveq : mapSubtypeEquiv L (W₁ ⊔ W₂) u = v := Subtype.ext (by rw [coe_mapSubtypeEquiv])
      have huV : ((u : ↥L)) ∈ cyclicTIset W₁ W₂ := by
        rw [mem_cyclicTIset]
        obtain ⟨hvW, hv1, hv2⟩ := mem_cyclicTIDiff.1 hv
        exact ⟨u.2, fun hc => hv1 ⟨(u : ↥L), hc, rfl⟩, fun hc => hv2 ⟨(u : ↥L), hc, rfl⟩⟩
      rw [dadeMap_apply_mem hD F (hVA hv),
        show (⟨(v : G), hD.mem_of_mem (hVA hv)⟩ : ↥L) = ((u : ↥L)) from rfl, hFcoe]
      rw [Pi.sub_apply, h.primeTIbridge_apply_of_mem_cyclicTIset hB i hj (v := u) huV,
        h.primeTIbridge_apply_of_mem_cyclicTIset hB i hk (v := u) huV]
      rw [← hveq, prodChar_irrMapSubtype h.isCyclicTIPair hW,
        prodChar_irrMapSubtype h.isCyclicTIPair hW]
      push_cast
      ring
  rw [hkey, one_smul]

theorem bridgeError_eq_of_ne_principal_right' (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hζS₁ : ζ ∈ S₁) (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (hk : k ≠ principalIrr ↥W₂) :
    bridgeError hB hA hD hW ω ν₁ hζS₁ i hj = bridgeError hB hA hD hW ω ν₁ hζS₁ i hk := by
  have hkey := dadeMap_primeTIbridge_sub_col_eq hB hA hD hW hω i hj hk
  rw [sub_eq_iff_eq_add] at hkey
  rw [bridgeError_apply, bridgeError_apply, hkey]
  abel

omit [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem primeTIbridge_sub_eq_primeTIirr_rectangle (i k : Irr ↥W₁) (j : Irr ↥W₂) :
    h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n k j
      = h.primeTIirr σ i j - h.primeTIirr σ i (principalIrr ↥W₂)
        - h.primeTIirr σ k j + h.primeTIirr σ k (principalIrr ↥W₂) := by
  funext x
  rw [Pi.sub_apply, IsPrimeCyclicTIHyp.primeTIbridge_apply,
    IsPrimeCyclicTIHyp.primeTIbridge_apply]
  simp only [Pi.add_apply, Pi.sub_apply]
  push_cast
  ring

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_self_primeTIbridge_sub_row (hB : h.IsUniformBridgeData σ ζ d n 1)
    {i k : Irr ↥W₁} {j : Irr ↥W₂} (hik : i ≠ k) (hj : j ≠ principalIrr ↥W₂) :
    cfInner (h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n k j)
      (h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n k j) = 4 := by
  classical
  have e := h.cfInner_primeTIirr hB.isometry
  rw [primeTIbridge_sub_eq_primeTIirr_rectangle]
  simp only [cfInner_sub_left, cfInner_sub_right, cfInner_add_left, cfInner_add_right, e]
  norm_num [hik, Ne.symm hik, hj, Ne.symm hj]

theorem dadeMap_primeTIbridge_sub_row_eq (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    {i k : Irr ↥W₁} {j : Irr ↥W₂} (hik : i ≠ k) (hj : j ≠ principalIrr ↥W₂) :
    ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
          primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ)
      - ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n k j,
          primeTIbridge_mem_dadeDomain hB hA k hj⟩ : classFun G) : G → ℂ)
      = hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
        - hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype))
        - hW.prodCharEta ω (irrMapSubtype L W₁ k) (irrMapSubtype L W₂ j)
        + hW.prodCharEta ω (irrMapSubtype L W₁ k) (principalIrr ↥(W₂.map L.subtype)) := by
  classical
  set F : dadeDomain L A₀ :=
    ⟨h.primeTIbridge σ ζ 1 n i j, primeTIbridge_mem_dadeDomain hB hA i hj⟩
      - ⟨h.primeTIbridge σ ζ 1 n k j, primeTIbridge_mem_dadeDomain hB hA k hj⟩ with hF
  have hFcoe : (F : ↥L → ℂ)
      = h.primeTIbridge σ ζ 1 n i j - h.primeTIbridge σ ζ 1 n k j := rfl
  have hsub : ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
        primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ)
      - ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n k j,
        primeTIbridge_mem_dadeDomain hB hA k hj⟩ : classFun G) : G → ℂ)
      = ((dadeMap hD F : classFun G) : G → ℂ) := by
    rw [hF, map_sub]; rfl
  rw [hsub]
  have hjmap : irrMapSubtype L W₂ j ≠ principalIrr ↥(W₂.map L.subtype) := fun hc =>
    hj (irrMapSubtype_injective L W₂ (hc.trans (irrMapSubtype_principal L W₂).symm))
  have himap : irrMapSubtype L W₁ i ≠ irrMapSubtype L W₁ k := fun hc =>
    hik (irrMapSubtype_injective L W₁ hc)
  refine hW.eq_prodCharEta_rectangle hω himap hjmap ?_ ?_ ?_
  · have hvc : (F : ↥L → ℂ) ∈ Submodule.span ℤ (Irr ↥L) := by
      rw [hFcoe]
      exact sub_mem (mem_span_Irr_of_mem_virtualChars
          (h.primeTIbridge_mem_virtualChars hB i j))
        (mem_span_Irr_of_mem_virtualChars (h.primeTIbridge_mem_virtualChars hB k j))
    have hres := hD.dadeMap_mem_span_Irr F.2 hvc
    convert hres using 3
  · rw [cfInner_self_dadeMap hD F, hFcoe]
    exact cfInner_self_primeTIbridge_sub_row hB hik hj
  · intro v hv
    have hVA := cyclicTIDiff_subset_param (K := K) hA
    have hvL : (v : G) ∈ L := Subgroup.map_subtype_le _ v.2
    have humem : (⟨(v : G), hvL⟩ : ↥L) ∈ W₁ ⊔ W₂ := by
      obtain ⟨x, hx, hxv⟩ := v.2
      have hxe : (⟨(v : G), hvL⟩ : ↥L) = x := Subtype.ext hxv.symm
      rw [hxe]; exact hx
    set u : ↥(W₁ ⊔ W₂) := ⟨⟨(v : G), hvL⟩, humem⟩ with hu
    have hveq : mapSubtypeEquiv L (W₁ ⊔ W₂) u = v := Subtype.ext (by rw [coe_mapSubtypeEquiv])
    have huV : ((u : ↥L)) ∈ cyclicTIset W₁ W₂ := by
      rw [mem_cyclicTIset]
      obtain ⟨hvW, hv1, hv2⟩ := mem_cyclicTIDiff.1 hv
      exact ⟨u.2, fun hc => hv1 ⟨(u : ↥L), hc, rfl⟩, fun hc => hv2 ⟨(u : ↥L), hc, rfl⟩⟩
    rw [dadeMap_apply_mem hD F (hVA hv),
      show (⟨(v : G), hD.mem_of_mem (hVA hv)⟩ : ↥L) = ((u : ↥L)) from rfl, hFcoe]
    rw [Pi.sub_apply, h.primeTIbridge_apply_of_mem_cyclicTIset hB i hj (v := u) huV,
      h.primeTIbridge_apply_of_mem_cyclicTIset hB k hj (v := u) huV]
    rw [← hveq, prodChar_irrMapSubtype h.isCyclicTIPair hW,
      ← irrMapSubtype_principal L W₂, prodChar_irrMapSubtype h.isCyclicTIPair hW,
      prodChar_irrMapSubtype h.isCyclicTIPair hW,
      prodChar_irrMapSubtype h.isCyclicTIPair hW]
    push_cast
    ring

theorem bridgeError_eq_of_row (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hζS₁ : ζ ∈ S₁) (i k : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    bridgeError hB hA hD hW ω ν₁ hζS₁ i hj = bridgeError hB hA hD hW ω ν₁ hζS₁ k hj := by
  rcases eq_or_ne i k with rfl | hik
  · rfl
  have hkey := dadeMap_primeTIbridge_sub_row_eq hB hA hD hW hω hik hj
  rw [sub_eq_iff_eq_add] at hkey
  rw [bridgeError_apply, bridgeError_apply, hkey]
  abel

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem zeta_ne_one (hB : h.IsUniformBridgeData σ ζ d n 1) : ζ ≠ 1 := by
  intro hc
  have h1 : (1 : ℂ) = (Nat.card ↥W₁ : ℂ) := by
    have hz := hB.apply_one
    rw [hc] at hz
    simpa using hz
  have h3 := h.isCyclicTIPair.three_le_natCard_left
  have hne : (Nat.card ↥W₁ : ℂ) ≠ 1 := by
    have hc1 : (Nat.card ↥W₁) ≠ 1 := by omega
    simpa using hc1
  exact hne h1.symm

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_primeTIbridge_one (hB : h.IsUniformBridgeData σ ζ d n 1) (i : Irr ↥W₁)
    {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) [Decidable (i = principalIrr ↥W₁)] :
    cfInner (h.primeTIbridge σ ζ 1 n i j) (1 : ↥L → ℂ)
      = -(if i = principalIrr ↥W₁ then 1 else 0) := by
  classical
  have hone : (1 : ↥L → ℂ) = h.primeTIirr σ (principalIrr ↥W₁) (principalIrr ↥W₂) :=
    (h.primeTIirr_principal hB.isometry).symm
  have hz : cfInner ζ (1 : ↥L → ℂ) = 0 := by
    rw [cfInner_eq_ite_of_mem_Irr hB.mem_Irr one_mem_Irr, if_neg (zeta_ne_one hB)]
  rw [IsPrimeCyclicTIHyp.cfInner_primeTIbridge_left, hz, hone,
    h.cfInner_primeTIirr hB.isometry i (principalIrr ↥W₁) j (principalIrr ↥W₂),
    h.cfInner_primeTIirr hB.isometry i (principalIrr ↥W₁) (principalIrr ↥W₂)
      (principalIrr ↥W₂), if_neg (by simp [hj])]
  by_cases hi : i = principalIrr ↥W₁ <;> simp [hi]

omit [Fintype G] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
include h in
theorem eq_zero_of_mem_charSpanZero_of_notMem (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (f : charSpanZero S₁) (x : ↥L) (hx : (x : G) ∉ A₀) : (f : ↥L → ℂ) x = 0 := by
  have hK := h.normal
  have hfspan : (f : ↥L → ℂ) ∈ Submodule.span ℤ (indFam K (Irr ↥K \ {1})) :=
    Submodule.span_mono hS₁ (charSpanZero_le _ f.2)
  by_cases hxK : x ∈ K
  · have hx1 : x = 1 := by
      by_contra hne
      exact hx (hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hxK hne, rfl⟩)
    rw [hx1]
    exact charSpanZero_apply_one f
  · exact NormalInducedFamily.eq_zero_of_mem_span_indFam_of_notMem K
      (indFam_mono K Set.sdiff_subset) hfspan hxK

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_nu_one (hodd : Odd (Nat.card G)) (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁)
    (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζS₁ : ζ ∈ S₁) :
    cfInner (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) (1 : G → ℂ) = 0 := by
  have hK := h.normal
  have hSD : S₁ ⊆ indFamDetect K (⊤ : Subgroup ↥K) :=
    hS₁.trans (PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K)
  have hS0 := eq_zero_of_mem_charSpanZero_of_notMem (h := h) hS₁ hA
  have hρ : (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) ∈ signedIrr G :=
    CoherentCore.nu_mem_signedIrr hodd hD hSD hS₁star hν₁.inner_eq hS0 hτ₁ hζS₁ hB.mem_Irr
  have hnr : star (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)
      ≠ (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) :=
    CoherentCore.star_nu_ne hodd hD hSD hS₁star hν₁.inner_eq hS0 hτ₁ hζS₁ hB.mem_Irr
  obtain ⟨ε, hε, χ, hχ, hval⟩ := mem_signedIrr_iff_exists_sign.1 hρ
  have hχ1 : χ ≠ 1 := by
    intro hc
    apply hnr
    rw [hval, hc]
    have hstarε : star ε = ε := by rcases hε with rfl | rfl <;> simp
    rw [star_smul, hstarε]
    congr 1
    funext x
    simp
  rw [hval, cfInner_smul_left, cfInner_eq_ite_of_mem_Irr hχ one_mem_Irr, if_neg hχ1, mul_zero]

theorem isOrthogonal_bridgeError_one (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζS₁ : ζ ∈ S₁) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    IsOrthogonal (bridgeError hB hA hD hW ω ν₁ hζS₁ i hj) 1 := by
  classical
  have hη00 : (1 : G → ℂ)
      = hW.prodCharEta ω (principalIrr ↥(W₁.map L.subtype))
          (principalIrr ↥(W₂.map L.subtype)) := (hW.prodCharEta_principal hω).symm
  have hτrec : cfInner ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
        primeTIbridge_mem_dadeDomain hB hA i hj⟩ : classFun G) : G → ℂ) (1 : G → ℂ)
      = -(if i = principalIrr ↥W₁ then 1 else 0) := by
    rw [NormalInducedFamily.cfInner_dadeMap_one hD]
    exact cfInner_primeTIbridge_one hB i hj
  have hηij : cfInner (hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j))
      (1 : G → ℂ) = 0 := by
    rw [hη00, hW.cfInner_prodCharEta_pair hω (irrMapSubtype L W₁ i, irrMapSubtype L W₂ j)
      (principalIrr ↥(W₁.map L.subtype), principalIrr ↥(W₂.map L.subtype)), if_neg]
    intro hc
    have h2 : irrMapSubtype L W₂ j = principalIrr ↥(W₂.map L.subtype) := congrArg Prod.snd hc
    exact hj (irrMapSubtype_injective L W₂ (h2.trans (irrMapSubtype_principal L W₂).symm))
  have hηi0 : cfInner (hW.prodCharEta ω (irrMapSubtype L W₁ i)
      (principalIrr ↥(W₂.map L.subtype))) (1 : G → ℂ)
      = (if i = principalIrr ↥W₁ then 1 else 0) := by
    rw [hη00, ← irrMapSubtype_principal L W₂,
      hW.cfInner_prodCharEta_pair hω (irrMapSubtype L W₁ i, irrMapSubtype L W₂ (principalIrr ↥W₂))
        (principalIrr ↥(W₁.map L.subtype), irrMapSubtype L W₂ (principalIrr ↥W₂))]
    by_cases hi : i = principalIrr ↥W₁
    · rw [if_pos, if_pos hi]
      rw [hi, irrMapSubtype_principal]
    · rw [if_neg, if_neg hi]
      intro hc
      have h1 : irrMapSubtype L W₁ i = principalIrr ↥(W₁.map L.subtype) := congrArg Prod.fst hc
      exact hi (irrMapSubtype_injective L W₁ (h1.trans (irrMapSubtype_principal L W₁).symm))
  have hν := cfInner_nu_one (h := h) hodd hB hS₁ hA hD hS₁star hν₁ hτ₁ hζS₁
  rw [isOrthogonal_iff, bridgeError_apply, cfInner_add_left, cfInner_add_left,
    cfInner_sub_left, cfInner_smul_left, hτrec, hηij, hηi0, hν]
  ring

omit [Fintype G] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem zeta_sub_star_mem_dadeDomain (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁) :
    ζ - star ζ ∈ dadeDomain L A₀ := by
  have hmem : ζ - star ζ ∈ charSpanZero S₁ := by
    refine mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span hζS₁)
      (Submodule.subset_span (hS₁star ζ hζS₁)), ?_⟩
    simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def, hB.apply_one]
    simp
  refine mem_dadeDomain.2 ⟨sub_mem (Irr_subset_classFun hB.mem_Irr)
    (star_mem_classFun (Irr_subset_classFun hB.mem_Irr)), ?_⟩
  exact fun x hx => eq_zero_of_mem_charSpanZero_of_notMem (h := h) hS₁ hA ⟨_, hmem⟩ x hx

theorem star_bridgeError_principal_left (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζS₁ : ζ ∈ S₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    star (bridgeError hB hA hD hW ω ν₁ hζS₁ (principalIrr ↥W₁) hj)
      = bridgeError hB hA hD hW ω ν₁ hζS₁ (principalIrr ↥W₁)
          (h.starIrr_ne_principalIrr_right hj) := by
  classical
  have hK := h.normal
  have hSD : S₁ ⊆ indFamDetect K (⊤ : Subgroup ↥K) :=
    hS₁.trans (PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K)
  have hS0 := eq_zero_of_mem_charSpanZero_of_notMem (h := h) hS₁ hA
  have hνstar : (ν₁ ⟨star ζ, Submodule.subset_span (hS₁star ζ hζS₁)⟩ : G → ℂ)
      = star (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) :=
    CoherentCore.nu_star_eq hodd hD hSD hS₁star hν₁.inner_eq hS0 hτ₁ hζS₁ hB.mem_Irr
  set Θ : dadeDomain L A₀ :=
    ⟨ζ - star ζ, zeta_sub_star_mem_dadeDomain (h := h) hB hS₁ hA hS₁star hζS₁⟩ with hΘ
  have hτΘ : ((dadeMap hD Θ : classFun G) : G → ℂ)
      = (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)
        - star (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
    have hsplit : (⟨ζ - star ζ, sub_mem (Submodule.subset_span hζS₁)
          (Submodule.subset_span (hS₁star ζ hζS₁))⟩ : Submodule.span ℤ S₁)
        = ⟨ζ, Submodule.subset_span hζS₁⟩
          - ⟨star ζ, Submodule.subset_span (hS₁star ζ hζS₁)⟩ := rfl
    have hkey := hτ₁ ⟨ζ - star ζ, sub_mem (Submodule.subset_span hζS₁)
        (Submodule.subset_span (hS₁star ζ hζS₁))⟩ Θ rfl
    rw [← hkey, hsplit, map_sub, Submodule.coe_sub, hνstar]
  set F : dadeDomain L A₀ :=
    ⟨h.primeTIbridge σ ζ 1 n (principalIrr ↥W₁) j,
      primeTIbridge_mem_dadeDomain hB hA (principalIrr ↥W₁) hj⟩ with hF
  set F' : dadeDomain L A₀ :=
    ⟨h.primeTIbridge σ ζ 1 n (principalIrr ↥W₁) (starIrr j),
      primeTIbridge_mem_dadeDomain hB hA (principalIrr ↥W₁)
        (h.starIrr_ne_principalIrr_right hj)⟩ with hF'
  have hstarF : (⟨star (F : ↥L → ℂ), star_mem_dadeDomain F.2⟩ : dadeDomain L A₀)
      = F' + (n : ℂ) • Θ := by
    refine Subtype.ext ?_
    have hs := star_primeTIbridge hB (principalIrr ↥W₁) j
    rw [starIrr_principalIrr] at hs
    simpa [hF, hF', hΘ] using hs
  have hτstar : star ((dadeMap hD F : classFun G) : G → ℂ)
      = ((dadeMap hD F' : classFun G) : G → ℂ)
        + (n : ℂ) • (((ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)
          - star (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ))) := by
    rw [← dadeMap_star hD F.2, show (⟨star (F : ↥L → ℂ), star_mem_dadeDomain F.2⟩ :
      dadeDomain L A₀) = F' + (n : ℂ) • Θ from hstarF, map_add, map_smul, Submodule.coe_add,
      SetLike.val_smul, hτΘ]
  have hη : star (hW.prodCharEta ω (irrMapSubtype L W₁ (principalIrr ↥W₁))
        (irrMapSubtype L W₂ j))
      = hW.prodCharEta ω (irrMapSubtype L W₁ (principalIrr ↥W₁))
          (irrMapSubtype L W₂ (starIrr j)) := by
    have hfin1 : Finite ↥(W₁.map L.subtype) := hW.finite_left
    have hfin2 : Finite ↥(W₂.map L.subtype) := hW.finite_right
    rw [hW.star_prodCharEta_starIrr hω, ← irrMapSubtype_starIrr, ← irrMapSubtype_starIrr,
      irrMapSubtype_principal, starIrr_principalIrr, irrMapSubtype_principal]
  have hη0 : star (hW.prodCharEta ω (irrMapSubtype L W₁ (principalIrr ↥W₁))
        (principalIrr ↥(W₂.map L.subtype)))
      = hW.prodCharEta ω (irrMapSubtype L W₁ (principalIrr ↥W₁))
          (principalIrr ↥(W₂.map L.subtype)) := by
    have hfin1 : Finite ↥(W₁.map L.subtype) := hW.finite_left
    have hfin2 : Finite ↥(W₂.map L.subtype) := hW.finite_right
    rw [hW.star_prodCharEta_starIrr hω, starIrr_principalIrr, ← irrMapSubtype_starIrr,
      irrMapSubtype_principal, starIrr_principalIrr, irrMapSubtype_principal]
  rw [bridgeError_apply, bridgeError_apply]
  rw [show ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n (principalIrr ↥W₁) j,
      primeTIbridge_mem_dadeDomain hB hA (principalIrr ↥W₁) hj⟩ : classFun G) : G → ℂ)
    = ((dadeMap hD F : classFun G) : G → ℂ) from rfl]
  rw [show ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n (principalIrr ↥W₁) (starIrr j),
      primeTIbridge_mem_dadeDomain hB hA (principalIrr ↥W₁)
        (h.starIrr_ne_principalIrr_right hj)⟩ : classFun G) : G → ℂ)
    = ((dadeMap hD F' : classFun G) : G → ℂ) from rfl]
  simp only [star_add, star_sub, star_smul, hτstar, hη, hη0, smul_sub]
  rw [show star ((n : ℂ)) = (n : ℂ) by simp]
  abel

theorem star_bridgeError_eq (hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}))
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hζS₁ : ζ ∈ S₁) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    star (bridgeError hB hA hD hW ω ν₁ hζS₁ i hj)
      = bridgeError hB hA hD hW ω ν₁ hζS₁ i hj := by
  rw [bridgeError_eq_of_row hB hA hD hW hω hζS₁ i (principalIrr ↥W₁) hj,
    star_bridgeError_principal_left (h := h) hodd hB hS₁ hA hD hW hω hS₁star hν₁ hτ₁ hζS₁ hj,
    bridgeError_eq_of_ne_principal_right' hB hA hD hW hω hζS₁ (principalIrr ↥W₁)
      (h.starIrr_ne_principalIrr_right hj) hj]

theorem exists_common_bridgeError (_hodd : Odd (Nat.card G))
    (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) ''
          cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
        ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅)
    (_hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (_hprime₁ : (Nat.card ↥W₁).Prime) (_hprime₂ : (Nat.card ↥W₂).Prime)
    (_hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (_hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁)
    (_hncard : (S₁.ncard : ℤ) = n)
    (_hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥W₁ : ℂ))
    (_hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (_hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ)) :
    ∃ β : G → ℂ,
      (∀ (i : Irr ↥W₁) (j : Irr ↥W₂) (hj : j ≠ principalIrr ↥W₂),
          bridgeError hB hA hD (h.isCyclicTIPair_map_subtype hstab hdisj) ω ν₁ hζS₁ i hj = β) ∧
        β ∈ virtualChars G ∧ (∀ g : G, (starRingEnd ℂ) (β g) = β g) ∧ IsOrthogonal β 1 := by
  classical
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  obtain ⟨j₀, -, hj₀⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h (principalIrr ↥W₂)
  have hS₁' : S₁ ⊆ indFam K (Irr ↥K \ {1}) := _hS₁.trans Set.inter_subset_left
  refine ⟨bridgeError hB hA hD hW ω ν₁ hζS₁ (principalIrr ↥W₁) hj₀, ?_, ?_, ?_, ?_⟩
  · intro i j hj
    rw [bridgeError_eq_of_row hB hA hD hW _hω hζS₁ i (principalIrr ↥W₁) hj,
      bridgeError_eq_of_ne_principal_right' hB hA hD hW _hω hζS₁ (principalIrr ↥W₁) hj hj₀]
  · exact bridgeError_mem_virtualChars hB hA hD hW _hω hζS₁ (principalIrr ↥W₁) hj₀
  · intro g
    have hstar := star_bridgeError_eq (h := h) _hodd hB hS₁' hA hD hW _hω _hS₁star _hν₁ _hτ₁
      hζS₁ (principalIrr ↥W₁) hj₀
    have := congrFun hstar g
    simpa [Pi.star_apply, RCLike.star_def] using this
  · exact isOrthogonal_bridgeError_one (h := h) _hodd hB hS₁' hA hD hW _hω _hS₁star _hν₁ _hτ₁
      hζS₁ (principalIrr ↥W₁) hj₀

end PrimeDadeCommonError

end CFSG.FeitThompson

end
