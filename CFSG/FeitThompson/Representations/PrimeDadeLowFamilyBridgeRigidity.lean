module

public import CFSG.FeitThompson.Representations.LowFamilyBridgesRealCorrection
import CFSG.FeitThompson.Representations.PrimeDadePrincipalRowSmallComplement
import CFSG.FeitThompson.Representations.PrincipalColumnProjectionNormalizedPivot

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace PrimeDadeLowFamily

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d n : ℤ} {A₀ : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {S₁ : Set (↥L → ℂ)} {ν₁ : Submodule.span ℤ S₁ →+ virtualChars G}
  {τ₁ : charSpanZero S₁ →+ virtualChars G}

omit [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  [K.Normal] in
theorem mixedSet_subset_param
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀) :
    cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ⊆ A₀ := by
  intro g hg
  rw [← image_cyclicTIset_eq] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact hA ⟨x, mem_primeTIbridgeSupport_of_isConj hx (IsConj.refl _), rfl⟩

noncomputable def tauBridge (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  ((dadeZMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
    primeTIbridge_mem_dadeZDomain hB hA i hj⟩ : charSpanZero (Irr G)) : G → ℂ)

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem tauBridge_def (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    tauBridge hB hA hD i hj
      = ((dadeZMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
          primeTIbridge_mem_dadeZDomain hB hA i hj⟩ : charSpanZero (Irr G)) : G → ℂ) := (rfl)

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem tauBridge_eq_dadeMap (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    tauBridge hB hA hD i hj
      = ((dadeMap hD ⟨h.primeTIbridge σ ζ 1 n i j,
          PrimeDadeCommonError.primeTIbridge_mem_dadeDomain hB hA i hj⟩ :
            classFun G) : G → ℂ) := by
  rw [tauBridge_def, coe_dadeZMap]

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem tauBridge_mem_virtualChars (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    tauBridge hB hA hD i hj ∈ virtualChars G :=
  dadeZMap_mem_virtualChars hD _

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem cfInner_self_tauBridge (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (tauBridge hB hA hD i hj) (tauBridge hB hA hD i hj) = 2 + (n : ℂ) ^ 2 := by
  rw [tauBridge_def, cfInner_dadeZMap]
  exact h.cfInner_self_primeTIbridge hB i hj

variable [Fintype ↑(Irr ↥W₁)]

noncomputable def tauPrincipalRowSub (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) : G → ℂ :=
  ((dadeZMap hD ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
    mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
      (h.primeTIrow_sub_mem_span_Irr hB.isometry hB.mem_indFam), fun x hx =>
        h.primeTIrow_sub_apply_eq_zero hB.isometry hB.mem_indFam hB.apply_one fun hmem =>
          hx (hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hmem.1
            (by simpa using hmem.2), rfl⟩)⟩⟩ : charSpanZero (Irr G)) : G → ℂ)

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem tauPrincipalRowSub_def (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hmem : h.primeTIrow σ (principalIrr ↥W₂) - ζ ∈ dadeZDomain L A₀) :
    tauPrincipalRowSub hB hA hD
      = ((dadeZMap hD ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ, hmem⟩ :
          charSpanZero (Irr G)) : G → ℂ) := (rfl)

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem tauPrincipalRowSub_eq_dadeMap (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (F : dadeDomain L A₀)
    (hF : (F : ↥L → ℂ) = h.primeTIrow σ (principalIrr ↥W₂) - ζ) :
    tauPrincipalRowSub hB hA hD = ((dadeMap hD F : classFun G) : G → ℂ) := by
  rw [tauPrincipalRowSub, coe_dadeZMap,
    show (⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ, mem_dadeDomain_of_mem_dadeZDomain
      (mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
        (h.primeTIrow_sub_mem_span_Irr hB.isometry hB.mem_indFam), fun x hx =>
          h.primeTIrow_sub_apply_eq_zero hB.isometry hB.mem_indFam hB.apply_one fun hmem =>
            hx (hA ⟨x, mem_primeTIbridgeSupport_of_mem_of_ne_one hmem.1
              (by simpa using hmem.2), rfl⟩)⟩)⟩ : dadeDomain L A₀) = F from Subtype.ext hF.symm]

omit [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem cfInner_tauPrincipalRowSub_tauBridge (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    cfInner (tauPrincipalRowSub hB hA hD) (tauBridge hB hA hD i hj) = (n : ℂ) - 1 := by
  classical
  have hrow : cfInner (h.primeTIbridge σ ζ 1 n i j) (h.primeTIrow σ (principalIrr ↥W₂)) = -1 := by
    rw [h.cfInner_primeTIbridge_primeTIrow hB i j (principalIrr ↥W₂), if_neg hj, if_pos rfl]
    ring
  have hrow' : cfInner (h.primeTIrow σ (principalIrr ↥W₂)) (h.primeTIbridge σ ζ 1 n i j) = -1 := by
    rw [← conj_cfInner, hrow]; simp
  rw [tauPrincipalRowSub, tauBridge_def, cfInner_dadeZMap]
  change cfInner (h.primeTIrow σ (principalIrr ↥W₂) - ζ) (h.primeTIbridge σ ζ 1 n i j)
    = (n : ℂ) - 1
  rw [cfInner_sub_left, hrow', h.cfInner_zeta_primeTIbridge hB i j]
  ring

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem tauBridge_apply_of_mem_mixedSet (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    (v : ↥((W₁ ⊔ W₂).map L.subtype))
    (hv : (v : G) ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype)) :
    tauBridge hB hA hD i hj (v : G)
      = (1 : ℂ) * (hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((irrMapSubtype L W₂ j : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v
        - hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((principalIrr ↥(W₂.map L.subtype) : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v) := by
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
  have e1 := prodChar_irrMapSubtype (L := L) h.isCyclicTIPair hW i j u
  rw [hveq] at e1
  have e2 := prodChar_irrMapSubtype (L := L) h.isCyclicTIPair hW i (principalIrr ↥W₂) u
  rw [hveq, irrMapSubtype_principal] at e2
  have hval : tauBridge hB hA hD i hj (v : G)
      = h.primeTIbridge σ ζ 1 n i j ⟨(v : G), hD.mem_of_mem (mixedSet_subset_param hA hv)⟩ := by
    rw [tauBridge_def]
    exact dadeZMap_apply_mem hD _ (mixedSet_subset_param hA hv)
  rw [hval,
    show (⟨(v : G), hD.mem_of_mem (mixedSet_subset_param hA hv)⟩ : ↥L) = ((u : ↥L)) from rfl,
    h.primeTIbridge_apply_of_mem_cyclicTIset hB i hj (v := u) huV, e1, e2, Int.cast_one]

omit [Fintype G] [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem cfInner_primeTIbridge_mem (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L) {ξ : ↥L → ℂ} (hξ : ξ ∈ S₁)
    (i : Irr ↥W₁) (j : Irr ↥W₂) [Decidable (ξ = ζ)] :
    cfInner (h.primeTIbridge σ ζ 1 n i j) ξ = -(if ξ = ζ then (n : ℂ) else 0) := by
  classical
  have hξind : ξ ∈ indFam K (Irr ↥K) := indFam_mono K Set.sdiff_subset (hS₁ hξ).1
  have hξIrr : ξ ∈ Irr ↥L := (hS₁ hξ).2
  have h0 : ∀ m : Irr ↥W₂, cfInner (h.primeTIirr σ i m) ξ = 0 := fun m => by
    have hz := h.cfInner_primeTIirr_eq_zero_of_mem_indFam hB.isometry hξind hξIrr i m
    rw [← conj_cfInner, hz, map_zero]
  rw [h.cfInner_primeTIbridge_left, h0 j, h0 (principalIrr ↥W₂),
    cfInner_eq_ite_of_mem_Irr hB.mem_Irr hξIrr]
  by_cases hc : ξ = ζ
  · rw [if_pos hc, if_pos hc.symm]; ring
  · rw [if_neg hc, if_neg (fun hcc => hc hcc.symm)]; ring

omit [Fintype G] [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [Fintype ↥(W₁ ⊔ W₂)]
  [K.Normal] in
include h in
theorem mem_dadeZDomain_of_mem_charSpanZero
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero S₁) : f ∈ dadeZDomain L A₀ :=
  mem_dadeZDomain.2
    ⟨Submodule.span_le.2 (fun _ hx => Irr_subset_virtualChars (hS₁ hx).2) (charSpanZero_le _ hf),
      fun x hx => PrimeDadeCommonError.eq_zero_of_mem_charSpanZero_of_notMem (h := h)
        (fun _ hx => (hS₁ hx).1) hA ⟨f, hf⟩ x hx⟩

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_tauBridge_nu (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero S₁) :
    cfInner (tauBridge hB hA hD i hj) (ν₁ ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = cfInner (h.primeTIbridge σ ζ 1 n i j) f := by
  have hfZ : f ∈ dadeZDomain L A₀ := mem_dadeZDomain_of_mem_charSpanZero (h := h) hS₁ hA hf
  have hnu : (ν₁ ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = ((dadeZMap hD ⟨f, hfZ⟩ : charSpanZero (Irr G)) : G → ℂ) := by
    rw [coe_dadeZMap]
    exact hτ₁ _ ⟨f, mem_dadeDomain_of_mem_dadeZDomain hfZ⟩ rfl
  rw [tauBridge_def, hnu, cfInner_dadeZMap]

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] in
theorem cfInner_tauBridge_nu_mem (hB : h.IsUniformBridgeData σ ζ d n 1)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥W₁ : ℂ)) (hζS₁ : ζ ∈ S₁)
    {ξ : ↥L → ℂ} (hξ : ξ ∈ S₁) (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂)
    [Decidable (ξ = ζ)] :
    cfInner (tauBridge hB hA hD i hj) (ν₁ ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ)
      = cfInner (tauBridge hB hA hD i hj) (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)
        + (n : ℂ) - (if ξ = ζ then (n : ℂ) else 0) := by
  classical
  have hz : ζ - ξ ∈ charSpanZero S₁ :=
    mem_charSpanZero.2 ⟨sub_mem (Submodule.subset_span hζS₁) (Submodule.subset_span hξ), by
      simp [hdeg ζ hζS₁, hdeg ξ hξ]⟩
  have hsplit : (⟨ζ - ξ, charSpanZero_le _ hz⟩ : Submodule.span ℤ S₁)
      = ⟨ζ, Submodule.subset_span hζS₁⟩ - ⟨ξ, Submodule.subset_span hξ⟩ := Subtype.ext rfl
  have hadd : (ν₁ ⟨ζ - ξ, charSpanZero_le _ hz⟩ : G → ℂ)
      = (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ)
        - (ν₁ ⟨ξ, Submodule.subset_span hξ⟩ : G → ℂ) := by
    rw [hsplit, map_sub, Submodule.coe_sub]
  have hkey := cfInner_tauBridge_nu (ν₁ := ν₁) hB hS₁ hA hD hτ₁ i hj hz
  rw [hadd, cfInner_sub_right, cfInner_sub_right, h.cfInner_primeTIbridge_zeta hB i j,
    cfInner_primeTIbridge_mem hB hS₁ hξ i j] at hkey
  linear_combination -hkey

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↥(W₁ ⊔ W₂)] in
include h in
theorem isOrthogonal_nu_prodCharEta (hodd : Odd (Nat.card G))
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁)
    (hνiso : ∀ f g : Submodule.span ℤ S₁,
      cfInner (ν₁ f : G → ℂ) (ν₁ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ))
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ξ : ↥L → ℂ} (hξS : ξ ∈ S₁)
    (k : Irr ↥(W₁.map L.subtype)) (l : Irr ↥(W₂.map L.subtype)) :
    IsOrthogonal (ν₁ ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) (hW.prodCharEta ω k l) :=
  CoherentCore.isOrthogonal_nu_prodCharEta hodd hW (Subgroup.map_mono h.right_le)
    (by rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]) hω hD (mixedSet_subset_param hA)
    (fun _ hx => PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K (hS₁ hx).1)
    hS₁star hνiso
    (fun f x hx => PrimeDadeCommonError.eq_zero_of_mem_charSpanZero_of_notMem (h := h)
      (fun _ hx => (hS₁ hx).1) hA f x hx) hτ₁ hξS (hS₁ hξS).2 k l

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↥(W₁ ⊔ W₂)] in
include h in
theorem nu_apply_eq_zero_of_mem_mixedSet (hodd : Odd (Nat.card G))
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hA : (fun x : ↥L => (x : G)) '' primeTIbridgeSupport K W₁ W₂ ⊆ A₀)
    (hD : IsDadeData L A₀ T)
    (hW : IsCyclicTIPair ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype))
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁)
    (hνiso : ∀ f g : Submodule.span ℤ S₁,
      cfInner (ν₁ f : G → ℂ) (ν₁ g : G → ℂ) = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ))
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    {ξ : ↥L → ℂ} (hξS : ξ ∈ S₁) {v : G}
    (hv : v ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)) :
    (ν₁ ⟨ξ, Submodule.subset_span hξS⟩ : G → ℂ) v = 0 :=
  CoherentCore.nu_apply_eq_zero_of_mem_cyclicTIDiff hodd hW (Subgroup.map_mono h.right_le)
    (by rw [← Subgroup.map_inf_eq W₁ K L.subtype L.subtype_injective, inf_comm, h.inf_eq_bot,
      Subgroup.map_bot]) hω hD (mixedSet_subset_param hA)
    (fun _ hx => PrimeDadePivot.indFam_sdiff_subset_indFamDetect_top K (hS₁ hx).1)
    hS₁star hνiso
    (fun f x hx => PrimeDadeCommonError.eq_zero_of_mem_charSpanZero_of_notMem (h := h)
      (fun _ hx => (hS₁ hx).1) hA f x hx) hτ₁ hξS (hS₁ hξS).2 hv

theorem exists_bijective_fin_apply_zero_eq {α : Type*} {S : Set α} (hS : S.Finite)
    {x : α} (hx : x ∈ S) {N : ℕ} (hcard : S.ncard = N) (hN : 0 < N) :
    ∃ f : Fin N → ↥S, Function.Bijective f ∧ f ⟨0, hN⟩ = ⟨x, hx⟩ := by
  have hfin : Finite ↥S := hS
  have hc : Nat.card ↥S = N := by rw [Nat.card_coe_set_eq, hcard]
  let g : ↥S ≃ Fin N := (Finite.equivFin ↥S).trans (finCongr hc)
  refine ⟨fun r => g.symm (Equiv.swap (g ⟨x, hx⟩) ⟨0, hN⟩ r), ?_, ?_⟩
  · exact (g.symm.bijective).comp (Equiv.swap _ _).bijective
  · simp

omit [Fintype ↑(Irr ↥W₁)] [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem isOrthonormalFamily_nu (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hν₁ : IsCoherentWith S₁ τ₁ ν₁) {N : ℕ} {f : Fin N → ↥S₁} (hf : Function.Injective f) :
    IsOrthonormalFamily (fun r => (ν₁ ⟨(f r : ↥L → ℂ),
      Submodule.subset_span (f r).2⟩ : G → ℂ)) := by
  classical
  rw [isOrthonormalFamily_iff]
  intro r s
  rw [hν₁.inner_eq]
  have hrIrr : ((f r : ↥L → ℂ)) ∈ Irr ↥L := (hS₁ (f r).2).2
  have hsIrr : ((f s : ↥L → ℂ)) ∈ Irr ↥L := (hS₁ (f s).2).2
  rw [show ((⟨(f r : ↥L → ℂ), Submodule.subset_span (f r).2⟩ :
      Submodule.span ℤ S₁) : ↥L → ℂ) = (f r : ↥L → ℂ) from rfl,
    show ((⟨(f s : ↥L → ℂ), Submodule.subset_span (f s).2⟩ :
      Submodule.span ℤ S₁) : ↥L → ℂ) = (f s : ↥L → ℂ) from rfl,
    cfInner_eq_ite_of_mem_Irr hrIrr hsIrr]
  by_cases hrs : r = s
  · rw [if_pos hrs, if_pos (by rw [hrs])]
  · rw [if_neg hrs, if_neg fun hc => hrs (hf (Subtype.ext hc))]

omit [Group G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)] [K.Normal] in
theorem sum_smul_eq_of_cfInner_eq {N : ℕ} {e : Fin N → G → ℂ} {f : G → ℂ} {r₁ : Fin N} {a : ℤ}
    (hcoeff : ∀ r, cfInner f (e r) = (a : ℂ) - (if r = r₁ then (N : ℂ) else 0)) :
    ∑ r, cfInner f (e r) • e r = (a : ℂ) • (∑ r, e r) - (N : ℂ) • e r₁ := by
  classical
  rw [Finset.sum_congr rfl fun r _ => by rw [hcoeff r], Finset.smul_sum]
  rw [Finset.sum_congr rfl fun r (_ : r ∈ Finset.univ) =>
    sub_smul (a : ℂ) (if r = r₁ then (N : ℂ) else 0) (e r), Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_eq_single_of_mem r₁ (Finset.mem_univ r₁)]
  · rw [if_pos rfl]
  · intro s _ hs
    rw [if_neg hs, zero_smul]

theorem tauBridge_eq_prodCharEta_sub (hodd : Odd (Nat.card G))
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
    (hω : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) ω)
    (hprime₁ : (Nat.card ↥W₁).Prime) (hprime₂ : (Nat.card ↥W₂).Prime)
    (hS₁ : S₁ ⊆ indFam K (Irr ↥K \ {1}) ∩ Irr ↥L)
    (hS₁star : ∀ χ ∈ S₁, star χ ∈ S₁) (hζS₁ : ζ ∈ S₁)
    (hncard : (S₁.ncard : ℤ) = n)
    (hdeg : ∀ χ ∈ S₁, χ 1 = (Nat.card ↥W₁ : ℂ))
    (hν₁ : IsCoherentWith S₁ τ₁ ν₁)
    (hτ₁ : ∀ (f : Submodule.span ℤ S₁) (F : dadeDomain L A₀), (f : ↥L → ℂ) = (F : ↥L → ℂ) →
      (ν₁ f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (hpsi : tauPrincipalRowSub hB hA hD
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEtaColSum ω
          (principalIrr ↥(W₂.map L.subtype)) - (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ))
    (i : Irr ↥W₁) {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    tauBridge hB hA hD i hj
      = (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω (irrMapSubtype L W₁ i)
            (irrMapSubtype L W₂ j)
        - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω (irrMapSubtype L W₁ i)
            (principalIrr ↥(W₂.map L.subtype))
        - (n : ℂ) • (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set φ : G → ℂ := tauBridge hB hA hD i hj with hφdef
  set N : ℕ := S₁.ncard with hN
  have hn2 : 2 ≤ n := hB.two_le
  have hNn : (N : ℤ) = n := hncard
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hNC : (N : ℂ) = (n : ℂ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hNn
  have hS₁fin : S₁.Finite := Set.finite_of_ncard_ne_zero (by omega)
  obtain ⟨fe, hfebij, hfe0⟩ :=
    exists_bijective_fin_apply_zero_eq hS₁fin hζS₁ (N := N) rfl hNpos
  set r₁ : Fin N := ⟨0, hNpos⟩ with hr₁
  set e : Fin N → G → ℂ :=
    fun r => (ν₁ ⟨(fe r : ↥L → ℂ), Submodule.subset_span (fe r).2⟩ : G → ℂ) with hedef
  have her₁ : e r₁ = (ν₁ ⟨ζ, Submodule.subset_span hζS₁⟩ : G → ℂ) := by
    rw [hedef]; simp only [hfe0]
  have he : IsOrthonormalFamily e := isOrthonormalFamily_nu hS₁ hν₁ hfebij.1
  have hemem : ∀ r, e r ∈ Submodule.span ℤ (Irr G) := fun r =>
    virtualChars_le_span_Irr (ν₁ _).2
  have heη : ∀ (r : Fin N) (k : Irr ↥(W₁.map L.subtype)) (l : Irr ↥(W₂.map L.subtype)),
      IsOrthogonal (e r) (hW.prodCharEta ω k l) := fun r k l =>
    isOrthogonal_nu_prodCharEta (h := h) hodd hS₁ hA hD hW hω hS₁star hν₁.inner_eq hτ₁
      (fe r).2 k l
  have heV : ∀ r, ∀ x ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), e r x = 0 := fun r x hx =>
    nu_apply_eq_zero_of_mem_mixedSet (h := h) hodd hS₁ hA hD hW hω hS₁star hν₁.inner_eq hτ₁
      (fe r).2 hx
  obtain ⟨c, hc⟩ := exists_int_cfInner_of_mem_span_Irr
    (mem_span_Irr_of_mem_virtualChars (tauBridge_mem_virtualChars hB hA hD i hj))
    (hemem r₁)
  set a : ℤ := c + (N : ℤ) with ha
  have hindex : ∀ r : Fin N, ((fe r : ↥L → ℂ) = ζ) ↔ r = r₁ := by
    intro r
    refine ⟨fun hr => hfebij.1 (by rw [hfe0]; exact Subtype.ext hr), fun hr => ?_⟩
    rw [hr, hfe0]
  have hcoeff : ∀ r, cfInner φ (e r) = (a : ℂ) - (if r = r₁ then (N : ℂ) else 0) := by
    intro r
    have hkey := cfInner_tauBridge_nu_mem (ν₁ := ν₁) hB hS₁ hA hD hτ₁ hdeg hζS₁ (fe r).2 i hj
    rw [← her₁, ← hφdef] at hkey
    rw [hedef, hkey, hc, ha]
    by_cases hr : r = r₁
    · rw [if_pos hr, if_pos ((hindex r).2 hr)]
      push_cast
      rw [hNC]
    · rw [if_neg hr, if_neg (fun hcc => hr ((hindex r).1 hcc))]
      push_cast
      rw [hNC]
  have hproj : ∑ r, cfInner φ (e r) • e r = (a : ℂ) • (∑ r, e r) - (N : ℂ) • e r₁ :=
    sum_smul_eq_of_cfInner_eq hcoeff
  obtain ⟨β, hβeq, -, hβreal, hβ1⟩ := PrimeDadeCommonError.exists_common_bridgeError
    hodd hB hA hD hstab hdisj hω hprime₁ hprime₂ hS₁ hS₁star hζS₁ hncard hdeg hν₁ hτ₁
  have hβval : β = φ - hW.prodCharEta ω (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
      + hW.prodCharEta ω (irrMapSubtype L W₁ i) (principalIrr ↥(W₂.map L.subtype))
      + (N : ℂ) • e r₁ := by
    rw [← hβeq i j hj, PrimeDadeCommonError.bridgeError_apply, hφdef,
      tauBridge_eq_dadeMap, her₁, hNC]
  have hjmap : irrMapSubtype L W₂ j ≠ principalIrr ↥(W₂.map L.subtype) := by
    intro hcc
    exact hj (irrMapSubtype_injective L W₂ (hcc.trans (irrMapSubtype_principal L W₂).symm))
  have hφmem : φ ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars (tauBridge_mem_virtualChars hB hA hD i hj)
  have hφnorm : cfInner φ φ = 2 + (N : ℂ) ^ 2 := by
    rw [hφdef, cfInner_self_tauBridge, hNC]
  have hψ : cfInner (hW.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype)) - e r₁) φ
      = (N : ℂ) - 1 := by
    rw [her₁, ← hpsi, hφdef, cfInner_tauPrincipalRowSub_tauBridge, hNC]
  have hφV : ∀ v : ↥((W₁ ⊔ W₂).map L.subtype),
      (v : G) ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) →
      φ (v : G)
        = hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
              ((irrMapSubtype L W₂ j : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v
          - hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
              ((principalIrr ↥(W₂.map L.subtype) : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v := by
    intro v hv
    rw [hφdef, tauBridge_apply_of_mem_mixedSet hB hA hD hW i hj v hv, one_mul]
  have hkey := hW.eq_prodCharEta_sub_of_isOrthonormal_of_odd hω hodd hN2 he hemem heη heV
    hjmap (φ := φ) (β := β) (a := a) hφmem hφnorm hproj hψ hφV hβval
    (fun x => Complex.conj_eq_iff_im.1 (hβreal x)) (isOrthogonal_iff.1 hβ1)
  rw [hkey.2, her₁, hNC]

end PrimeDadeLowFamily

end CFSG.FeitThompson

end
