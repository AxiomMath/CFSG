module

public import CFSG.FeitThompson.Representations.CoherentNormalIrreducibleConjugation
public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Representations.SmallCharactersPerpendicularCyclicTIArray
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
import CFSG.FeitThompson.Representations.DisjointCoherentRowColumnContradiction
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate Pointwise

variable {G : Type*} [Group G]

theorem dadeMap_eq_dadeMap_of_subset [Finite G] {L : Subgroup G} {A B : Set G}
    {J : G → Subgroup G} (hD : IsDadeData L A J) (hDB : IsDadeData L B J) (hBA : B ⊆ A)
    {f : ↥L → ℂ} (hfB : f ∈ dadeDomain L B) (hfA : f ∈ dadeDomain L A) :
    ((dadeMap hD ⟨f, hfA⟩ : classFun G) : G → ℂ)
      = ((dadeMap hDB ⟨f, hfB⟩ : classFun G) : G → ℂ) := by
  funext x
  by_cases hx : x ∈ totalDadeSupport B J
  · obtain ⟨b, hb, hxb⟩ := mem_totalDadeSupport_iff.1 hx
    rw [dadeMap_apply_of_mem_dadeSupport hD ⟨f, hfA⟩ (hBA hb) hxb,
      dadeMap_apply_of_mem_dadeSupport hDB ⟨f, hfB⟩ hb hxb]
  · rw [coe_dadeMap hD, coe_dadeMap hDB,
      dadeMapFun_eq_zero_of_notMem_totalDadeSupport hD hfA
        (fun y hy => dadeDomain.apply_eq_zero hfB hy) hx,
      dadeMapFun_eq_zero_of_notMem L B J hx]

theorem isDadeData_puncturedCore [Finite G] {L : Subgroup G} {A : Set G} {T : G → Subgroup G}
    {K : Subgroup ↥L} [K.Normal]
    (hD : IsDadeData L A T) (hKA : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A) :
    IsDadeData L ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T := by
  refine hD.of_subset hKA ?_
  rintro a ⟨k, ⟨hkK, hk1⟩, rfl⟩ x hx
  refine ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, ⟨Subgroup.Normal.conj_mem ‹K.Normal› k hkK ⟨x, hx⟩, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff]
    intro hc
    refine hk1 ?_
    have hk : k = (⟨x, hx⟩ : ↥L)⁻¹ * (⟨x, hx⟩ * k * (⟨x, hx⟩ : ↥L)⁻¹) * ⟨x, hx⟩ := by group
    rw [Set.mem_singleton_iff, hk, hc]
    group
  · simp

theorem coe_nu_eq_dadeMap_puncturedCore [Finite G] {L : Subgroup G} {A : Set G}
    {T : G → Subgroup G} {K : Subgroup ↥L} [K.Normal] {S : Set (↥L → ℂ)}
    {ν : Submodule.span ℤ S →+ virtualChars G} (hD : IsDadeData L A T)
    (hKA : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A)
    (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
      (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
    (f : Submodule.span ℤ S)
    (F : dadeDomain L ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})))
    (h : (f : ↥L → ℂ) = (F : ↥L → ℂ)) :
    (ν f : G → ℂ)
      = ((dadeMap (isDadeData_puncturedCore hD hKA) F : classFun G) : G → ℂ) := by
  have hFA : (F : ↥L → ℂ) ∈ dadeDomain L A := dadeDomain_mono hKA F.2
  rw [hντ f ⟨(F : ↥L → ℂ), hFA⟩ h]
  exact dadeMap_eq_dadeMap_of_subset hD (isDadeData_puncturedCore hD hKA) hKA F.2 hFA

theorem notMem_map_subtype_of_mem_cyclicTIDiff {L : Subgroup G} {K : Subgroup ↥L}
    {W W1 W2 : Subgroup G} (hW : IsCyclicTIPair W W1 W2) (hW2K : W2 ≤ K.map L.subtype)
    (hW1K : W1 ⊓ K.map L.subtype = ⊥) {v : G} (hv : v ∈ cyclicTIDiff W W1 W2) :
    v ∉ K.map L.subtype := by
  obtain ⟨hvW, hv1, hv2⟩ := mem_cyclicTIDiff.1 hv
  intro hvK
  have hmul : v ∈ (W1 : Set G) * (W2 : Set G) := by rw [hW.mul_eq]; exact hvW
  obtain ⟨x, hx, y, hy, hxy⟩ := hmul
  have hxy' : x * y = v := hxy
  have hxK : x ∈ K.map L.subtype := by
    have hx' : x = v * y⁻¹ := by rw [← hxy']; group
    rw [hx']
    exact mul_mem hvK (inv_mem (hW2K hy))
  have hx1 : x = 1 := by
    have hmem : x ∈ W1 ⊓ K.map L.subtype := ⟨hx, hxK⟩
    rw [hW1K] at hmem
    simpa using hmem
  have hvy : v = y := by rw [← hxy', hx1, one_mul]
  exact hv2 (hvy ▸ hy)

theorem IsCyclicTIIsometry.apply_eq_zero_of_forall_cfInner_eq_zero [Fintype G]
    {W W1 W2 : Subgroup G} [Fintype ↥W] {σ : classFun ↥W →ₗ[ℂ] classFun G}
    (hW : IsCyclicTIPair W W1 W2) (hσ : IsCyclicTIIsometry W W1 W2 σ) {ρ : G → ℂ}
    (hρ : ρ ∈ classFun G)
    (horth : ∀ χ : classFun ↥W, (χ : ↥W → ℂ) ∈ Irr ↥W → cfInner ρ (σ χ : G → ℂ) = 0)
    {v : ↥W} (hv : (v : G) ∈ cyclicTIDiff W W1 W2) : ρ (v : G) = 0 := by
  classical
  have hcomm := hW.isMulCommutative_coe
  have : Fintype ↑(Irr ↥W) := Fintype.ofFinite _
  set p : ↥W → ℂ := Pi.single v 1 with hp
  set pcf : classFun ↥W := ⟨p, single_mem_classFun v 1⟩ with hpcf
  have hσp : (σ pcf : G → ℂ) = indClassFun W p := by
    refine hσ.eq_indClassFun pcf fun x hx => ?_
    change p x = 0
    rw [hp, Pi.single_eq_of_ne']
    intro hxv
    exact hx (hxv ▸ hv)
  set F : classFun ↥W →ₗ[ℂ] (G → ℂ) := (classFun G).subtype ∘ₗ σ with hF
  have hzero : cfInner ρ (σ pcf : G → ℂ) = 0 := by
    have hsum : F pcf
        = ∑ χ : Irr ↥W, (classFun.basisIrr ↥W).repr pcf χ • F ((classFun.basisIrr ↥W) χ) := by
      conv_lhs => rw [← (classFun.basisIrr ↥W).sum_repr pcf]
      rw [map_sum]
      simp only [map_smul]
    have hz : cfInner ρ (F pcf) = 0 := by
      rw [hsum, cfInner_sum_right]
      refine Finset.sum_eq_zero fun χ _ => ?_
      rw [cfInner_smul_right]
      have hχ := horth ((classFun.basisIrr ↥W) χ) (by
        rw [classFun.basisIrr_apply, Irr.coe_toClassFun]; exact χ.2)
      rw [show F ((classFun.basisIrr ↥W) χ) = (σ ((classFun.basisIrr ↥W) χ) : G → ℂ) from rfl,
        hχ, mul_zero]
    exact hz
  rw [hσp] at hzero
  have h1 : cfInner p (resClassFun W ρ) = 0 := by
    rw [← cfInner_indClassFun W p hρ, ← conj_cfInner, hzero, map_zero]
  have h2 : cfInner (resClassFun W ρ) p = 0 := by
    rw [← conj_cfInner, h1, map_zero]
  rw [hp, cfInner_single, resClassFun_apply] at h2
  have hcard : ((Nat.card ↥W : ℂ))⁻¹ ≠ 0 := by simp
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd h hcard
  · exact h

namespace ExtendedDade

variable [Fintype G] {L : Subgroup G} [Fintype ↥L] {K : Subgroup ↥L} [K.Normal]
  {T : G → Subgroup G} {A : Set G} {W W1 W2 : Subgroup G} [Fintype ↥W]
  {ω : classFun ↥W →ₗ[ℂ] classFun G} {S : Set (↥L → ℂ)} {ζ : ↥L → ℂ}
  {ν : Submodule.span ℤ S →+ virtualChars G}
  (hodd : Odd (Nat.card G))
  (hD : IsDadeData L A T)
  (hKA : (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ A)
  (hVA : cyclicTIDiff W W1 W2 ⊆ A)
  (hS : S = indFam K (Irr ↥K \ {1}))
  (hνiso : ∀ f h : Submodule.span ℤ S,
    cfInner (ν f : G → ℂ) (ν h : G → ℂ) = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
  (hντ : ∀ (f : Submodule.span ℤ S) (F : dadeDomain L A),
    (f : ↥L → ℂ) = (F : ↥L → ℂ) → (ν f : G → ℂ) = ((dadeMap hD F : classFun G) : G → ℂ))
  (hζS : ζ ∈ S) (hζIrr : ζ ∈ Irr ↥L)
  (hW : IsCyclicTIPair W W1 W2) (hWL : W ≤ L)
  (hW2K : W2 ≤ K.map L.subtype) (hW1K : W1 ⊓ K.map L.subtype = ⊥)
  (hω : IsCyclicTIIsometry W W1 W2 ω)

omit [Fintype G] [Fintype ↥W] in
include hodd hS hζS hζIrr in
theorem star_mem_and_ne : star ζ ∈ S ∧ star ζ ≠ ζ :=
  ⟨NormalInducedFamily.star_mem_of_mem hS hζS,
    NormalInducedFamily.star_ne_self_of_odd hodd hS hζS hζIrr⟩

omit [Fintype G] [Fintype ↥W] in
include hKA hS hζS hζIrr in
theorem sub_star_mem_dadeDomain : ζ - star ζ ∈ dadeDomain L A := by
  have hSsub : S ⊆ indFam K (Irr ↥K) := by rw [hS]; exact indFam_mono K Set.sdiff_subset
  refine dadeDomain_mono hKA
    (NormalInducedFamily.mem_dadeDomain_of_mem_span_indFam (H := K) rfl hSsub ?_ ?_)
  · exact sub_mem (Submodule.subset_span hζS)
      (Submodule.subset_span (NormalInducedFamily.star_mem_of_mem hS hζS))
  · simp [conj_apply_one_of_mem_Irr hζIrr]

omit [Fintype ↥W] in
include hodd hD hKA hS hνiso hντ hζS hζIrr in
theorem coe_nu_star_eq :
    (ν ⟨star ζ, Submodule.subset_span (NormalInducedFamily.star_mem_of_mem hS hζS)⟩ : G → ℂ)
      = star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) :=
  NormalInducedFamily.coe_nu_star_eq hodd (isDadeData_puncturedCore hD hKA) rfl hS hνiso
    (coe_nu_eq_dadeMap_puncturedCore hD hKA hντ) hζS hζIrr

omit [Fintype ↥W] in
include hodd hD hKA hS hνiso hντ hζS hζIrr in
theorem exists_sign_nonreal_Irr_nu :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ χ ∈ Irr G, star χ ≠ χ ∧
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) = ε • χ :=
  NormalInducedFamily.exists_sign_nonreal_Irr_nu hodd (isDadeData_puncturedCore hD hKA) rfl hS
    hνiso (coe_nu_eq_dadeMap_puncturedCore hD hKA hντ) hζS hζIrr

omit [Fintype ↥W] in
include hodd hD hKA hS hνiso hντ hζS hζIrr in
theorem nu_mem_signedIrr : (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) ∈ signedIrr G :=
  NormalInducedFamily.nu_mem_signedIrr hodd (isDadeData_puncturedCore hD hKA) rfl hS hνiso
    (coe_nu_eq_dadeMap_puncturedCore hD hKA hντ) hζS hζIrr

omit [Fintype ↥W] in
include hodd hD hKA hS hνiso hντ hζS hζIrr in
theorem star_nu_ne :
    star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
      ≠ (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) :=
  NormalInducedFamily.star_nu_ne hodd (isDadeData_puncturedCore hD hKA) rfl hS hνiso
    (coe_nu_eq_dadeMap_puncturedCore hD hKA hντ) hζS hζIrr

omit [Fintype ↥W] in
include hodd hD hKA hS hνiso hντ hζS hζIrr in
theorem coe_nu_sub_star_eq_dadeMap :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
      = ((dadeMap hD ⟨ζ - star ζ, sub_star_mem_dadeDomain hKA hS hζS hζIrr⟩ :
          classFun G) : G → ℂ) := by
  have hstar : star ζ ∈ S := NormalInducedFamily.star_mem_of_mem hS hζS
  have hsub : ζ - star ζ ∈ Submodule.span ℤ S :=
    sub_mem (Submodule.subset_span hζS) (Submodule.subset_span hstar)
  have key : (ν ⟨ζ - star ζ, hsub⟩ : G → ℂ)
      = (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        - (ν ⟨star ζ, Submodule.subset_span hstar⟩ : G → ℂ) := by
    rw [show (⟨ζ - star ζ, hsub⟩ : Submodule.span ℤ S)
        = ⟨ζ, Submodule.subset_span hζS⟩ - ⟨star ζ, Submodule.subset_span hstar⟩ from rfl,
      map_sub]
    rfl
  rw [← coe_nu_star_eq hodd hD hKA hS hνiso hντ hζS hζIrr, ← key]
  exact hντ _ _ rfl

omit [Fintype ↥W] in
include hodd hD hKA hVA hS hνiso hντ hζS hζIrr hW hWL hW2K hW1K in
theorem sub_star_nu_apply_eq_zero_of_mem_cyclicTIDiff {v : G} (hv : v ∈ cyclicTIDiff W W1 W2) :
    ((ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
      - star (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)) v = 0 := by
  have hvL : v ∈ L := hWL (mem_cyclicTIDiff.1 hv).1
  have hvK : v ∉ K.map L.subtype := notMem_map_subtype_of_mem_cyclicTIDiff hW hW2K hW1K hv
  have hvK' : (⟨v, hvL⟩ : ↥L) ∉ K := fun hc => hvK ⟨⟨v, hvL⟩, hc, rfl⟩
  rw [coe_nu_sub_star_eq_dadeMap hodd hD hKA hS hνiso hντ hζS hζIrr,
    dadeMap_apply_mem hD _ (hVA hv)]
  have hSsub : S ⊆ indFam K (Irr ↥K) := by rw [hS]; exact indFam_mono K Set.sdiff_subset
  have hz : ζ (⟨v, hvL⟩ : ↥L) = 0 := eq_zero_of_mem_indFam_of_notMem K (hSsub hζS) hvK'
  simp only [Pi.sub_apply, Pi.star_apply, RCLike.star_def]
  rw [hz]
  simp

include hodd hD hKA hVA hS hνiso hντ hζS hζIrr hW hWL hW2K hW1K hω in
theorem cfInner_nu_apply_eq_zero {χ : classFun ↥W} (hχ : (χ : ↥W → ℂ) ∈ Irr ↥W) :
    cfInner (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) (ω χ : G → ℂ) = 0 := by
  set ρ : G → ℂ := (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) with hρdef
  have hρ : ρ ∈ signedIrr G := nu_mem_signedIrr hodd hD hKA hS hνiso hντ hζS hζIrr
  have hnrstar : star ρ ≠ ρ := star_nu_ne hodd hD hKA hS hνiso hντ hζS hζIrr
  have hnr : ρ ≠ fun x => conj (ρ x) := by
    intro hc
    exact hnrstar (by funext x; simpa using (congrFun hc x).symm)
  have h0 : ∀ x ∈ cyclicTIDiff W W1 W2, (ρ - fun y => conj (ρ y)) x = 0 := by
    intro x hx
    have hx0 := sub_star_nu_apply_eq_zero_of_mem_cyclicTIDiff hodd hD hKA hVA hS hνiso hντ hζS
      hζIrr hW hWL hW2K hW1K hx
    simpa using hx0
  exact isOrthogonal_iff.1 (hW.isOrthogonal_apply_of_ne_conj hω hρ hnr h0 hχ)

include hodd hD hKA hVA hS hνiso hντ hζS hζIrr hW hWL hW2K hW1K hω in
theorem cfInner_nu_prodCharEta_eq_zero (i : Irr ↥W1) (j : Irr ↥W2) :
    cfInner (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) (hW.prodCharEta ω i j) = 0 := by
  rw [IsCyclicTIPair.prodCharEta_eq_coe_apply]
  refine cfInner_nu_apply_eq_zero hodd hD hKA hVA hS hνiso hντ hζS hζIrr hW hWL hW2K hW1K hω ?_
  rw [IsCyclicTIPair.coe_basisProdIrr_apply]
  exact hW.prodChar_mem_Irr i.2 j.2

include hodd hD hKA hVA hS hνiso hντ hζS hζIrr hW hWL hW2K hW1K hω in
theorem nu_apply_eq_zero_of_mem_cyclicTIDiff {v : G} (hv : v ∈ cyclicTIDiff W W1 W2) :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) v = 0 := by
  have hρcf : (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) ∈ classFun G :=
    mem_classFun_of_mem_span_Irr (signedIrr_subset_span_Irr
      (nu_mem_signedIrr hodd hD hKA hS hνiso hντ hζS hζIrr))
  have hvW : v ∈ W := (mem_cyclicTIDiff.1 hv).1
  exact hω.apply_eq_zero_of_forall_cfInner_eq_zero hW hρcf
    (fun χ hχ => cfInner_nu_apply_eq_zero hodd hD hKA hVA hS hνiso hντ hζS hζIrr hW hWL hW2K
      hW1K hω hχ) (v := ⟨v, hvW⟩) hv

end ExtendedDade

end CFSG.FeitThompson
