module

public import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
public import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
public import CFSG.FeitThompson.Representations.LowNormAnchoredRectangleColumnProjection
public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients
public import CFSG.FeitThompson.Representations.DadeBetaIntegralDegreeZero
public import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
public import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
public import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.UniformLocalBridgePuncturedSupportNorm
import CFSG.FeitThompson.Definitions.KappaPrimes

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G] {L : Subgroup G} {K W₁ W₂ : Subgroup ↥L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L} {ζ : ↥L → ℂ}

def cyclicTIsat {M : Type*} [Group M] (V₁ V₂ : Subgroup M) : Set M :=
  ⋃ t : M, (fun x : M => t⁻¹ * x * t) '' cyclicTIset V₁ V₂

theorem mem_cyclicTIsat_iff {M : Type*} [Group M] {V₁ V₂ : Subgroup M} {x : M} :
    x ∈ cyclicTIsat V₁ V₂ ↔ ∃ t : M, ∃ v ∈ cyclicTIset V₁ V₂, t⁻¹ * v * t = x := by
  simp [cyclicTIsat, eq_comm]

theorem cyclicTIset_subset_cyclicTIsat {M : Type*} [Group M] {V₁ V₂ : Subgroup M} :
    cyclicTIset V₁ V₂ ⊆ cyclicTIsat V₁ V₂ :=
  fun x hx => mem_cyclicTIsat_iff.2 ⟨1, x, hx, by group⟩

def primeDadeSupport (K W₁ W₂ : Subgroup ↥L) : Set G :=
  (fun x : ↥L => (x : G)) '' (((K : Set ↥L) \ {1}) ∪ cyclicTIsat W₁ W₂)

theorem mem_primeDadeSupport_iff {x : G} :
    x ∈ primeDadeSupport K W₁ W₂ ↔
      ∃ y : ↥L, (y : G) = x ∧ (y ∈ (K : Set ↥L) \ {1} ∨ y ∈ cyclicTIsat W₁ W₂) := by
  simp only [primeDadeSupport, Set.mem_image, Set.mem_union]
  exact ⟨fun ⟨y, hy, hyx⟩ => ⟨y, hyx, hy⟩, fun ⟨y, hyx, hy⟩ => ⟨y, hy, hyx⟩⟩

theorem image_sdiff_subset_primeDadeSupport :
    (fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1}) ⊆ primeDadeSupport K W₁ W₂ := by
  rintro x ⟨y, hy, rfl⟩
  exact mem_primeDadeSupport_iff.2 ⟨y, rfl, Or.inl hy⟩

theorem coe_mem_primeDadeSupport_of_mem_cyclicTIset {y : ↥L} (hy : y ∈ cyclicTIset W₁ W₂) :
    (y : G) ∈ primeDadeSupport K W₁ W₂ :=
  mem_primeDadeSupport_iff.2 ⟨y, rfl, Or.inr (cyclicTIset_subset_cyclicTIsat hy)⟩

theorem cyclicTIDiff_map_subtype_eq_image :
    cyclicTIDiff (W₁.map L.subtype ⊔ W₂.map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      = (fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂ := by
  ext x
  simp only [mem_cyclicTIDiff, Set.mem_image, mem_cyclicTIset, ← Subgroup.map_sup]
  constructor
  · rintro ⟨hxW, hx1, hx2⟩
    obtain ⟨y, hy, rfl⟩ := hxW
    exact ⟨y, ⟨hy, fun hc => hx1 ⟨y, hc, rfl⟩, fun hc => hx2 ⟨y, hc, rfl⟩⟩, rfl⟩
  · rintro ⟨y, ⟨hy, hy1, hy2⟩, rfl⟩
    refine ⟨⟨y, hy, rfl⟩, ?_, ?_⟩
    · rintro ⟨z, hz, hzy⟩
      exact hy1 (Subtype.val_injective hzy ▸ hz)
    · rintro ⟨z, hz, hzy⟩
      exact hy2 (Subtype.val_injective hzy ▸ hz)

theorem IsPrimeCyclicTIHyp.isCyclicTIPair_map (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        ((fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂)
      = (fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) '' ((fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂)
        ∩ (fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂ = ∅) :
    IsCyclicTIPair (W₁.map L.subtype ⊔ W₂.map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) where
  left_ne_bot := fun hc =>
    h.left_ne_bot ((Subgroup.map_eq_bot_iff_of_injective W₁ L.subtype_injective).1 hc)
  right_ne_bot := fun hc =>
    h.right_ne_bot ((Subgroup.map_eq_bot_iff_of_injective W₂ L.subtype_injective).1 hc)
  mul_eq := by
    rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, ← h.coe_sup_eq_mul,
      ← Subgroup.map_sup, Subgroup.coe_map]
  inf_eq_bot := by
    rw [← Subgroup.map_inf _ _ _ L.subtype_injective, h.inf_left_right_eq_bot, Subgroup.map_bot]
  commute := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    exact congrArg (fun z : ↥L => (z : G)) (h.commute_left_right a ha b hb).eq
  isCyclic := by
    rw [← Subgroup.map_sup]
    exact (isCyclic_map_subtype_iff (W₁ ⊔ W₂)).2 h.isCyclic_sup
  odd_natCard := by
    rw [← Subgroup.map_sup, Subgroup.card_map_of_injective L.subtype_injective,
      h.natCard_sup_eq_mul]
    exact h.odd_natCard
  setOf_conj_eq_self := by
    rw [cyclicTIDiff_map_subtype_eq_image, hstab, ← Subgroup.map_sup]
  inter_eq_empty := by
    intro g hg
    rw [cyclicTIDiff_map_subtype_eq_image]
    exact hdisj g (by rwa [Subgroup.map_sup])

theorem IsPrimeCyclicTIHyp.primeTIrow_principal [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) :
    h.primeTIrow σ (principalIrr ↥W₂) = indClassFun K (1 : ↥K → ℂ) := by
  rw [← h.indClassFun_primeTIres hσ, h.primeTIres_principal hσ]

theorem IsPrimeCyclicTIHyp.index_eq (h : IsPrimeCyclicTIHyp K W₁ W₂) :
    K.index = Nat.card ↥W₁ := h.isComplement'_left.index_eq_card

theorem IsPrimeCyclicTIHyp.primeTIrow_sub_apply_eq_zero [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hζS : ζ ∈ indFam K (Irr ↥K \ {1}))
    (hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) {x : ↥L} (hx : x ∉ (K : Set ↥L) \ {1}) :
    h.primeTIrow σ (principalIrr ↥W₂) x - ζ x = 0 := by
  have hK := h.normal
  have hmem := NormalInducedFamily.indClassFun_one_sub_mem_dadeDomain
    (L := L) (A := (fun y : ↥L => (y : G)) '' ((K : Set ↥L) \ {1})) (H := K) rfl hζS
    (by rw [hζ1, h.index_eq])
  have hx' : (x : G) ∉ (fun y : ↥L => (y : G)) '' ((K : Set ↥L) \ {1}) := by
    rintro ⟨y, hy, hyx⟩
    exact hx (Subtype.val_injective hyx ▸ hy)
  have hz := (mem_dadeDomain.1 hmem).2 x hx'
  rw [h.primeTIrow_principal hσ]
  simpa using hz

theorem IsPrimeCyclicTIHyp.primeTIrow_sub_mem_dadeDomain [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hζS : ζ ∈ indFam K (Irr ↥K \ {1}))
    (hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ
      ∈ dadeDomain L (primeDadeSupport (G := G) K W₁ W₂) := by
  have hK := h.normal
  rw [h.primeTIrow_principal hσ]
  exact dadeDomain_mono image_sdiff_subset_primeDadeSupport
    (NormalInducedFamily.indClassFun_one_sub_mem_dadeDomain rfl hζS (by rw [hζ1, h.index_eq]))

theorem IsPrimeCyclicTIHyp.primeTIrow_sub_mem_span_Irr [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ ∈ Submodule.span ℤ (Irr ↥L) := by
  have hK := h.normal
  rw [h.primeTIrow_principal hσ]
  exact NormalInducedFamily.indClassFun_one_sub_mem_span_Irr hζS

theorem IsPrimeCyclicTIHyp.cfInner_self_primeTIrow_sub [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hζS : ζ ∈ indFam K (Irr ↥K \ {1}))
    (hζIrr : ζ ∈ Irr ↥L) :
    cfInner (h.primeTIrow σ (principalIrr ↥W₂) - ζ) (h.primeTIrow σ (principalIrr ↥W₂) - ζ)
      = (Nat.card ↥W₁ : ℂ) + 1 := by
  have hK := h.normal
  rw [h.primeTIrow_principal hσ,
    NormalInducedFamily.cfInner_self_indClassFun_one_sub hζS hζIrr, h.index_eq]

theorem IsPrimeCyclicTIHyp.cfInner_primeTIrow_sub_one [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
    [Fintype ↑(Irr ↥W₁)] (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) :
    cfInner (h.primeTIrow σ (principalIrr ↥W₂) - ζ) (1 : ↥L → ℂ) = 1 := by
  have hK := h.normal
  rw [h.primeTIrow_principal hσ, NormalInducedFamily.cfInner_indClassFun_one_sub_one hζS]

theorem IsCyclicTIPair.exists_virtualChar_norm_one_prodCharEta {H : Type*} [Group H] [Fintype H]
    {W V₁ V₂ : Subgroup H} [Fintype ↥W] [Fintype ↑(Irr ↥V₁)]
    {ω : classFun ↥W →ₗ[ℂ] classFun H}
    (hW : IsCyclicTIPair W V₁ V₂) (hω : IsCyclicTIIsometry W V₁ V₂ ω)
    {f : H → ℂ} (hf : f ∈ Submodule.span ℤ (Irr H))
    (hnorm : cfInner f f = (Nat.card ↥V₁ : ℂ) + 1)
    (hf1 : cfInner f (1 : H → ℂ) = 1)
    (hfV : ∀ x ∈ cyclicTIDiff W V₁ V₂, f x = 0)
    (hcard : Nat.card ↥V₁ < Nat.card ↥V₂) :
    ∃ χ ∈ Submodule.span ℤ (Irr H), cfInner χ χ = 1 ∧
      (∀ (i : Irr ↥V₁) (j : Irr ↥V₂), IsOrthogonal χ (hW.prodCharEta ω i j)) ∧
      f = (∑ i : Irr ↥V₁, hW.prodCharEta ω i (principalIrr ↥V₂)) - χ := by
  classical
  have hfin2 : Finite ↥V₂ := hW.finite_right
  have hFJ : Fintype (Irr ↥V₂) := Fintype.ofFinite _
  have hηorth : IsOrthonormalFamily
      fun p : Irr ↥V₁ × Irr ↥V₂ => hW.prodCharEta ω p.1 p.2 :=
    IsOrthonormalFamily.of_cfInner_eq_ite fun z z' => hW.cfInner_prodCharEta_pair hω z z'
  have hηmem : ∀ (i : Irr ↥V₁) (j : Irr ↥V₂),
      hW.prodCharEta ω i j ∈ Submodule.span ℤ (Irr H) := fun i j =>
    virtualChars_le_span_Irr (hW.prodCharEta_mem_virtualChars hω i j)
  have hcI : Fintype.card (Irr ↥V₁) = Nat.card ↥V₁ := by
    rw [← Nat.card_eq_fintype_card]; exact hW.card_Irr_left
  have hcJ : Fintype.card (Irr ↥V₂) = Nat.card ↥V₂ := by
    rw [← Nat.card_eq_fintype_card]; exact hW.card_Irr_right
  have hm : 2 ≤ Fintype.card (Irr ↥V₁) := by
    rw [hcI]; exact le_trans (by norm_num) hW.three_le_natCard_left
  have hq : (Fintype.card (Irr ↥V₁) : ℤ) + 1 < Fintype.card (Irr ↥V₂) := by
    obtain ⟨a, ha⟩ := hW.odd_natCard_left
    obtain ⟨b, hb⟩ := hW.odd_natCard_right
    rw [hcI, hcJ]
    have hlt : Nat.card ↥V₁ + 1 < Nat.card ↥V₂ := by omega
    exact_mod_cast hlt
  have h00 : cfInner f (hW.prodCharEta ω (principalIrr ↥V₁) (principalIrr ↥V₂)) = 1 := by
    rw [hW.prodCharEta_principal hω, hf1]
  have hnorm' : cfInner f f = (Fintype.card (Irr ↥V₁) : ℂ) + 1 := by rw [hnorm, hcI]
  have hexch : ∀ (i : Irr ↥V₁) (j : Irr ↥V₂),
      cfInner f (hW.prodCharEta ω i j)
          + cfInner f (hW.prodCharEta ω (principalIrr ↥V₁) (principalIrr ↥V₂))
        = cfInner f (hW.prodCharEta ω i (principalIrr ↥V₂))
          + cfInner f (hW.prodCharEta ω (principalIrr ↥V₁) j) := fun i j =>
    hW.cfInner_prodCharEta_exchange hω (mem_classFun_of_mem_span_Irr hf) hfV i j
  obtain ⟨-, -, χ, hχmem, hχnorm, hχorth, hfeq⟩ :=
    AnchoredLowNormRectangle.exists_virtualChar_norm_one
      (η := fun (i : Irr ↥V₁) (j : Irr ↥V₂) => hW.prodCharEta ω i j) (f := f)
      (i₀ := principalIrr ↥V₁) (j₀ := principalIrr ↥V₂) hηorth hηmem hf hm hq hnorm' h00 hexch
  exact ⟨χ, hχmem, hχnorm, hχorth, hfeq⟩

theorem IsPrimeCyclicTIHyp.exists_virtualChar_norm_one_dadeMap_primeTIrow_sub [Fintype G]
    [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
    [Fintype ↥(W₁.map L.subtype ⊔ W₂.map L.subtype)] [Fintype ↑(Irr ↥(W₁.map L.subtype))]
    {T : G → Subgroup G}
    {ω : classFun ↥(W₁.map L.subtype ⊔ W₂.map L.subtype) →ₗ[ℂ] classFun G}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (hζS : ζ ∈ indFam K (Irr ↥K \ {1})) (hζIrr : ζ ∈ Irr ↥L)
    (hζ1 : ζ 1 = (Nat.card ↥W₁ : ℂ)) (_hodd : Odd (Nat.card G))
    (hstab : {g : G | (fun x => g⁻¹ * x * g) ''
        ((fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂)
      = (fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂}
      = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G))
    (hdisj : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
      (fun x => g⁻¹ * x * g) '' ((fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂)
        ∩ (fun x : ↥L => (x : G)) '' cyclicTIset W₁ W₂ = ∅)
    (hD : IsDadeData L (primeDadeSupport (G := G) K W₁ W₂) T)
    (hω : IsCyclicTIIsometry (W₁.map L.subtype ⊔ W₂.map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype) ω)
    (hm : Nat.card ↥W₁ < Nat.card ↥W₂) :
    (∀ x : ↥L, x ∉ (K : Set ↥L) \ {1} →
        h.primeTIrow σ (principalIrr ↥W₂) x - ζ x = 0) ∧
      ∃ χ ∈ Submodule.span ℤ (Irr G), cfInner χ χ = 1 ∧
        (∀ (i : Irr ↥(W₁.map L.subtype)) (j : Irr ↥(W₂.map L.subtype)),
          IsOrthogonal χ ((h.isCyclicTIPair_map hstab hdisj).prodCharEta ω i j)) ∧
        ((dadeMap hD ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
              h.primeTIrow_sub_mem_dadeDomain hσ hζS hζ1⟩ : classFun G) : G → ℂ)
          = (∑ i : Irr ↥(W₁.map L.subtype),
              (h.isCyclicTIPair_map hstab hdisj).prodCharEta ω i
                (principalIrr ↥(W₂.map L.subtype))) - χ := by
  classical
  have hK := h.normal
  set hWa := h.isCyclicTIPair_map hstab hdisj with hWadef
  set β : ↥L → ℂ := h.primeTIrow σ (principalIrr ↥W₂) - ζ with hβ
  have hβdom : β ∈ dadeDomain L (primeDadeSupport (G := G) K W₁ W₂) :=
    h.primeTIrow_sub_mem_dadeDomain hσ hζS hζ1
  set f : G → ℂ := ((dadeMap hD ⟨β, hβdom⟩ : classFun G) : G → ℂ) with hf
  have hfint : f ∈ Submodule.span ℤ (Irr G) :=
    hD.dadeMap_mem_span_Irr hβdom (h.primeTIrow_sub_mem_span_Irr hσ hζS)
  have hfnorm : cfInner f f = (Nat.card ↥(W₁.map L.subtype) : ℂ) + 1 := by
    rw [hf, cfInner_self_dadeMap hD ⟨β, hβdom⟩,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact h.cfInner_self_primeTIrow_sub hσ hζS hζIrr
  have hf1 : cfInner f (1 : G → ℂ) = 1 := by
    rw [hf, NormalInducedFamily.cfInner_dadeMap_one hD ⟨β, hβdom⟩]
    exact h.cfInner_primeTIrow_sub_one hσ hζS
  have hfV : ∀ x ∈ cyclicTIDiff (W₁.map L.subtype ⊔ W₂.map L.subtype) (W₁.map L.subtype)
      (W₂.map L.subtype), f x = 0 := by
    intro x hx
    rw [cyclicTIDiff_map_subtype_eq_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyA : (y : G) ∈ primeDadeSupport (G := G) K W₁ W₂ :=
      coe_mem_primeDadeSupport_of_mem_cyclicTIset hy
    rw [hf, dadeMap_apply_mem hD ⟨β, hβdom⟩ hyA]
    have hyK : (⟨(y : G), hD.mem_of_mem hyA⟩ : ↥L) ∉ (K : Set ↥L) \ {1} := by
      rintro ⟨hmem, -⟩
      exact h.notMem_of_mem_cyclicTIset hy (by simpa using hmem)
    have hz := h.primeTIrow_sub_apply_eq_zero hσ hζS hζ1 hyK
    simpa [hβ] using hz
  have hcard : Nat.card ↥(W₁.map L.subtype) < Nat.card ↥(W₂.map L.subtype) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective L.subtype_injective]
    exact hm
  exact ⟨fun x hx => h.primeTIrow_sub_apply_eq_zero hσ hζS hζ1 hx,
    hWa.exists_virtualChar_norm_one_prodCharEta hω hfint hfnorm hf1 hfV hcard⟩

end CFSG.FeitThompson
