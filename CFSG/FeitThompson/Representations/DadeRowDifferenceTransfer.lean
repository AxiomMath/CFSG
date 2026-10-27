module

public import CFSG.FeitThompson.Representations.PrimeTILocalBridgeSupportNorm
public import CFSG.FeitThompson.Representations.CoherenceDeterminesUniformBridgeImage
import CFSG.FeitThompson.Representations.PrimeDadeRowDifferenceSupport
import CFSG.FeitThompson.Representations.MixedValuesNormTwoArrayDifference
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace IsPrimeCyclicTIHyp

variable {G : Type*} [Group G] {L : Subgroup G} {K W₁ W₂ : Subgroup ↥L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}

section Local

variable [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]

theorem primeTIirr_sub_mem_dadeDomain {A₀ : Set G} (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H)
    {A : Set ↥L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1) :
    h.primeTIirr σ i j - h.primeTIirr σ i k ∈ dadeDomain L A₀ :=
  mem_dadeDomain_of_mem_span_Irr
    (sub_mem (Submodule.subset_span (h.primeTIirr_mem_Irr hσ i j))
      (Submodule.subset_span (h.primeTIirr_mem_Irr hσ i k)))
    fun x hx => h.primeTIirr_sub_eq_zero_of_notMem_bridgeSupport hσ hWH hA i hj hk hone
      fun hc => hx (hA₀ ⟨x, hc, rfl⟩)

theorem cfInner_self_primeTIirr_sub (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) {j k : Irr ↥W₂} (hjk : j ≠ k) :
    cfInner (h.primeTIirr σ i j - h.primeTIirr σ i k)
      (h.primeTIirr σ i j - h.primeTIirr σ i k) = 2 := by
  have e1 : cfInner (h.primeTIirr σ i j) (h.primeTIirr σ i j) = 1 := by
    simpa using h.cfInner_primeTIirr_eq_ite hσ (i, j) (i, j)
  have e2 : cfInner (h.primeTIirr σ i j) (h.primeTIirr σ i k) = 0 := by
    simpa [hjk] using h.cfInner_primeTIirr_eq_ite hσ (i, j) (i, k)
  have e3 : cfInner (h.primeTIirr σ i k) (h.primeTIirr σ i j) = 0 := by
    simpa [Ne.symm hjk] using h.cfInner_primeTIirr_eq_ite hσ (i, k) (i, j)
  have e4 : cfInner (h.primeTIirr σ i k) (h.primeTIirr σ i k) = 1 := by
    simpa using h.cfInner_primeTIirr_eq_ite hσ (i, k) (i, k)
  rw [cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, e1, e2, e3, e4]
  ring

theorem primeTIirr_sub_apply_of_mem_cyclicTIset (h : IsPrimeCyclicTIHyp K W₁ W₂)
    (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (i : Irr ↥W₁) {j k : Irr ↥W₂}
    (hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1) {v : ↥(W₁ ⊔ W₂)}
    (hv : (v : ↥L) ∈ cyclicTIset W₁ W₂) :
    (h.primeTIirr σ i j - h.primeTIirr σ i k) (v : ↥L)
      = h.primeTISign σ j *
        (h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ) (j : ↥W₂ → ℂ) v
          - h.isCyclicTIPair.prodChar (i : ↥W₁ → ℂ) (k : ↥W₂ → ℂ) v) := by
  have hB : (v : ↥L) ∈ primeTIset W₁ W₂ := cyclicTIset_subset_primeTIset hv
  rw [Pi.sub_apply, h.primeTIirr_apply_of_mem_primeTIset hσ i j hB,
    h.primeTIirr_apply_of_mem_primeTIset hσ i k hB,
    ← h.primeTISign_eq_of_primeTIirr_one_eq hσ i j k hone]
  ring

end Local

section Transfer

variable [Fintype G] [Fintype ↥L] [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]

theorem dadeMap_primeTIirr_sub_eq {A₀ : Set G} {T : G → Subgroup G}
    {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    {H : Subgroup ↥L} [H.Normal] (hWH : W₂ ≤ H) {A : Set ↥L}
    (hA : ∀ y ∈ H, y ≠ 1 → ((K ⊓ Subgroup.centralizer {y} : Subgroup ↥L) : Set ↥L) \ {1} ⊆ A)
    (hA₀ : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀)
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
    (i : Irr ↥W₁) {j k : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂)
    (hone : h.primeTIirr σ i j 1 = h.primeTIirr σ i k 1) :
    ((dadeMap hD ⟨h.primeTIirr σ i j - h.primeTIirr σ i k,
          h.primeTIirr_sub_mem_dadeDomain hσ hWH hA hA₀ i hj hk hone⟩ : classFun G) : G → ℂ)
      = h.primeTISign σ j •
          ((h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ j)
            - (h.isCyclicTIPair_map_subtype hstab hdisj).prodCharEta ω
              (irrMapSubtype L W₁ i) (irrMapSubtype L W₂ k)) := by
  classical
  set hW := h.isCyclicTIPair_map_subtype hstab hdisj with hWdef
  set hmem := h.primeTIirr_sub_mem_dadeDomain hσ hWH hA hA₀ i hj hk hone with hmemdef
  rcases eq_or_ne j k with rfl | hjk
  · have h0 : (⟨h.primeTIirr σ i j - h.primeTIirr σ i j, hmem⟩ : dadeDomain L A₀) = 0 :=
      Subtype.ext (sub_self _)
    rw [h0, map_zero]
    simp
  set f : G → ℂ := ((dadeMap hD ⟨h.primeTIirr σ i j - h.primeTIirr σ i k, hmem⟩ :
    classFun G) : G → ℂ) with hfdef
  have hne : (irrMapSubtype L W₁ i, irrMapSubtype L W₂ j)
      ≠ (irrMapSubtype L W₁ i, irrMapSubtype L W₂ k) := by
    intro hc
    exact hjk (irrMapSubtype_injective L W₂ (congrArg Prod.snd hc))
  have hfint : f ∈ Submodule.span ℤ (Irr G) :=
    hD.dadeMap_mem_span_Irr hmem
      (sub_mem (Submodule.subset_span (h.primeTIirr_mem_Irr hσ i j))
        (Submodule.subset_span (h.primeTIirr_mem_Irr hσ i k)))
  have hfnorm : cfInner f f = 2 := by
    rw [hfdef, cfInner_self_dadeMap hD]
    exact h.cfInner_self_primeTIirr_sub hσ i hjk
  have hfV : ∀ v : ↥((W₁ ⊔ W₂).map L.subtype),
      (v : G) ∈ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) →
      f (v : G) = h.primeTISign σ j *
        (hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((irrMapSubtype L W₂ j : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v
          - hW.prodChar ((irrMapSubtype L W₁ i : Irr ↥(W₁.map L.subtype)) : _ → ℂ)
            ((irrMapSubtype L W₂ k : Irr ↥(W₂.map L.subtype)) : _ → ℂ) v) := by
    intro v hv
    rw [← image_cyclicTIset_eq] at hv
    obtain ⟨u, hu, huv⟩ := hv
    have huW : u ∈ W₁ ⊔ W₂ := (mem_cyclicTIset.1 hu).1
    set uu : ↥(W₁ ⊔ W₂) := ⟨u, huW⟩ with huu
    have hveq : mapSubtypeEquiv L (W₁ ⊔ W₂) uu = v :=
      Subtype.ext (by rw [coe_mapSubtypeEquiv]; exact huv)
    have huA : (u : G) ∈ A₀ :=
      hA₀ ⟨u, cyclicTIsetConj_subset_bridgeSupport
        (cyclicTIset_subset_cyclicTIsetConj _ _ hu), rfl⟩
    have hval : f (u : G) = (h.primeTIirr σ i j - h.primeTIirr σ i k) u := by
      rw [hfdef, dadeMap_apply_mem hD _ huA]
    rw [← huv, hval, h.primeTIirr_sub_apply_of_mem_cyclicTIset hσ i hone (v := uu) hu,
      ← hveq, prodChar_irrMapSubtype h.isCyclicTIPair hW,
      prodChar_irrMapSubtype h.isCyclicTIPair hW]
  exact hW.eq_signed_sub_prodCharEta hω hne
    (h.primeTISign_eq_one_or_eq_neg_one (σ := σ) j) hfint hfnorm hfV

end Transfer

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson

end
