module

public import CFSG.FeitThompson.Representations.PrincipalRowMinusReferenceDadeImage
public import CFSG.FeitThompson.Representations.CyclicTITwoColumnHalfSelection
import CFSG.FeitThompson.Representations.PrincipalCyclicTIAxisOddSum
import CFSG.FeitThompson.Representations.CoherentInducedImageVanishesMixedTI
import CFSG.FeitThompson.Representations.PrimeDadePrincipalRowSmallComplement
import CFSG.FeitThompson.Representations.FrobeniusAbelianKernelInducedCharacters

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Transport

variable {G : Type*} [Group G]

theorem irrMapSubtype_surjective (L : Subgroup G) (W : Subgroup ↥L) :
    Function.Surjective (irrMapSubtype L W) := by
  intro j
  refine ⟨⟨(j : ↥(W.map L.subtype) → ℂ) ∘ (mapSubtypeEquiv L W),
    FrobeniusInduction.mem_Irr_comp_mulEquiv j.2 (mapSubtypeEquiv L W)⟩, ?_⟩
  refine Subtype.ext ?_
  rw [coe_irrMapSubtype]
  funext x
  simp

theorem irrMapSubtype_bijective (L : Subgroup G) (W : Subgroup ↥L) :
    Function.Bijective (irrMapSubtype L W) :=
  ⟨irrMapSubtype_injective L W, irrMapSubtype_surjective L W⟩

end Transport

namespace IsUniformBridgeCoherenceData

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ : Subgroup ↥L} [K.Normal] [Fintype ↥(W₁ ⊔ W₂)] [Fintype ↑(Irr ↥W₁)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {h : IsPrimeCyclicTIHyp K W₁ W₂} {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L}
  {ζ : ↥L → ℂ} {d n δ : ℤ} {A : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}
  {ν : Submodule.span ℤ (indFam K (Irr ↥K \ {1})) →+ virtualChars G}
  (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν)

omit [K.Normal] in
include hC in
theorem primeTIrow_principal_sub_mem_dadeZDomain_puncturedCore :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ
      ∈ dadeZDomain L ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) := by
  refine mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
    (h.primeTIrow_sub_mem_span_Irr hC.local_data.isometry hC.local_data.mem_indFam),
    fun x hx => ?_⟩
  exact h.primeTIrow_sub_apply_eq_zero hC.local_data.isometry hC.local_data.mem_indFam
    hC.local_data.apply_one (fun hmem => hx ⟨x, hmem, rfl⟩)

include hC in
theorem tauPrincipalRowSub_apply_eq_zero_of_notMem {g : G}
    (hg : g ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T) :
    hC.tauPrincipalRowSub g = 0 := by
  have hDB := isDadeData_puncturedCore hC.isDadeData hC.image_puncturedCore_subset
  have hfB : h.primeTIrow σ (principalIrr ↥W₂) - ζ
      ∈ dadeDomain L ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) :=
    mem_dadeDomain_of_mem_dadeZDomain hC.primeTIrow_principal_sub_mem_dadeZDomain_puncturedCore
  have key : hC.tauPrincipalRowSub
      = ((dadeMap hDB ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ, hfB⟩ : classFun G) : G → ℂ) := by
    rw [hC.tauPrincipalRowSub_def, coe_dadeZMap]
    exact dadeMap_eq_dadeMap_of_subset hC.isDadeData hDB hC.image_puncturedCore_subset hfB _
  rw [key]
  exact dadeMap_eq_zero_of_notMem hDB _ hg

omit [K.Normal] in
include hC in
theorem sum_etaLocal_principal_eq_prodCharEtaColSum :
    ∑ i : Irr ↥W₁, hC.etaLocal i (principalIrr ↥W₂)
      = hC.isCyclicTIPair.prodCharEtaColSum ω (principalIrr ↥(W₂.map L.subtype)) := by
  have : Fintype ↑(Irr ↥(W₁.map L.subtype)) := Fintype.ofFinite _
  rw [hC.isCyclicTIPair.prodCharEtaColSum_eq_sum]
  refine Fintype.sum_bijective (irrMapSubtype L W₁) (irrMapSubtype_bijective L W₁)
    (fun i => hC.etaLocal i (principalIrr ↥W₂))
    (fun i' => hC.isCyclicTIPair.prodCharEta ω i' (principalIrr ↥(W₂.map L.subtype)))
    fun i => ?_
  rw [hC.etaLocal_def, irrMapSubtype_principal]

include hC in
theorem nuZeta_apply_eq_sum_etaLocal {g : G}
    (hg : g ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T) :
    hC.nuZeta g = ∑ i : Irr ↥W₁, hC.etaLocal i (principalIrr ↥W₂) g := by
  have hkey := congrFun hC.tauPrincipalRowSub_eq g
  rw [hC.tauPrincipalRowSub_apply_eq_zero_of_notMem hg] at hkey
  simp only [Pi.sub_apply, Finset.sum_apply] at hkey
  linear_combination hkey

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem exists_odd_int_nuZeta_apply {g : G}
    (hg : g ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T)
    (hgc : (orderOf g).Coprime (Nat.card ↥W₁)) :
    ∃ m : ℤ, Odd m ∧ hC.nuZeta g = (m : ℂ) := by
  have := h.isCyclicTIPair.finite_left
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  have hcard : Nat.card ↥(W₁.map L.subtype) = Nat.card ↥W₁ :=
    Subgroup.card_map_of_injective (K := W₁) L.subtype_injective
  obtain ⟨m, hodd, hm⟩ := hC.isCyclicTIPair.exists_odd_int_prodCharEtaColSum hC.omega_isometry
    (g := g) (by rwa [hcard])
  refine ⟨m, hodd, ?_⟩
  rw [hC.nuZeta_apply_eq_sum_etaLocal hg, ← Finset.sum_apply,
    hC.sum_etaLocal_principal_eq_prodCharEtaColSum, hm]

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem one_le_norm_nuZeta_apply {g : G}
    (hg : g ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T)
    (hgc : (orderOf g).Coprime (Nat.card ↥W₁)) : 1 ≤ ‖hC.nuZeta g‖ := by
  obtain ⟨m, hodd, hm⟩ := hC.exists_odd_int_nuZeta_apply hg hgc
  have hm0 : m ≠ 0 := by rintro rfl; simp at hodd
  rw [hm, Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hm0

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem nuZeta_apply_ne_zero {g : G}
    (hg : g ∉ totalDadeSupport ((fun x : ↥L => (x : G)) '' ((K : Set ↥L) \ {1})) T)
    (hgc : (orderOf g).Coprime (Nat.card ↥W₁)) : hC.nuZeta g ≠ 0 := by
  intro he
  have hle := hC.one_le_norm_nuZeta_apply hg hgc
  rw [he, norm_zero] at hle
  exact absurd hle (by norm_num)

end IsUniformBridgeCoherenceData

end CFSG.FeitThompson

end
