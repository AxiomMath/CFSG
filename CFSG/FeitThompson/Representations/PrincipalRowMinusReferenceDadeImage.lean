module

public import CFSG.FeitThompson.Representations.CoherentLocalRowImagesColumnSum
import CFSG.FeitThompson.Representations.PrimeDadePrincipalRowSmallComplement

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

section Rows

variable {L : Type*} [Group L] [Fintype L] {K W₁ W₂ : Subgroup L} [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↑(Irr ↥W₁)] {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L} {ζ : L → ℂ} {d n δ : ℤ}
  {h : IsPrimeCyclicTIHyp K W₁ W₂}

theorem sum_primeTIbridge_eq (hB : h.IsUniformBridgeData σ ζ d n δ) (j : Irr ↥W₂) :
    ∑ i : Irr ↥W₁, h.primeTIbridge σ ζ δ n i j
      = h.primeTIrow σ j - (d : ℂ) • ζ
        - (δ : ℂ) • (h.primeTIrow σ (principalIrr ↥W₂) - ζ) := by
  have hcard : (Fintype.card ↑(Irr ↥W₁) : ℂ) = (Nat.card ↥W₁ : ℂ) := by
    rw [← Nat.card_eq_fintype_card, h.isCyclicTIPair.card_Irr_left]
  funext x
  simp only [Finset.sum_apply, h.primeTIbridge_apply, h.primeTIrow_def, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, hcard]
  linear_combination (ζ x) * hB.sub_eq_complex

end Rows

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
theorem primeTIrow_principal_sub_mem_dadeZDomain :
    h.primeTIrow σ (principalIrr ↥W₂) - ζ ∈ dadeZDomain L A := by
  refine mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr
    (h.primeTIrow_sub_mem_span_Irr hC.local_data.isometry hC.local_data.mem_indFam),
    fun x hx => ?_⟩
  refine h.primeTIrow_sub_apply_eq_zero hC.local_data.isometry hC.local_data.mem_indFam
    hC.local_data.apply_one (fun hmem => hx ?_)
  exact hC.image_puncturedCore_subset ⟨x, hmem, rfl⟩

noncomputable def tauPrincipalRowSub
    (hC : IsUniformBridgeCoherenceData h σ ζ d n δ A T ω ν) : G → ℂ :=
  ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
    hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ)

omit [K.Normal] in
theorem tauPrincipalRowSub_def : hC.tauPrincipalRowSub
    = ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
      hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ) := (rfl)

omit [K.Normal] in
include hC in
theorem tauPrincipalRowSub_mem_virtualChars : hC.tauPrincipalRowSub ∈ virtualChars G :=
  dadeZMap_mem_virtualChars hC.isDadeData _

omit [K.Normal] in
include hC in
theorem cfInner_self_tauPrincipalRowSub :
    cfInner hC.tauPrincipalRowSub hC.tauPrincipalRowSub = (Nat.card ↥W₁ : ℂ) + 1 := by
  rw [tauPrincipalRowSub, cfInner_dadeZMap]
  exact h.cfInner_self_primeTIrow_sub hC.local_data.isometry hC.local_data.mem_indFam
    hC.local_data.mem_Irr

omit [Fintype ↑(Irr ↥W₁)] in
include hC in
theorem coe_nu_eq_dadeZMap {f : ↥L → ℂ} (hf : f ∈ charSpanZero (indFam K (Irr ↥K \ {1}))) :
    (ν ⟨f, charSpanZero_le _ hf⟩ : G → ℂ)
      = ((dadeZMap hC.isDadeData ⟨f, hC.mem_dadeZDomain_of_mem_charSpanZero hf⟩ :
          charSpanZero (Irr G)) : G → ℂ) := by
  rw [coe_dadeZMap]
  exact hC.nu_eq_tau _ ⟨f, mem_dadeDomain_of_mem_dadeZDomain
    (hC.mem_dadeZDomain_of_mem_charSpanZero hf)⟩ rfl

include hC in
theorem smul_tauPrincipalRowSub {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    (δ : ℂ) • hC.tauPrincipalRowSub
      = hC.nuRow hj - (d : ℂ) • hC.nuZeta - ∑ i : Irr ↥W₁, hC.tauBridge i hj := by
  have hf := primeTIrow_sub_smul_zeta_mem_charSpanZero hC.local_data hj
  have key : δ • (⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
        hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : dadeZDomain L A)
      = ⟨h.primeTIrow σ j - (d : ℂ) • ζ, hC.mem_dadeZDomain_of_mem_charSpanZero hf⟩
        - ∑ i : Irr ↥W₁, (⟨h.primeTIbridge σ ζ δ n i j,
            primeTIbridge_mem_dadeZDomain hC.local_data hC.image_subset i hj⟩ :
              dadeZDomain L A) := by
    refine Subtype.ext ?_
    push_cast
    rw [sum_primeTIbridge_eq hC.local_data j,
      show (δ : ℂ) • (h.primeTIrow σ (principalIrr ↥W₂) - ζ)
        = δ • (h.primeTIrow σ (principalIrr ↥W₂) - ζ) from Int.cast_smul_eq_zsmul _ _ _]
    abel
  have hmap := congrArg (fun z : charSpanZero (Irr G) => (z : G → ℂ))
    (congrArg (dadeZMap hC.isDadeData) key)
  simp only [map_zsmul, map_sub, map_sum] at hmap
  push_cast at hmap
  rw [tauPrincipalRowSub, hC.nuRow_sub_smul_nuZeta hj, hC.coe_nu_eq_dadeZMap hf]
  simp only [hC.tauBridge_def]
  rw [show (δ : ℂ) • ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
      hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ)
    = δ • ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
      hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ) from
      Int.cast_smul_eq_zsmul _ _ _]
  exact hmap

include hC in
theorem sum_tauBridge_eq {j : Irr ↥W₂} (hj : j ≠ principalIrr ↥W₂) :
    ∑ i : Irr ↥W₁, hC.tauBridge i hj
      = (δ : ℂ) • (∑ i : Irr ↥W₁, hC.etaLocal i j
          - ∑ i : Irr ↥W₁, hC.etaLocal i (principalIrr ↥W₂))
        - ((Nat.card ↥W₁ : ℂ) * (n : ℂ)) • hC.nuZeta := by
  have hcard : (Fintype.card ↑(Irr ↥W₁) : ℂ) = (Nat.card ↥W₁ : ℂ) := by
    rw [← Nat.card_eq_fintype_card, h.isCyclicTIPair.card_Irr_left]
  rw [Finset.sum_congr rfl fun i _ => hC.tauBridge_eq_etaLocal i hj]
  funext x
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcard]
  ring

include hC in
theorem tauPrincipalRowSub_eq :
    hC.tauPrincipalRowSub = ∑ i : Irr ↥W₁, hC.etaLocal i (principalIrr ↥W₂) - hC.nuZeta := by
  classical
  have : Fintype ↑(Irr ↥W₂) := Fintype.ofFinite _
  obtain ⟨j, -, hj⟩ := exists_ne_ne_of_isPrimeCyclicTIHyp h (principalIrr ↥W₂)
  have hkey := hC.smul_tauPrincipalRowSub hj
  rw [hC.sum_tauBridge_eq hj, hC.nuRow_eq_smul_sum_etaLocal hj] at hkey
  have hδ : (δ : ℂ) * (δ : ℂ) = 1 := hC.local_data.sign_sq
  have hd := hC.local_data.sub_eq_complex
  funext x
  have hx := congrFun hkey x
  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at hx ⊢
  linear_combination (δ : ℂ) * hx
    - (hC.tauPrincipalRowSub x - (∑ i : Irr ↥W₁, hC.etaLocal i (principalIrr ↥W₂) x)
        + hC.nuZeta x) * hδ
    - (δ : ℂ) * hC.nuZeta x * hd

include hC in
theorem dadeZMap_primeTIrow_principal_sub_eq :
    ((dadeZMap hC.isDadeData ⟨h.primeTIrow σ (principalIrr ↥W₂) - ζ,
        hC.primeTIrow_principal_sub_mem_dadeZDomain⟩ : charSpanZero (Irr G)) : G → ℂ)
      = ∑ i : Irr ↥W₁, hC.isCyclicTIPair.prodCharEta ω (irrMapSubtype L W₁ i)
            (principalIrr ↥(W₂.map L.subtype))
        - (ν ⟨ζ, Submodule.subset_span hC.local_data.mem_indFam⟩ : G → ℂ) := by
  rw [← hC.tauPrincipalRowSub_def, hC.tauPrincipalRowSub_eq, hC.nuZeta_def]
  simp only [hC.etaLocal_def, irrMapSubtype_principal]

end IsUniformBridgeCoherenceData

end CFSG.FeitThompson

end
