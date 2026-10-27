module

public import CFSG.FeitThompson.Representations.PrimeTILocalBridgeSupportNorm
public import CFSG.FeitThompson.Representations.CoherenceDeterminesUniformBridgeImage
public import CFSG.FeitThompson.Representations.CyclicTIAxesNonrealConjugatePairs
import CFSG.FeitThompson.Representations.DadeRowDifferenceTransfer
import CFSG.FeitThompson.Representations.CoherentInducedFamilyOrthogonalPrincipal
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
public import CFSG.FeitThompson.Representations.RealBridgeRemainderProjectionBound

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open scoped ComplexConjugate

section Local

variable {L : Type*} [Group L] [Fintype L] {K W₁ W₂ H U : Subgroup L} [H.Normal] {A : Set L}
  [Fintype ↥(W₁ ⊔ W₂)] {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}
  {hc : IsPrimeTIBridgeConfig K W₁ W₂ H U A}

namespace IsPrimeTIBridgeConfig

theorem conj_bridgeChar_apply (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {j : Irr ↥W₂}
    (hd : hc.primeCyclicTI.primeTISign σ j = 1)
    (hd' : hc.primeCyclicTI.primeTISign σ (starIrr j) = 1) (x : L) :
    conj (hc.bridgeChar (σ := σ) (H := H) (j := j) x)
      = hc.bridgeChar (σ := σ) (H := H) (j := starIrr j) x := by
  have hst := hc.primeCyclicTI.isCyclicTIPair.star_prodCharEta hσ
    (i := principalIrr ↥W₁) (k := principalIrr ↥W₁) (j := j) (l := starIrr j)
    (by simp) (by simp)
  have hmu : conj (hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j x)
      = hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) (starIrr j) x := by
    rw [IsPrimeCyclicTIHyp.primeTIirr_principal_left,
      IsPrimeCyclicTIHyp.primeTIirr_principal_left, hd, hd', one_smul, one_smul,
      ← IsCyclicTIPair.prodCharEta_eq_coe_apply, ← IsCyclicTIPair.prodCharEta_eq_coe_apply, ← hst]
    rfl
  rw [bridgeChar_apply, bridgeChar_apply, map_sub, conj_bridgePermChar_apply, hmu]

end IsPrimeTIBridgeConfig

end Local

section Transport

variable {G : Type*} [Group G]

theorem irrMapSubtype_starIrr (L : Subgroup G) (W : Subgroup ↥L) [Finite ↥W]
    [Finite ↥(W.map L.subtype)] (i : Irr ↥W) :
    irrMapSubtype L W (starIrr i) = starIrr (irrMapSubtype L W i) :=
  Subtype.ext (by rw [coe_irrMapSubtype, coe_starIrr, coe_starIrr, coe_irrMapSubtype]; rfl)

end Transport

namespace IsPrimeTIBridgeConfig

variable {G : Type*} [Group G] [Fintype G] {L : Subgroup G} [Fintype ↥L]
  {K W₁ W₂ H U : Subgroup ↥L} [H.Normal] {A : Set ↥L} [Fintype ↥(W₁ ⊔ W₂)]
  [Fintype ↥((W₁ ⊔ W₂).map L.subtype)]
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L} {A₀ : Set G} {T : G → Subgroup G}
  {ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G}

structure IsDadeBridgeData (hc : IsPrimeTIBridgeConfig K W₁ W₂ H U A)
    (σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun ↥L) (A₀ : Set G) (T : G → Subgroup G)
    (ω : classFun ↥((W₁ ⊔ W₂).map L.subtype) →ₗ[ℂ] classFun G) : Prop where
  isometry : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ
  primeTIres_one : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ →
    hc.primeCyclicTI.primeTIres σ j 1 = (Nat.card ↥U : ℂ)
  primeTIres_eq_zero : ∀ j : Irr ↥W₂, j ≠ principalIrr ↥W₂ → ∀ k : ↥K, (k : ↥L) ∉ H →
    hc.primeCyclicTI.primeTIres σ j k = 0
  image_subset : (fun x : ↥L => (x : G)) '' bridgeSupport A W₁ W₂ ⊆ A₀
  isDadeData : IsDadeData L A₀ T
  setOf_conj_eq : {g : G | (fun x => g⁻¹ * x * g) ''
      cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
    = cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)}
    = (((W₁ ⊔ W₂).map L.subtype : Subgroup G) : Set G)
  inter_eq_empty : ∀ g ∉ (W₁ ⊔ W₂).map L.subtype,
    (fun x => g⁻¹ * x * g) ''
        cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype)
      ∩ cyclicTIDiff ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype) (W₂.map L.subtype) = ∅
  omega_isometry : IsCyclicTIIsometry ((W₁ ⊔ W₂).map L.subtype) (W₁.map L.subtype)
    (W₂.map L.subtype) ω

namespace IsDadeBridgeData

variable {hc : IsPrimeTIBridgeConfig K W₁ W₂ H U A}

theorem bridgeChar_mem_dadeDomain (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) :
    hc.bridgeChar (σ := σ) (j := j) ∈ dadeDomain L A₀ :=
  mem_dadeDomain_of_mem_span_Irr
    (virtualChars_le_span_Irr (hc.bridgeChar_mem_virtualChars hB.isometry))
    fun x hx => hc.bridgeChar_eq_zero_of_notMem_bridgeSupport hB.isometry
      (hB.primeTIres_one j hj) (hB.primeTIres_eq_zero j hj)
      fun hmem => hx (hB.image_subset ⟨x, hmem, rfl⟩)

noncomputable def tauBridge (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : G → ℂ :=
  ((dadeMap hB.isDadeData
      ⟨hc.bridgeChar (σ := σ) (j := j), hB.bridgeChar_mem_dadeDomain hj⟩ : classFun G) : G → ℂ)

noncomputable def ambientEta (hB : IsDadeBridgeData hc σ A₀ T ω) (j : Irr ↥W₂) : G → ℂ :=
  (hc.primeCyclicTI.isCyclicTIPair_map_subtype hB.setOf_conj_eq hB.inter_eq_empty).prodCharEta ω
    (principalIrr ↥(W₁.map L.subtype)) (irrMapSubtype L W₂ j)

noncomputable def bridgeRemainder (hB : IsDadeBridgeData hc σ A₀ T ω) {j₀ : Irr ↥W₂}
    (hj₀ : j₀ ≠ principalIrr ↥W₂) : G → ℂ :=
  hB.tauBridge hj₀ - 1 + hB.ambientEta j₀

theorem primeTISign_eq_one (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : hc.primeCyclicTI.primeTISign σ j = 1 :=
  hc.primeTISign_eq_one hB.isometry (hB.primeTIres_one j hj)

theorem tauBridge_mem_virtualChars (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : hB.tauBridge hj ∈ virtualChars G := by
  rw [virtualChars_eq_span_Irr]
  exact hB.isDadeData.dadeMap_mem_span_Irr _
    (virtualChars_le_span_Irr (hc.bridgeChar_mem_virtualChars hB.isometry))

theorem ambientEta_mem_virtualChars (hB : IsDadeBridgeData hc σ A₀ T ω) (j : Irr ↥W₂) :
    hB.ambientEta j ∈ virtualChars G :=
  IsCyclicTIPair.prodCharEta_mem_virtualChars _ hB.omega_isometry _ _

theorem cfInner_tauBridge_one (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : cfInner (hB.tauBridge hj) (1 : G → ℂ) = 1 := by
  rw [tauBridge, NormalInducedFamily.cfInner_dadeMap_one]
  exact hc.cfInner_bridgeChar_one hB.isometry hj

theorem cfInner_ambientEta_one (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) : cfInner (hB.ambientEta j) (1 : G → ℂ) = 0 := by
  set hW := hc.primeCyclicTI.isCyclicTIPair_map_subtype hB.setOf_conj_eq hB.inter_eq_empty
  have h1 := hW.cfInner_prodCharEta_col hB.omega_isometry (irrMapSubtype L W₂ j)
    (principalIrr ↥(W₂.map L.subtype))
  rw [hW.prodCharEta_principal hB.omega_isometry] at h1
  rw [ambientEta, h1, if_neg]
  intro hcc
  exact hj (irrMapSubtype_injective L W₂ (hcc.trans (irrMapSubtype_principal L W₂).symm))

theorem cfInner_self_tauBridge (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) :
    cfInner (hB.tauBridge hj) (hB.tauBridge hj)
      = ((Nat.card ↥U : ℂ) - 1) / (Nat.card ↥W₁ : ℂ) + 2 := by
  rw [tauBridge, cfInner_self_dadeMap]
  exact hc.cfInner_bridgeChar_self hB.isometry hj

theorem conj_tauBridge (hB : IsDadeBridgeData hc σ A₀ T ω) {j : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) (x : G) :
    conj (hB.tauBridge hj x) = hB.tauBridge (starIrr_ne_principalIrr hj) x := by
  have hEq : (⟨hc.bridgeChar (σ := σ) (j := starIrr j),
        hB.bridgeChar_mem_dadeDomain (starIrr_ne_principalIrr hj)⟩ : dadeDomain L A₀)
      = ⟨fun y => conj (hc.bridgeChar (σ := σ) (j := j) y),
        star_mem_dadeDomain (hB.bridgeChar_mem_dadeDomain hj)⟩ :=
    Subtype.ext (funext fun y => (hc.conj_bridgeChar_apply hB.isometry (hB.primeTISign_eq_one hj)
      (hB.primeTISign_eq_one (starIrr_ne_principalIrr hj)) y).symm)
  rw [tauBridge, tauBridge, hEq, dadeMap_conj_apply]

theorem conj_ambientEta (hB : IsDadeBridgeData hc σ A₀ T ω) (j : Irr ↥W₂) (x : G) :
    conj (hB.ambientEta j x) = hB.ambientEta (starIrr j) x := by
  have hst := (hc.primeCyclicTI.isCyclicTIPair_map_subtype hB.setOf_conj_eq
      hB.inter_eq_empty).star_prodCharEta hB.omega_isometry
    (i := principalIrr ↥(W₁.map L.subtype)) (k := principalIrr ↥(W₁.map L.subtype))
    (j := irrMapSubtype L W₂ j) (l := irrMapSubtype L W₂ (starIrr j))
    (by simp) (by rw [irrMapSubtype_starIrr, coe_starIrr])
  rw [ambientEta, ambientEta, ← hst]
  rfl

theorem tauBridge_sub_tauBridge (hB : IsDadeBridgeData hc σ A₀ T ω) {j k : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂) :
    hB.tauBridge hj - hB.tauBridge hk = hB.ambientEta k - hB.ambientEta j := by
  have hone : hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) k 1
      = hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j 1 := by
    rw [← hc.primeCyclicTI.primeTIres_one (σ := σ) k,
      ← hc.primeCyclicTI.primeTIres_one (σ := σ) j, hB.primeTIres_one k hk,
      hB.primeTIres_one j hj]
  have hmem := hc.primeCyclicTI.primeTIirr_sub_mem_dadeDomain (A₀ := A₀) hB.isometry
    hc.right_le_H hc.centralizer_sdiff_subset hB.image_subset (principalIrr ↥W₁) hk hj hone
  have hkey : (⟨hc.bridgeChar (σ := σ) (j := j), hB.bridgeChar_mem_dadeDomain hj⟩ :
        dadeDomain L A₀)
      - ⟨hc.bridgeChar (σ := σ) (j := k), hB.bridgeChar_mem_dadeDomain hk⟩
      = ⟨hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) k
          - hc.primeCyclicTI.primeTIirr σ (principalIrr ↥W₁) j, hmem⟩ := by
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sub, Pi.sub_apply, IsPrimeTIBridgeConfig.bridgeChar_apply]
    ring
  have hsub : hB.tauBridge hj - hB.tauBridge hk
      = ((dadeMap hB.isDadeData
          (⟨hc.bridgeChar (σ := σ) (j := j), hB.bridgeChar_mem_dadeDomain hj⟩
            - ⟨hc.bridgeChar (σ := σ) (j := k), hB.bridgeChar_mem_dadeDomain hk⟩) :
            classFun G) : G → ℂ) := by
    rw [map_sub]; rfl
  rw [hsub, hkey]
  have h1 := hc.primeCyclicTI.dadeMap_primeTIirr_sub_eq (A₀ := A₀) (T := T) (ω := ω)
    hB.isometry hc.right_le_H hc.centralizer_sdiff_subset hB.image_subset hB.isDadeData
    hB.setOf_conj_eq hB.inter_eq_empty hB.omega_isometry (principalIrr ↥W₁) hk hj hone
  rw [h1, hB.primeTISign_eq_one hk]
  simp [ambientEta]

theorem bridgeRemainder_eq (hB : IsDadeBridgeData hc σ A₀ T ω) {j k : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) (hk : k ≠ principalIrr ↥W₂) :
    hB.bridgeRemainder hj = hB.bridgeRemainder hk := by
  have h := hB.tauBridge_sub_tauBridge hj hk
  have h2 : hB.tauBridge hj + hB.ambientEta j = hB.tauBridge hk + hB.ambientEta k := by
    rw [← sub_eq_zero] at h ⊢
    rw [← h]; ring
  rw [bridgeRemainder, bridgeRemainder, sub_add_eq_add_sub, sub_add_eq_add_sub, h2]

theorem bridgeRemainder_mem_virtualChars (hB : IsDadeBridgeData hc σ A₀ T ω) {j₀ : Irr ↥W₂}
    (hj₀ : j₀ ≠ principalIrr ↥W₂) : hB.bridgeRemainder hj₀ ∈ virtualChars G := by
  rw [bridgeRemainder]
  exact add_mem (sub_mem (hB.tauBridge_mem_virtualChars hj₀)
    (Irr_subset_virtualChars one_mem_Irr)) (hB.ambientEta_mem_virtualChars j₀)

theorem conj_bridgeRemainder_apply (hB : IsDadeBridgeData hc σ A₀ T ω) {j₀ : Irr ↥W₂}
    (hj₀ : j₀ ≠ principalIrr ↥W₂) (x : G) :
    conj (hB.bridgeRemainder hj₀ x) = hB.bridgeRemainder hj₀ x := by
  have hstar : hB.bridgeRemainder (starIrr_ne_principalIrr hj₀) = hB.bridgeRemainder hj₀ :=
    hB.bridgeRemainder_eq _ _
  have hconj : conj (hB.bridgeRemainder hj₀ x)
      = hB.bridgeRemainder (starIrr_ne_principalIrr hj₀) x := by
    simp only [bridgeRemainder, Pi.add_apply, Pi.sub_apply, Pi.one_apply, map_add, map_sub,
      map_one, hB.conj_tauBridge hj₀ x, hB.conj_ambientEta j₀ x]
  rw [hconj, hstar]

theorem cfInner_bridgeRemainder_one (hB : IsDadeBridgeData hc σ A₀ T ω) {j₀ : Irr ↥W₂}
    (hj₀ : j₀ ≠ principalIrr ↥W₂) : cfInner (hB.bridgeRemainder hj₀) (1 : G → ℂ) = 0 := by
  rw [bridgeRemainder, cfInner_add_left, cfInner_sub_left, hB.cfInner_tauBridge_one hj₀,
    hB.cfInner_ambientEta_one hj₀, cfInner_one_one]
  ring

theorem tauBridge_eq (hB : IsDadeBridgeData hc σ A₀ T ω) {j j₀ : Irr ↥W₂}
    (hj : j ≠ principalIrr ↥W₂) (hj₀ : j₀ ≠ principalIrr ↥W₂) :
    hB.tauBridge hj = 1 - hB.ambientEta j + hB.bridgeRemainder hj₀ := by
  rw [hB.bridgeRemainder_eq hj₀ hj, bridgeRemainder]
  ring

end IsDadeBridgeData

end IsPrimeTIBridgeConfig

end CFSG.FeitThompson

end
