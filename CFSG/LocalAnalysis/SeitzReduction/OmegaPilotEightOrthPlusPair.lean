module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusStepA

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.EvenSmallLie
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  regular_coordinateQuadPlus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.LinearPilot (SLmCatalogueClausesAt upperUnit lowerUnit diagUnit
  weylUnit coe_diagUnit)
open scoped MatrixGroups

theorem conj_mem_centralizer_of_normalizer_plus {G : Type*} [Group G] {U : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (U : Set G)) (hc : c ∈ centralizer (U : Set G)) :
    n * c * n⁻¹ ∈ centralizer (U : Set G) := by
  rw [mem_centralizer_iff]
  intro u hu
  have hv : n⁻¹ * u * n ∈ U := by
    have := (mem_normalizer_iff.mp (inv_mem hn) u).mp hu
    rwa [inv_inv] at this
  have hvc := mem_centralizer_iff.mp hc _ hv
  calc u * (n * c * n⁻¹) = n * ((n⁻¹ * u * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * u * n)) * n⁻¹ := by rw [hvc]
    _ = n * c * n⁻¹ * u := by group

theorem diagUnit_apply_ne {F : Type*} [Field F] (α : Fˣ) :
    ∀ i j : Fin 2, i ≠ j → ((diagUnit α : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) i j = 0 := by
  intro i j hij
  rw [coe_diagUnit]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rfl
  · rfl
  · exact absurd rfl hij

section Torus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {F : Type} [Field F] [Finite F] {ι : K →+* F} {m : ℕ}
variable {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)}

omit [Finite G] [Finite F] in
theorem frameHom_mem_normalizer_frameCore (s : Fin (m + 1) → Kˣ)
    (P' : Subgroup (Fin (m + 1) → Kˣ)) :
    ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) ∈
      normalizer (F4Pilot.centralizerPerfectCore (modelToG e (plusFrameTorus K P')) : Set G) :=
  UnitaryPilot.symm_mem_normalizer_centralizerPerfectCore_modelToG e
    (centralizer_le_normalizer _ ((isHypFrame_plus K (m + 1)).frameTorusOf_le_centralizer ⊤ P'
      ((isHypFrame_plus K (m + 1)).frameHom_mem_frameTorusOf (Subgroup.mem_top s))))

omit [Finite G] [Finite F] in
theorem frameHom_mem_normalizer_plusNeighbourCore (s : Fin (m + 1) → Kˣ) (k : Fin (m + 1)) :
    ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) ∈
      normalizer (plusNeighbourCore e k : Set G) := by
  have h := frameHom_mem_normalizer_frameCore (G := G) (e := e) s (rootParam k)
  rwa [plusFrameTorus_rootParam] at h

omit [Finite G] [Finite F] in
theorem plusFieldCover_conj_nodeParam_diag {k : Fin (m + 1)} (C : PlusFieldCover e ι k)
    {J P : Finset (Fin (m + 1))} (hk : k ∉ J) (hJ : J.card = 2)
    (φ : SL(2, F) ≃* plusSignedLevelCore e J P)
    (hφC : ∀ A, ((C.π (Subgroup.inclusion (plusSignedLevelCore_le_plusNeighbourCore e hk P)
        (φ A)) : StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) =
      nodeParam F (preimagePlanes k J) (preimagePlanes k P) ((card_preimagePlanes hk).trans hJ) A)
    {A : SL(2, F)} (hA : ∀ i j : Fin 2, i ≠ j → (A : Matrix (Fin 2) (Fin 2) F) i j = 0)
    (s : Fin (m + 1) → Kˣ) :
    C.π ((plusNeighbourCore e k).normalizerMonoidHom
        ⟨_, frameHom_mem_normalizer_plusNeighbourCore s k⟩
        (Subgroup.inclusion (plusSignedLevelCore_le_plusNeighbourCore e hk P) (φ A))) =
      C.π (Subgroup.inclusion (plusSignedLevelCore_le_plusNeighbourCore e hk P) (φ A)) := by
  have hdiag : ∀ a b : Fin m ⊕ Fin m, a ≠ b →
      ((nodeParam F (preimagePlanes k J) (preimagePlanes k P) ((card_preimagePlanes hk).trans hJ)
        A : GL (Fin m ⊕ Fin m) F) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) a b = 0 :=
    fun a b hab => nodeParam_apply_ne_of_diag _ _ _ hA hab
  rw [C.equivariant s]
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hφC A]
  change neighbourDiag ι k s * _ * (neighbourDiag ι k s)⁻¹ = _
  rw [neighbourDiag_apply, ← commute_diagOmega_of_apply_ne hdiag, mul_inv_cancel_right]

omit [Finite G] [Finite F] in
theorem frameHom_commute_nodeParam_diag {k : Fin (m + 1)} (C : PlusFieldCover e ι k)
    {J P : Finset (Fin (m + 1))} (hk : k ∉ J) (hJ : J.card = 2)
    (φ : SL(2, F) ≃* plusSignedLevelCore e J P)
    (hφC : ∀ A, ((C.π (Subgroup.inclusion (plusSignedLevelCore_le_plusNeighbourCore e hk P)
        (φ A)) : StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) =
      nodeParam F (preimagePlanes k J) (preimagePlanes k P) ((card_preimagePlanes hk).trans hJ) A)
    {A : SL(2, F)} (hA : ∀ i j : Fin 2, i ≠ j → (A : Matrix (Fin 2) (Fin 2) F) i j = 0)
    (s : Fin (m + 1) → Kˣ) :
    ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) * (φ A : G) =
      (φ A : G) * ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) := by
  have hUE := plusSignedLevelCore_le_plusNeighbourCore e hk P
  have hnU := frameHom_mem_normalizer_frameCore (G := G) (e := e) s (signedLevelParam J P)
  have hmem : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) * (φ A : G) *
      ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G)⁻¹ ∈
        plusSignedLevelCore e J P :=
    (mem_normalizer_iff.mp hnU _).mp (φ A).2
  have hconj : Subgroup.inclusion hUE ⟨_, hmem⟩ =
      (plusNeighbourCore e k).normalizerMonoidHom
        ⟨_, frameHom_mem_normalizer_plusNeighbourCore s k⟩ (Subgroup.inclusion hUE (φ A)) := by
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
      Subgroup.coe_inclusion]
  have key := plusFieldCover_conj_nodeParam_diag C hk hJ φ hφC hA s
  rw [← hconj] at key
  have hφB : φ (φ.symm ⟨_, hmem⟩) = ⟨_, hmem⟩ := MulEquiv.apply_symm_apply _ _
  have hBA : φ.symm ⟨_, hmem⟩ = A := by
    apply nodeParam_injective (preimagePlanes k J) (preimagePlanes k P)
      ((card_preimagePlanes hk).trans hJ)
    rw [← hφC, ← hφC, hφB, key]
  have h1 := congrArg Subtype.val hφB
  rw [hBA] at h1
  have h1' : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) * (φ A : G) *
      ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G)⁻¹ = (φ A : G) := h1.symm
  calc ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) * (φ A : G) =
        ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) * (φ A : G) *
          ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G)⁻¹ *
          ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) := by group
    _ = (φ A : G) * ((e.symm ((isHypFrame_plus K (m + 1)).frameHom s) : L) : G) := by
        rw [h1']

omit [Finite G] in
theorem le_centralizer_of_nodeParam_pair [CharP F 2] {k : Fin (m + 1)} (C : PlusFieldCover e ι k)
    {J P : Finset (Fin (m + 1))} (hk : k ∉ J) (hJ : J.card = 2)
    (φ : SL(2, F) ≃* plusSignedLevelCore e J P)
    (hφC : ∀ A, ((C.π (Subgroup.inclusion (plusSignedLevelCore_le_plusNeighbourCore e hk P)
        (φ A)) : StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) =
      nodeParam F (preimagePlanes k J) (preimagePlanes k P) ((card_preimagePlanes hk).trans hJ) A)
    (I : Finset (Fin (m + 1)))
    (hK : ∀ A' : SL(2, K), (φ (SpecialLinearGroup.map ι A') : G) ∈
      centralizer (plusLevelCore e I : Set G)) :
    plusSignedLevelCore e J P ≤ centralizer (plusLevelCore e I : Set G) := by
  have hnorm : ∀ α : Fˣ, (φ (diagUnit α) : G) ∈ normalizer (plusLevelCore e I : Set G) := by
    intro α
    refine F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    have hx' : x ∈ frameTorusOf (coordinateQuadPlus (m + 1) K) (plusFrameLeft (m + 1))
        (plusFrameRight (m + 1)) (levelParam I) := hx
    rw [(isHypFrame_plus K (m + 1)).frameTorusOf_eq_map] at hx'
    obtain ⟨s, -, rfl⟩ := hx'
    exact frameHom_commute_nodeParam_diag C hk hJ φ hφC (diagUnit_apply_ne α) s
  set H : Subgroup SL(2, F) := (centralizer (plusLevelCore e I : Set G)).comap
    ((plusSignedLevelCore e J P).subtype.comp φ.toMonoidHom) with hH
  have hmemH : ∀ A, A ∈ H ↔ (φ A : G) ∈ centralizer (plusLevelCore e I : Set G) :=
    fun A => Iff.rfl
  have hKH : ∀ A' : SL(2, K), SpecialLinearGroup.map ι A' ∈ H := fun A' => (hmemH _).2 (hK A')
  have hu1 : LinearPilot.upperUnit (1 : F) ∈ H := by
    have h := hKH (LinearPilot.upperUnit 1)
    rwa [LinearPilot.map_upperUnit, map_one] at h
  have hu : ∀ c : F, LinearPilot.upperUnit c ∈ H := by
    intro c
    by_cases hc : c = 0
    · rw [hc, LinearPilot.upperUnit_zero]
      exact one_mem H
    obtain ⟨α, hα⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) c
    have hα0 : α ≠ 0 := by
      rintro rfl
      exact hc (by rw [hα, mul_zero])
    have hconj := LinearPilot.diagUnit_mul_upperUnit_mul_inv (Units.mk0 α hα0) (1 : F)
    rw [Units.val_mk0, mul_one, ← hα] at hconj
    rw [← hconj, hmemH, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact conj_mem_centralizer_of_normalizer_plus (hnorm _) ((hmemH _).1 hu1)
  have hw : LinearPilot.weylUnit ∈ H := by
    have h := hKH LinearPilot.weylUnit
    rwa [LinearPilot.map_weylUnit] at h
  have hl : ∀ c : F, LinearPilot.lowerUnit c ∈ H := by
    intro c
    have h := LinearPilot.weylUnit_mul_upperUnit_mul_inv (-c)
    rw [neg_neg] at h
    rw [← h]
    exact mul_mem (mul_mem hw (hu _)) (inv_mem hw)
  have htop : H = ⊤ := LinearPilot.eq_top_of_upperUnit_mem_of_lowerUnit_mem hu hl
  intro x hx
  have h := (hmemH (φ.symm ⟨x, hx⟩)).1 (by rw [htop]; exact Subgroup.mem_top _)
  rwa [MulEquiv.apply_symm_apply] at h

end Torus

section StepB

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem le_centralizer_plusLevelCore_of_leviFixBar (hq : 4 ≤ Nat.card K)
    {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)} {t : G}
    (htC : t ∈ centralizer (L : Set G)) {F : Type} [Field F] [Finite F] [CharP F 2]
    {ι : K →+* F} {σ : F ≃+* F} (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι)
    (hF16 : 16 ≤ Nat.card F) (C : PlusFieldCover (m := 3) e ι 0)
    (hC3 : ∀ x : plusNeighbourCore e 0, C.π ((plusNeighbourCore e 0).normalizerMonoidHom ⟨t,
        UnitaryPilot.mem_normalizer_centralizerPerfectCore_modelToG_of_mem_centralizer e htC _⟩ x) =
      statedOmegaPlusCongr σ 3 (C.π x))
    {J P : Finset (Fin 4)} (hk : (0 : Fin 4) ∉ J) (hJ : J.card = 2)
    {P₁ P₂ : HypPair (coordinateQuadPlus 4 K)} (h₁₂ : P₁.Orth P₂)
    (hYU : modelToG e (leviFixBar P₁ P₂) ≤ plusSignedLevelCore e J P)
    (hY0 : modelToG e (leviFixBar P₁ P₂) ≤
      centralizer (plusLevelCore e ({0, 1} : Finset (Fin 4)) : Set G)) :
    plusSignedLevelCore e J P ≤ centralizer (plusLevelCore e ({0, 1} : Finset (Fin 4)) : Set G) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hQ' := (isHypCoord_coordinateQuadPlus (K := K) (n := 4) 0).exists_ne_zero
  obtain ⟨φ, hφC, hφt⟩ := exists_nodeParam_of_cover C htC hC3 hq (by omega) (by omega) P hk hJ
  have hYt : modelToG e (leviFixBar P₁ P₂) ≤ centralizer ({t} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htC y (UnitaryPilot.modelToG_le e _ hy))
  have hcard : Nat.card SL(2, K) ≤ Nat.card (modelToG e (leviFixBar P₁ P₂)) := by
    rw [UnitaryPilot.card_modelToG e, card_leviFixBar h₁₂ hQ hT hQ']
  have hrange := eq_range_of_card_le φ ι hfix hφt hYU hYt hcard
  refine le_centralizer_of_nodeParam_pair C hk hJ φ hφC _ fun A' => hY0 ?_
  rw [hrange]
  exact ⟨A', rfl⟩

theorem plusNode_zero_le_centralizer_plusNode_two_three (hset : SeitzSetting G L)
    (hcat : SLmCatalogueClausesAt 4) (hdet : LinearPilot.SLmEvenTypeDetAt 4) {f : ℕ}
    (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K)) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hR5 : ∃ x : G, ∃ z ∈ L ⊓ CFSG.conjugate L x, x⁻¹ * t * x = t * z ∧
      (∃ hz : z ∈ L, IsLongRoot (coordinateQuadPlus 4 K) (e ⟨z, hz⟩)) ∧
      (∃ hz : z ∈ CFSG.conjugate L x,
        IsLongRoot (coordinateQuadPlus 4 K) (((conjugateMulEquiv L x).symm.trans e) ⟨z, hz⟩)))
    (hnn : ∀ k : Fin 4, ¬ (((modelToG e (pairPerp (K := K) k)).subgroupOf
          (centralizer (modelToG e (pairTorus (K := K) k) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (modelToG e (pairTorus (K := K) k) :
            Set G))))).Normal)
    (hrow : ∀ k : Fin 4, OmegaRowAt t (modelToG e (pairTorus (K := K) k))
      (modelToG e (pairPerp (K := K) k)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    plusNode e 0 ≤ centralizer (plusNode e 2 : Set G) ∧
      plusNode e 0 ≤ centralizer (plusNode e 3 : Set G) := by
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσσ : σ * σ = 1 := by rw [← _root_.sq, ← hσ, pow_orderOf_eq_one]
  have hFK : Nat.card F = Nat.card K ^ 2 := by
    obtain ⟨ω, hω⟩ := LinearPilot.exists_trace_one_of_involution hσ1 hσσ
    exact LinearPilot.natCard_eq_sq_of_trace_one ι hσσ hfix hω
  have hF16 : 16 ≤ Nat.card F := by rw [hFK]; nlinarith
  have hA := plusNode_zero_le_centralizer_stabTwoBar hset hcat hdet hKc hq e ht hKt hR5 (hnn 2)
    (hrow 2) ι hσ hfix
  have hR : modelToG e (stabTwoBar K 0 1) ≤ centralizer (plusNode e 0 : Set G) :=
    le_centralizer_iff.mp hA
  have hU₀ : plusNode e 0 = plusLevelCore e ({0, 1} : Finset (Fin 4)) := by
    rw [plusNode, plusNodeSet_four_zero, plusNodeFlip_four_zero,
      plusSignedLevelCore_of_disjoint e (Finset.disjoint_empty_right _)]
  rw [hU₀] at hR
  obtain ⟨C, hC3⟩ := exists_plusFieldCover_conj_four hset hcat hdet hKc hq 0 e htC ht (hnn 0)
    (hrow 0) ι hσ hfix
  have h02 : (plusPair K 0).Orth (plusPair K 2) := plusPair_orth (by decide)
  have h12 : (plusPair K 1).Orth (plusPair K 2) := plusPair_orth (by decide)
  have h2 : plusNode e 2 ≤ centralizer (plusLevelCore e ({0, 1} : Finset (Fin 4)) : Set G) :=
    le_centralizer_plusLevelCore_of_leviFixBar hq htC hfix hF16 C hC3 (by decide) (by decide)
      (plusPair_orth (show (2 : Fin 4) ≠ 3 by decide))
      (modelToG_leviFixBar_le_plusNode_two hq e)
      ((UnitaryPilot.modelToG_mono e (leviFixBar_le_stabTwoBar_of_orth h02
        (plusPair_orth (by decide)) h12 (plusPair_orth (by decide)))).trans hR)
  have h3 : plusNode e 3 ≤ centralizer (plusLevelCore e ({0, 1} : Finset (Fin 4)) : Set G) :=
    le_centralizer_plusLevelCore_of_leviFixBar hq htC hfix hF16 C hC3 (by decide) (by decide)
      (plusPair_orth_flip (show (2 : Fin 4) ≠ 3 by decide))
      (modelToG_leviFixBar_le_plusNode_three hq e)
      ((UnitaryPilot.modelToG_mono e (leviFixBar_le_stabTwoBar_of_orth h02
        (plusPair_orth_flip (by decide)) h12 (plusPair_orth_flip (by decide)))).trans hR)
  rw [hU₀]
  exact ⟨le_centralizer_iff.mp h2, le_centralizer_iff.mp h3⟩

end StepB


end CFSG.SeitzReduction.OmegaPilot
