module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveNormalize
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveFlip
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverExists
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus plusIndexEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusSwap
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Adapters.RankTwoModelTransports (glCongr glCongr_coe)

section Quotient

variable {E Kc : Type*} [Group E] [Group Kc]

@[expose] noncomputable def autOfQuotient (q : E →* Kc) (hqs : Function.Surjective q)
    (hker : q.ker = center E) (c : MulAut E) : MulAut Kc :=
  (QuotientGroup.quotientKerEquivOfSurjective q hqs).symm.trans
    ((QuotientGroup.congr q.ker q.ker c (by
      rw [hker]
      exact Subgroup.characteristic_iff_map_eq.1 inferInstance c)).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hqs))

theorem autOfQuotient_apply (q : E →* Kc) (hqs : Function.Surjective q)
    (hker : q.ker = center E) (c : MulAut E) (y : E) :
    autOfQuotient q hqs hker c (q y) = q (c y) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective q hqs).symm (q y) =
      QuotientGroup.mk' q.ker y := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [autOfQuotient, MulEquiv.trans_apply]
  rw [h1, QuotientGroup.congr_mk']
  rfl

end Quotient

section Congr

variable {K k₀ : Type} [Field K] [Field k₀]

theorem glCongr_plusSwapMatrix (φ : K ≃+* k₀) (m : ℕ) (hm : 0 < m) :
    glCongr φ (plusSwapMatrix m K hm) = plusSwapMatrix m k₀ hm := by
  apply Units.ext
  rw [glCongr_coe, coe_plusSwapMatrix, coe_plusSwapMatrix]
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem statedOmegaPlusCongr_plusSwapDerived (φ : K ≃+* k₀) (m : ℕ) (hm : 0 < m)
    (A : StatedOmega (StatedQuadPlus m K)) :
    statedOmegaPlusCongr φ m (plusSwapDerived m K hm A) =
      plusSwapDerived m k₀ hm (statedOmegaPlusCongr φ m A) := by
  apply Subtype.ext
  rw [coe_statedOmegaPlusCongr, plusSwapDerived_val, plusSwapDerived_val, map_mul, map_mul,
    map_inv, glCongr_plusSwapMatrix, coe_statedOmegaPlusCongr]

theorem fieldChange_plusFlipAut [CharP K 2] [CharP k₀ 2] (φ : K ≃+* k₀) (m : ℕ) (hm : 1 ≤ m)
    (u : matrixProjectiveDerived (coordinateQuadPlus m K)) :
    statedOmegaPlusEquiv k₀ m hm (statedOmegaPlusCongr φ m
        ((statedOmegaPlusEquiv K m hm).symm (plusFlipAut m K (by omega) u))) =
      plusFlipAut m k₀ (by omega) (statedOmegaPlusEquiv k₀ m hm (statedOmegaPlusCongr φ m
        ((statedOmegaPlusEquiv K m hm).symm u))) := by
  obtain ⟨A, rfl⟩ := (statedOmegaPlusEquiv K m hm).surjective u
  rw [plusFlipAut_statedOmegaPlusEquiv, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply,
    statedOmegaPlusCongr_plusSwapDerived, plusFlipAut_statedOmegaPlusEquiv]

end Congr

section PerpFlip

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_flip_pairPerp {m : ℕ} (hm : 3 ≤ m) (k : Fin (m + 1)) {k₀ : Type} [Field k₀]
    [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀) :
    ∃ w : matrixProjectiveDerived (coordinateQuadPlus (m + 1) K),
      w ∈ normalizer (pairTorus (K := K) k :
        Set (matrixProjectiveDerived (coordinateQuadPlus (m + 1) K))) ∧
      w ∈ normalizer (pairPerp (K := K) k :
        Set (matrixProjectiveDerived (coordinateQuadPlus (m + 1) K))) ∧
      ∀ x x' : pairPerp (K := K) k,
        (x' : matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) = w * x * w⁻¹ →
        ((pairPerpModelEquiv (by omega) k).trans ((statedOmegaPlusEquiv K m (by omega)).symm.trans
          ((statedOmegaPlusCongr φ m).trans (statedOmegaPlusEquiv k₀ m (by omega))))) x' =
        plusFlipAut m k₀ (by omega)
          (((pairPerpModelEquiv (by omega) k).trans ((statedOmegaPlusEquiv K m (by omega)).symm.trans
            ((statedOmegaPlusCongr φ m).trans (statedOmegaPlusEquiv k₀ m (by omega))))) x) := by
  set ℓ : Fin (m + 1 - 1) := ⟨m + 1 - 1 - 1, by omega⟩ with hℓ
  have hk' := Ne.symm (avoid_ne (M := m + 1 - 1) (by omega) k ℓ)
  have hd := pairDisjoint_plus (n := m + 1) hk'
  have hw := doubleFlip_mem_orthDerived (K := K) (isHypCoord_coordinateQuadPlus k)
    (isHypCoord_coordinateQuadPlus _) hd
  set W : orthDerived (coordinateQuadPlus (m + 1) K) := ⟨_, hw⟩ with hW
  refine ⟨projHom _ W, projHom_doubleFlip_mem_normalizer_pairTorusOf
    (isHypCoord_coordinateQuadPlus k) hd hw, projHom_doubleFlip_mem_normalizer_pairPerpOf hd hw,
    fun x x' hxx' => ?_⟩
  obtain ⟨y, hy, hyx⟩ := x.2
  have hy' : W * y * W⁻¹ ∈ (stabSub (K := K) (plusIndexEquiv (m + 1) (.inl k))
      (plusIndexEquiv (m + 1) (.inr k))).subgroupOf (orthDerived (coordinateQuadPlus (m + 1) K)) := by
    rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact doubleFlip_conj_mem_stabSub hd (mem_subgroupOf.1 hy)
  have hx : x = ⟨projHom _ y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hyx.symm
  have hx' : x' = ⟨projHom _ (W * y * W⁻¹), ⟨_, hy', rfl⟩⟩ := by
    apply Subtype.ext
    change (x' : matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) = projHom _ (W * y * W⁻¹)
    rw [hxx', map_mul, map_mul, map_inv, hyx]
  subst hx hx'
  have hL2 := pairPerpEquiv_conj_doubleFlip (n := m + 1) (by omega) k ℓ W y rfl
    (mem_subgroupOf.1 hy) (mem_subgroupOf.1 hy')
  have hz : swapLin (K := K) (plusIndexEquiv (m + 1 - 1) (.inl ⟨m + 1 - 1 - 1, by omega⟩))
      (plusIndexEquiv (m + 1 - 1) (.inr ⟨m + 1 - 1 - 1, by omega⟩)) *
      ((pairPerpEquiv (by omega) k ⟨projHom _ y, ⟨y, hy, rfl⟩⟩ :
        orthDerived (coordinateQuadPlus (m + 1 - 1) K)) :
          (Fin (2 * (m + 1 - 1)) → K) ≃ₗ[K] (Fin (2 * (m + 1 - 1)) → K)) *
      swapLin (plusIndexEquiv (m + 1 - 1) (.inl ⟨m + 1 - 1 - 1, by omega⟩))
        (plusIndexEquiv (m + 1 - 1) (.inr ⟨m + 1 - 1 - 1, by omega⟩)) ∈
      orthDerived (coordinateQuadPlus (m + 1 - 1) K) := by
    rw [← hL2]
    exact Subtype.property _
  have hPE : pairPerpEquiv (K := K) (by omega) k ⟨projHom _ (W * y * W⁻¹), ⟨_, hy', rfl⟩⟩ =
      ⟨_, hz⟩ := Subtype.ext hL2
  have hflip := plusFlipAut_projHom (F := K) (m := m + 1 - 1) (by omega)
    (pairPerpEquiv (by omega) k ⟨projHom _ y, ⟨y, hy, rfl⟩⟩) hz
  have hJ1 : pairPerpModelEquiv (K := K) (by omega : 4 ≤ m + 1) k
      ⟨projHom _ (W * y * W⁻¹), ⟨_, hy', rfl⟩⟩ =
      plusFlipAut (m + 1 - 1) K (by omega)
        (pairPerpModelEquiv (K := K) (by omega : 4 ≤ m + 1) k ⟨projHom _ y, ⟨y, hy, rfl⟩⟩) := by
    change projHom _ (pairPerpEquiv _ k _) = plusFlipAut (m + 1 - 1) K _
      (projHom _ (pairPerpEquiv _ k _))
    rw [hPE, hflip]
  simp only [MulEquiv.trans_apply]
  rw [hJ1]
  exact fieldChange_plusFlipAut φ m (by omega) _

end PerpFlip

section Cover

open CFSG

variable {G : Type} [Group G] {L : Subgroup G}

theorem nonempty_plusFieldCover_of_neighbourCoreField_four {f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (k : Fin (4 + 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) K)) {t : G}
    (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hNC : NeighbourCoreField t X D htX Kc 4 f .POmegaPlus)
    (hcomp : CFSG.Open.IsComponentOf ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
      (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (PlusFieldCover e ι k) := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hLie : LieModel D .POmegaPlus 4 2 f := by
    rw [hDe]
    exact LieType.CurtisTits.lieModel_of_mulEquiv (modelToGEquiv e (pairPerp (K := K) k))
      (lieModel_pairPerp hKc (by omega : 5 ≤ 4 + 1) k)
  obtain ⟨hsN, hout, -, hmodel, -, q, hqs, hqker, -, -, -, hDE, hqinj, hqrange⟩ := hNC
  have hDs := hcomp.1
  have hDc := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
    ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK
  have hD'c := F4Pilot.isComponent_subgroupOf_subgroupOf
    (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
  have hDfix : ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc ≤
      fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) := by
    rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  have hD'map : ((((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc).subgroupOf
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))).map
          (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)).subtype =
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hDfix]
  have hεr := hqrange.trans hD'map.symm
  have hD'm := LieType.CurtisTits.lieModel_of_mulEquiv
    ((MonoidHom.ofInjective hqinj).trans ((MulEquiv.subgroupCongr hεr).trans
      ((((((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf Kc).subgroupOf
          (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)))).equivMapOfInjective _
            (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)).subtype_injective).symm)) hLie
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hτ : Kc.normalizerMonoidHom ⟨_, hsN⟩ * Kc.normalizerMonoidHom ⟨_, hsN⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨_, hsN⟩ : normalizer (Kc : Set (centralizer (X : Set G) ⧸
        oddCore (centralizer (X : Set G))))) * ⟨_, hsN⟩ = 1 := by
      apply Subtype.ext
      change QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
          (⟨t, htX⟩ : centralizer (X : Set G)) *
        QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
          (⟨t, htX⟩ : centralizer (X : Set G)) = 1
      rw [← map_mul]
      have h2 : (⟨t, htX⟩ : centralizer (X : Set G)) * ⟨t, htX⟩ = 1 := Subtype.ext htt
      rw [h2, map_one]
    rw [h1, map_one]
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hmodel F hF
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  rw [← UnitaryPilot.modelToG_def e] at hX hDe
  subst hX hDe
  obtain ⟨w, hwX, hwD, hwJ⟩ := exists_flip_pairPerp (K := K) (by omega : 3 ≤ 4) k
    ι.rangeRestrictFieldEquiv
  obtain ⟨s, hs⟩ : ∃ s : G, s = ((e.symm w : L) : G) := ⟨_, rfl⟩
  have hsX : s ∈ normalizer (modelToG e (pairTorus (K := K) k) : Set G) :=
    hs ▸ UnitaryPilot.symm_mem_normalizer_modelToG e hwX
  have hsD : s ∈ normalizer (modelToG e (pairPerp (K := K) k) : Set G) :=
    hs ▸ UnitaryPilot.symm_mem_normalizer_modelToG e hwD
  have hsE : s ∈ normalizer (centralizerPerfectCore (modelToG e (pairTorus (K := K) k)) :
      Set G) := F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _ hsX
  obtain ⟨θ, hθ⟩ : ∃ θ : MulAut Kc, θ = autOfQuotient q hqs hqker
      ((centralizerPerfectCore (modelToG e (pairTorus (K := K) k))).normalizerMonoidHom
        ⟨s, hsE⟩) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : MulAut (modelToG e (pairPerp (K := K) k)),
      a = (modelToG e (pairPerp (K := K) k)).normalizerMonoidHom ⟨s, hsD⟩ := ⟨_, rfl⟩
  have hθa : ∀ x, θ ((q.comp (Subgroup.inclusion hDE)) x) =
      (q.comp (Subgroup.inclusion hDE)) (a x) := by
    intro x
    rw [hθ]
    refine (autOfQuotient_apply q hqs hqker _ (Subgroup.inclusion hDE x)).trans ?_
    change q _ = q _
    congr 1
    apply Subtype.ext
    rw [ha]
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
  obtain ⟨j, hj⟩ : ∃ j : modelToG e (pairPerp (K := K) k) ≃*
      matrixProjectiveDerived (coordinateQuadPlus 4 ι.fieldRange),
      j = (modelToGEquiv e (pairPerp (K := K) k)).symm.trans
        ((pairPerpModelEquiv (by omega) k).trans ((statedOmegaPlusEquiv K 4 (by omega)).symm.trans
          ((statedOmegaPlusCongr ι.rangeRestrictFieldEquiv 4).trans
            (statedOmegaPlusEquiv ι.fieldRange 4 (by omega))))) := ⟨_, rfl⟩
  have hjx : ∀ x : pairPerp (K := K) k, j (modelToGEquiv e (pairPerp (K := K) k) x) =
      ((pairPerpModelEquiv (by omega) k).trans ((statedOmegaPlusEquiv K 4 (by omega)).symm.trans
          ((statedOmegaPlusCongr ι.rangeRestrictFieldEquiv 4).trans
            (statedOmegaPlusEquiv ι.fieldRange 4 (by omega))))) x := by
    intro x
    rw [hj, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hγ : MulAut.congr j a = plusFlipAut 4 ι.fieldRange (by omega) := by
    ext y
    obtain ⟨d, rfl⟩ := j.surjective y
    obtain ⟨x, rfl⟩ := (modelToGEquiv e (pairPerp (K := K) k)).surjective d
    change j (a (j.symm (j _))) = _
    rw [MulEquiv.symm_apply_apply]
    have hx' : w * x * w⁻¹ ∈ pairPerp (K := K) k := (mem_normalizer_iff.1 hwD x).1 x.2
    have h2 : a (modelToGEquiv e (pairPerp (K := K) k) x) =
        modelToGEquiv e (pairPerp (K := K) k) ⟨_, hx'⟩ := by
      apply Subtype.ext
      rw [ha, Subgroup.normalizerMonoidHom_apply_apply_coe, UnitaryPilot.coe_modelToGEquiv_apply,
        UnitaryPilot.coe_modelToGEquiv_apply]
      simp only [hs, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, hjx, hjx]
    exact hwJ x ⟨_, hx'⟩ rfl
  have hγF := plusFlipAut_smul_pointFamily 4 ι.fieldRange (by omega)
  have hγX := plusFlipAut_smul_plusCX 4 ι.fieldRange (by omega)
  have hγX' := plusFlipAut_smul_plusCXstar 4 ι.fieldRange (by omega)
  rw [← hγ] at hγF hγX hγX'
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comp_eq_incl_four hσ hσk
    (ψS.trans (statedOmegaPlusEquiv F 4 (by omega))) hτ hout hD'c hD'm _ hqinj hεr j θ a hθa
    hγF hγX hγX'
  refine ⟨PlusFieldCover.ofNormalized
    ((statedOmegaPlusEquiv F 4 (by omega)).symm.toMonoidHom.comp (ψ.toMonoidHom.comp q))
    ((statedOmegaPlusEquiv F 4 (by omega)).symm.surjective.comp (ψ.surjective.comp hqs))
    (fun x hx => ?_) hDE (fun t' ht' hmem => ?_)⟩
  · have hx' : ψ (q x) = 1 := by
      have h1 := MonoidHom.mem_ker.1 hx
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
      exact (MulEquiv.map_eq_one_iff _).1 h1
    have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 hx')
    rw [hqker] at h2
    exact h2
  · have hgD := symm_mem_modelToG e (frameHom_mem_pairPerp (K := K) ht')
    have hw' : liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')) =
        liftParam ι (restrictParam k t') := by
      funext l
      apply Units.ext
      simp [liftParam]
    have hjF : j ⟨_, hgD⟩ = (isHypFrame_plus ι.fieldRange 4).frameHom
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')) := by
      rw [hj]
      exact pairPerpFieldEquiv_frameHom e (by omega) k _ ht' hgD
    change (((statedOmegaPlusEquiv F 4 (by omega)).symm
      (ψ ((q.comp (Subgroup.inclusion hDE)) ⟨_, hgD⟩)) :
        StatedOmega (StatedQuadPlus 4 F)) : GL (Fin 4 ⊕ Fin 4) F) = _
    rw [hψ, hjF, incl_frameHom, statedOmegaPlusEquiv_symm_frameHom, hw', neighbourDiag_apply]

variable [Finite G]

theorem nonempty_plusFieldCover_of_field_five (hset : SeitzSetting G L) {f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (k : Fin (4 + 1)) (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (4 + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hfield : OmegaNeighbourAlternativeField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc 4 f .POmegaPlus)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (PlusFieldCover e ι k) := by
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_pairTorus_of_seitzSetting hset hKc hq
    (by omega : 5 ≤ 4 + 1) k e htC ht hX htX hDe
  have hNC := neighbourCoreField_pairTorus hset hKc hq (by omega : 5 ≤ 4 + 1) k e htC ht hX htX
    hDe hKcomp hfield hKt
  obtain ⟨-, ⟨-, hDK, -, -⟩ | ⟨hKt', -⟩⟩ := hfield
  · exact nonempty_plusFieldCover_of_neighbourCoreField_four hKc k e ht hX htX hDe hNC hcomp
      hDK.le ι hσ hfix
  · exact absurd hKt hKt'

end Cover

end CFSG.SeitzReduction.OmegaPilot
