module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverBridge
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverNormalize
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotNeighbourCore
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaCovers
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParamField
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)

theorem nonempty_mulEquiv_statedOmegaPlus_of_lieModel {S : Type} [Group S] {m g : ℕ}
    (hm : 1 ≤ m) (hS : LieModel S .POmegaPlus m 2 g) (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ g) : Nonempty (S ≃* StatedOmega (StatedQuadPlus m F)) := by
  obtain ⟨-, K', _, _, hK', ⟨e'⟩⟩ := F4Pilot.statedClassicalModel_of_lieModel_pomega (Or.inl rfl) hS
  have : CharP K' 2 := LinearPilot.charP_two_of_card_eq_two_pow hK'
  let σ' : F ≃+* K' := CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard (hF.trans hK'.symm)
  have hbot : (StatedScalars (Fin m ⊕ Fin m) K').subgroupOf (StatedOmega (StatedQuadPlus m K')) =
      ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (CFSG.LieType.Universal.Spin.coe_quadPlus m K')
      (CFSG.LieType.Universal.Spin.exists_map_ne_zero_of_hypPair _
        (CFSG.ClassicalGroups.Orthogonal.plusPair K' (⟨0, by omega⟩ : Fin m)))
  exact ⟨e'.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
    (QuotientGroup.quotientBot.trans (statedOmegaPlusCongr σ' m).symm))⟩

section Perp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {m : ℕ}

@[expose] noncomputable def pairPerpFieldEquiv
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) (hm : 3 ≤ m)
    (k : Fin (m + 1)) {k₀ : Type} [Field k₀] [CharP k₀ 2] (φ : K ≃+* k₀) :
    (((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype : Subgroup G) ≃*
      matrixProjectiveDerived (coordinateQuadPlus m k₀) :=
  (modelToGEquiv e (pairPerp (K := K) k)).symm.trans ((pairPerpModelEquiv (by omega) k).trans
    ((statedOmegaPlusEquiv K m (by omega)).symm.trans
      ((statedOmegaPlusCongr φ m).trans (statedOmegaPlusEquiv k₀ m (by omega)))))

theorem pairPerpFieldEquiv_frameHom
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) (hm : 3 ≤ m)
    (k : Fin (m + 1)) {k₀ : Type} [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀)
    {t : Fin (m + 1) → Kˣ} (ht : t k = 1)
    (hmem : ((e.symm ((isHypFrame_plus K (m + 1)).frameHom t) : L) : G) ∈
      ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype) :
    pairPerpFieldEquiv e hm k φ ⟨_, hmem⟩ =
      (isHypFrame_plus k₀ m).frameHom (liftParam φ.toRingHom (restrictParam k t)) := by
  have h1 : (modelToGEquiv e (pairPerp (K := K) k)).symm ⟨_, hmem⟩ =
      ⟨(isHypFrame_plus K (m + 1)).frameHom t, frameHom_mem_pairPerp ht⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  have h2 := pairPerpModelEquiv_frameHom (by omega : 4 ≤ m + 1) k ht
  have h3 : (statedOmegaPlusEquiv K m (by omega)).symm
      ((isHypFrame_plus K m).frameHom (restrictParam k t)) =
      ⟨diagOmega K m (restrictParam k t), diagOmega_mem_statedOmega_of_one_le (by omega) _⟩ :=
    Subtype.ext (statedOmegaPlusEquiv_symm_frameHom (by omega) _)
  have h4 : statedOmegaPlusCongr φ m
      ⟨diagOmega K m (restrictParam k t), diagOmega_mem_statedOmega_of_one_le (by omega) _⟩ =
      ⟨diagOmega k₀ m (liftParam φ.toRingHom (restrictParam k t)),
        diagOmega_mem_statedOmega_of_one_le (by omega) _⟩ :=
    Subtype.ext ((coe_statedOmegaPlusCongr φ _).trans (glCongr_diagOmega φ _))
  have h5 := statedOmegaPlusEquiv_diag (F := k₀) (by omega : 1 ≤ m)
    (liftParam φ.toRingHom (restrictParam k t)) (diagOmega_mem_statedOmega_of_one_le (by omega) _)
  have h2' : pairPerpModelEquiv (by omega : 4 ≤ m + 1) k
      ⟨(isHypFrame_plus K (m + 1)).frameHom t, frameHom_mem_pairPerp ht⟩ =
      (isHypFrame_plus K m).frameHom (restrictParam k t) := h2
  calc pairPerpFieldEquiv e hm k φ ⟨_, hmem⟩
      = statedOmegaPlusEquiv k₀ m (by omega) (statedOmegaPlusCongr φ m
          ((statedOmegaPlusEquiv K m (by omega)).symm (pairPerpModelEquiv (by omega) k
            ((modelToGEquiv e (pairPerp (K := K) k)).symm ⟨_, hmem⟩)))) := rfl
    _ = _ := by rw [h1, h2', h3, h4, h5]

end Perp

section Cover

open CFSG

variable {G : Type} [Group G] {L : Subgroup G}

theorem nonempty_plusFieldCover_of_neighbourCoreField {m f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hm : 5 ≤ m) (k : Fin (m + 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) {t : G}
    (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hNC : NeighbourCoreField t X D htX Kc m f .POmegaPlus)
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
  have hLie : LieModel D .POmegaPlus m 2 f := by
    rw [hDe]
    exact LieType.CurtisTits.lieModel_of_mulEquiv (modelToGEquiv e (pairPerp (K := K) k))
      (lieModel_pairPerp hKc (by omega : 5 ≤ m + 1) k)
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
  subst hX hDe
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comp_eq_incl hσ hσk hm
    (ψS.trans (statedOmegaPlusEquiv F m (by omega))) hτ hout hD'c hD'm _ hqinj hεr
    (pairPerpFieldEquiv e (by omega) k ι.rangeRestrictFieldEquiv)
  refine ⟨PlusFieldCover.ofNormalized
    ((statedOmegaPlusEquiv F m (by omega)).symm.toMonoidHom.comp (ψ.toMonoidHom.comp q))
    ((statedOmegaPlusEquiv F m (by omega)).symm.surjective.comp (ψ.surjective.comp hqs))
    (fun x hx => ?_) hDE (fun t' ht' hmem => ?_)⟩
  · have hx' : ψ (q x) = 1 := by
      have h1 := MonoidHom.mem_ker.1 hx
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
      exact (MulEquiv.map_eq_one_iff _).1 h1
    have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 hx')
    rw [hqker] at h2
    exact h2
  · have hgD := symm_mem_modelToG e (frameHom_mem_pairPerp (K := K) ht')
    have hw : liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')) =
        liftParam ι (restrictParam k t') := by
      funext l
      apply Units.ext
      simp [liftParam]
    change (((statedOmegaPlusEquiv F m (by omega)).symm
      (ψ ((q.comp (Subgroup.inclusion hDE)) ⟨_, hgD⟩)) :
        StatedOmega (StatedQuadPlus m F)) : GL (Fin m ⊕ Fin m) F) = _
    rw [hψ, pairPerpFieldEquiv_frameHom e (by omega) k _ ht' hgD, incl_frameHom,
      statedOmegaPlusEquiv_symm_frameHom, hw, neighbourDiag_apply]

variable [Finite G]

theorem nonempty_plusFieldCover_of_field (hset : SeitzSetting G L) {m f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hm : 5 ≤ m) (k : Fin (m + 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hfield : OmegaNeighbourAlternativeField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f .POmegaPlus)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (PlusFieldCover e ι k) := by
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_pairTorus_of_seitzSetting hset hKc hq
    (by omega : 5 ≤ m + 1) k e htC ht hX htX hDe
  have hNC := neighbourCoreField_pairTorus hset hKc hq (by omega : 5 ≤ m + 1) k e htC ht hX htX
    hDe hKcomp hfield hKt
  obtain ⟨-, ⟨-, hDK, -, -⟩ | ⟨hKt', -⟩⟩ := hfield
  · exact nonempty_plusFieldCover_of_neighbourCoreField hKc hm k e ht hX htX hDe hNC hcomp
      hDK.le ι hσ hfix
  · exact absurd hKt hKt'

end Cover

end CFSG.SeitzReduction.OmegaPilot
