module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveDescent
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Global
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverExists
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Bridge

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.SeitzReduction.SymplecticPilot (liftParam)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)

section Cover

open CFSG

variable {G : Type} [Group G] {L : Subgroup G}

theorem nonempty_minusFieldCover_of_neighbourCoreField_of_three_le {r f : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hr : 3 ≤ r) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (r + 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (n := r + 2) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (n := r + 2) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hNC : NeighbourCoreField t X D htX Kc (r + 1) f .POmegaMinus)
    (hcomp : CFSG.Open.IsComponentOf ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
      (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (MinusFieldCover e ι k) := by
  have hF : Nat.card F = 2 ^ (2 * f) :=
    SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι hKc hσ hfix
  have hFK : Nat.card F = Nat.card K ^ 2 := by rw [hF, hKc, ← pow_mul, mul_comm]
  have hLie : LieModel D .POmegaMinus (r + 1) 2 f := by
    rw [hDe]
    exact LieType.CurtisTits.lieModel_of_mulEquiv
      (modelToGEquiv e (minusPairPerp (K := K) (n := r + 2) _ b c k))
      (lieModel_minusPairPerp hKc (by omega : 5 ≤ r + 2) hirr k)
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
  have hirr₀ : ∀ s : ι.fieldRange, s ^ 2 + ι.rangeRestrictFieldEquiv b * s +
      ι.rangeRestrictFieldEquiv c ≠ 0 := by
    intro s hs
    apply hirr (ι.rangeRestrictFieldEquiv.symm s)
    apply ι.rangeRestrictFieldEquiv.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs
  subst hX hDe
  obtain ⟨ψ, hψ, -⟩ := exists_mulEquiv_comp_eq_incl_minus_of_four_le hσ hσk (by omega : 4 ≤ r + 1)
    (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c) hirr₀
    (ψS.trans (statedOmegaPlusEquiv F (r + 1) (by omega))) hτ hD'c hD'm _ hqinj hεr
    (minusPairPerpFieldEquiv (by omega) hirr e k ι.rangeRestrictFieldEquiv)
  have hφb : ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) = ι b :=
    RingHom.rangeRestrictFieldEquiv_apply_coe ι b
  have hφc : ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) = ι c :=
    RingHom.rangeRestrictFieldEquiv_apply_coe ι c
  obtain ⟨α, hα⟩ := exists_root_of_card_eq_sq ι hFK hirr
  have hαF : α ^ 2 + ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) * α +
      ((ι.rangeRestrictFieldEquiv c : ι.fieldRange) : F) = 0 := by
    rw [hφb, hφc]
    exact hα
  have hβ0 : ((ι.rangeRestrictFieldEquiv b : ι.fieldRange) : F) ≠ 0 := by
    rw [hφb]
    exact (map_ne_zero ι).2 (coeff_ne_zero_of_irreducible hirr)
  have hαα := root_ne_other_of_ne_zero (α := α) hβ0
  let π0 := (minusPlusBridge (r := r) (by omega) hαF hαα).toMonoidHom.comp (ψ.toMonoidHom.comp q)
  have hs0 : Function.Surjective π0 :=
    (minusPlusBridge (r := r) (by omega) hαF hαα).surjective.comp (ψ.surjective.comp hqs)
  have hk0 : π0.ker ≤ center (minusNeighbourCore e k) := by
    intro x hx
    have hx' : ψ (q x) = 1 := by
      have h1 := MonoidHom.mem_ker.1 hx
      simp only [π0, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
      exact (MulEquiv.map_eq_one_iff _).1 h1
    have h2 : x ∈ q.ker := MonoidHom.mem_ker.2 ((MulEquiv.map_eq_one_iff ψ).1 hx')
    rw [hqker] at h2
    exact h2
  have hD0 : modelToG e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k) ≤
      minusNeighbourCore e k := hDE
  have hn0 : ∀ t' : Fin (r + 1) → Kˣ, t' k = 1 →
      ∀ hmem : ((e.symm ((isHypFrame_minus K (n := r + 2) (by omega) b c).frameHom t') : L) :
        G) ∈ minusNeighbourCore e k,
        ((π0 ⟨_, hmem⟩ : StatedOmega (StatedQuadPlus (r + 1) F)) :
          GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = minusNeighbourDiag ι k t' := by
    intro t' ht' hmem
    have hgD := symm_mem_modelToG e (frameHom_mem_minusPairPerp (n := r + 2) ht')
    have hjf := minusPairPerpFieldEquiv_frameHom (by omega) hirr e k ι.rangeRestrictFieldEquiv ht'
      hgD
    have hinc := incl_frameHom_minus ι.fieldRange (n := r + 1) (by omega)
      (ι.rangeRestrictFieldEquiv b) (ι.rangeRestrictFieldEquiv c)
      (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t'))
    have hbr := minusPlusBridge_frameHom (r := r) (by omega) hαF hαα
      (liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')))
    have hw : liftParam ι.fieldRange.subtype
        (liftParam ι.rangeRestrictFieldEquiv.toRingHom (restrictParam k t')) =
        liftParam ι (restrictParam k t') := by
      funext l
      apply Units.ext
      simp [liftParam]
    change (((minusPlusBridge (r := r) (by omega) hαF hαα)
      (ψ ((q.comp (Subgroup.inclusion hDE)) ⟨_, hgD⟩)) :
        StatedOmega (StatedQuadPlus (r + 1) F)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) = _
    rw [hψ, hjf, hinc, hbr, hw, minusNeighbourDiag_apply]
  exact ⟨MinusFieldCover.ofNormalized (e := e) (ι := ι) (k := k) π0 hs0 hk0 hD0 hn0⟩

variable [Finite G]

theorem nonempty_minusFieldCover_of_field_of_three_le (hset : SeitzSetting G L) {r f : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (hr : 3 ≤ r) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (k : Fin (r + 1))
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (n := r + 2) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (n := r + 2) (by omega) b c k).map
      e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hfield : OmegaNeighbourAlternativeField
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc (r + 1) f .POmegaMinus)
    (hKt : Kc.map (MulAut.conj
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    Nonempty (MinusFieldCover e ι k) := by
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq
    (by omega : 5 ≤ r + 2) hirr k e htC ht hX htX hDe
  have hNC := neighbourCoreField_minusPairTorus hset hKc hq (by omega : 5 ≤ r + 2) hirr k e htC ht
    hX htX hDe hKcomp hfield hKt
  obtain ⟨-, ⟨-, hDK, -, -⟩ | ⟨hKt', -⟩⟩ := hfield
  · exact nonempty_minusFieldCover_of_neighbourCoreField_of_three_le hKc hr hirr k e ht hX htX hDe
      hNC hcomp hDK.le ι hσ hfix
  · exact absurd hKt hKt'

theorem forall_nonempty_minusFieldCover_of_fieldRow_of_three_le (hset : SeitzSetting G L)
    {r f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hr : 3 ≤ r) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (h8 : ∀ k : Fin (r + 1), OmegaHR8FieldAt t (r + 1) f .POmegaMinus
      (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k))
      (modelToG e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k)))
    (hrow : ∀ k : Fin (r + 1), OmegaRowAt t
      (modelToG e (minusPairTorus (K := K) (n := r + 2) (by omega) b c k))
      (modelToG e (minusPairPerp (K := K) (n := r + 2) (by omega) b c k)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (ι : K →+* F) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) (hfix : ∀ x : F, σ x = x ↔ x ∈ Set.range ι) :
    ∀ k, Nonempty (MinusFieldCover e ι k) := by
  intro k
  obtain ⟨-, htX, -⟩ := neighbour_data_minusPairTorus hKc hq (by omega : 5 ≤ r + 2) hirr k e htC
    rfl rfl
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq
    (by omega : 5 ≤ r + 2) hirr k e htC ht rfl htX rfl
  obtain ⟨htX', Kc, hKcomp, hfield, hKt⟩ := exists_fieldAlt_of_rowAt_tag (h8 k) (hrow k) hcomp.2.2
  exact nonempty_minusFieldCover_of_field_of_three_le hset hKc hq hr hirr k e htC ht rfl htX' rfl
    hKcomp hfield hKt ι hσ hfix

end Cover

end CFSG.SeitzReduction.OmegaPilot
