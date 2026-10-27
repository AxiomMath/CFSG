module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataNorm
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusFiveDescent
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus
  coordinateQuadMinus)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG modelToGEquiv symm_mem_modelToG)
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (incl)

theorem OmegaNeighbourAlternative.field_of_lieModel {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ}
    (hdet : OmegaEvenTypeDetAt m) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) (hDm : LieModel (D ⧸ center D) tag m 2 f)
    {Kc : Subgroup Y} (hKc : IsComponent Kc) (h : OmegaNeighbourAlternative s D Kc m f)
    (hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc)
    (hmodel : LieModel Kc .POmegaPlus m 2 (2 * f)) :
    OmegaNeighbourAlternativeField s D Kc m f tag ∧ center D = ⊥ := by
  obtain ⟨hDKK, ⟨-, hDK, hsK, hsN, hout, hZodd, -⟩ | ⟨hKt', -⟩⟩ := h
  · have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hZodd
    have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
    have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
      (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    obtain ⟨hD'c, hD'm, hD'map, -⟩ :=
      UnitaryPilot.isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK.le hDs hDcomp hDm
    have hτ2 := orderOf_normalizerMonoidHom_of_not_mem_range hs2 hout
    obtain ⟨hD'Z, hD'L, hall⟩ :=
      forall_isPComponent_eq_of_not_inner hdet hmodel hτ2 hout htag hD'c hD'm
    have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
      rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
      intro x hx
      exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
    refine ⟨⟨hDKK, .inl ⟨hKt, hDK, hsK, hsN, hout, hZ, hmodel, fun P hP => ?_⟩⟩, ?_⟩
    · rw [hall P hP]
      exact ⟨hD'map, hD'L⟩
    · rw [← map_center_eq (F4Pilot.subgroupOfSubgroupOfEquiv hDK.le hDfix), hD'Z,
        Subgroup.map_bot]
  · exact absurd hKt hKt'

section NormPlusTen


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_normalized_plusAnisoTorus_of_lieModel (hset : SeitzSetting G L) {m : ℕ}
    (hm : 3 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G}
    (hX : X = modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoTorus m hirr))
    (htX : t ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hK : OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)
      (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
          (plusAnisoPerp (K := K) m b c)).subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc (m + 1) 1)
    (hKt' : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom = Kc)
    (hlie : LieModel Kc .POmegaPlus (m + 1) 2 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) {k₀ : Subfield F} [CharP k₀ 2] (hσk : ∀ x, x ∈ k₀ ↔ σ x = x)
    (φ : K ≃+* k₀) :
    ∃ hDE : modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c) ≤
        centralizerPerfectCore X,
      ∃ π : centralizerPerfectCore X ≃*
          matrixProjectiveDerived (coordinateQuadMinus (m + 1) F (by omega)
            ((φ b : k₀) : F) ((φ c : k₀) : F)),
        ∀ d, π (Subgroup.inclusion hDE d) =
          incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
            (plusAnisoPerpFieldEquiv (by omega) hirr (e.trans (plusAnisoProjEquiv m hirr).symm)
              φ d) := by
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  set D := modelToG e' (plusAnisoPerp (K := K) m b c) with hDdef
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, -, -, -, -, -, -, hZ⟩ :=
    neighbour_data_plusAnisoTorus (X := X) (D := D) hm hirr e' htC hX rfl
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_plusAnisoTorus (X := X) (D := D)
    hset.standardSetting.standard htC ht hKt hm hirr e' hX rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_plusAnisoTorus (X := X) (D := D)
    hset.standardSetting.standard htC ht hKt hm hirr e' hX htX rfl
  obtain ⟨hLie, -⟩ := lieModel_map_plusAnisoPerp (D := D) hKc hm hirr e' rfl
  set s := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ with hs
  set Db := (D.subgroupOf (centralizer (X : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) with hDb
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 :=
    (Subgroup.orderOf_coe (⟨t, htX⟩ : centralizer (X : Set G))).symm.trans ht
  have hs2' : orderOf s = 2 := orderOf_mk_oddCore ht'
  have hD1 : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  have hDX : D ≤ centralizer (X : Set G) :=
    (hD ▸ map_subtype_le _ : D ≤ L ⊓ _).trans inf_le_right
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hLie) hD1
  obtain ⟨hfield, -⟩ := OmegaNeighbourAlternative.field_of_lieModel
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2' hcomp (omegaEvenTypeDetAt (m + 1))
    (Or.inr rfl) hDm' hKcomp hK hKt' hlie
  have hNC := neighbourCore_of_field htC ht hLt htX hD hDq hZ hXo hsyl hKcomp hfield hKt'
  have hDK : Db ≤ Kc := by
    obtain ⟨-, ⟨-, hDK, -, -⟩ | ⟨hKt'', -⟩⟩ := hfield
    · exact hDK.le
    · exact absurd hKt' hKt''
  obtain ⟨hsN, -, -, hmodel, -, q, hqs, hqker, hkodd, -, -, hDE, hqinj, hqrange⟩ := hNC
  have hDs := hcomp.1
  have hDc := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
    ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hcomp)
  have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK
  have hD'c := F4Pilot.isComponent_subgroupOf_subgroupOf
    (F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN) hDcomp
  have hDfix : Db.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩) := by
    rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
    intro x hx
    exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
  have hD'map : ((Db.subgroupOf Kc).subgroupOf
      (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩))).map
        (fixedSubgroup (Kc.normalizerMonoidHom ⟨_, hsN⟩)).subtype = Db.subgroupOf Kc := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hDfix]
  have hεr := hqrange.trans hD'map.symm
  have hD'm := LieType.CurtisTits.lieModel_of_mulEquiv
    ((MonoidHom.ofInjective hqinj).trans ((MulEquiv.subgroupCongr hεr).trans
      ((((Db.subgroupOf Kc).subgroupOf
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
  have hirr₀ : ∀ s' : k₀, s' ^ 2 + φ b * s' + φ c ≠ 0 := by
    intro s' hs'
    apply hirr (φ.symm s')
    apply φ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, map_zero]
    exact hs'
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hmodel F
    (by rw [hF]; norm_num)
  obtain ⟨ψ, hψ, -⟩ := exists_mulEquiv_comp_eq_incl_minus_of_four_le hσ hσk (by omega : 4 ≤ m + 1)
    (φ b) (φ c) hirr₀ (ψS.trans (statedOmegaPlusEquiv F (m + 1) (by omega))) hτ hD'c hD'm _
    hqinj hεr (plusAnisoPerpFieldEquiv (by omega) hirr e' φ)
  have hinj : Function.Injective q := by
    have : Group.IsPerfect (centralizerPerfectCore X) :=
      isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
    exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hmodel (centralizerPerfectCore X) this
      q hqs hqker.le hkodd
  exact ⟨hDE, (MulEquiv.ofBijective q ⟨hinj, hqs⟩).trans ψ, fun d => hψ d⟩

end NormPlusTen

@[expose] def OmegaMinusTwoTenNormalizedInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))).Normal →
        ∀ (htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))
          (Kc : Subgroup (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) :
              Set G) ⧸ oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)))),
          IsComponent Kc →
          OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
            (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
                (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) Kc 4 1 →
          Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
              (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)))
                ⟨t, htX⟩)).toMonoidHom = Kc →
          LieModel Kc .POmegaPlus 4 2 2 →
          ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → ∀ σ : F ≃+* F,
            orderOf σ = 2 → ∀ (k₀ : Subfield F) [CharP k₀ 2], (∀ x, x ∈ k₀ ↔ σ x = x) →
            ∀ φ : K ≃+* k₀,
            ∃ hDE : modelToG e (anisoPerp (K := K) (by norm_num) b c) ≤
                centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by norm_num) b c)),
              ∃ π : centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by norm_num) b c)) ≃*
                  matrixProjectiveDerived (coordinateQuadPlus (5 - 1) F),
                ∀ d, π (Subgroup.inclusion hDE d) =
                  incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (5 - 1) k₀)
                    (anisoPerpFieldEquivN (by norm_num) hirr e φ d)

end CFSG.SeitzReduction.OmegaPilot
