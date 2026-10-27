module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2FieldDataWeyl
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightInputsAnisoCover
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

section Perp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {n : ℕ} {b c : K}

@[expose] noncomputable def anisoPerpFieldEquivN (hn : 4 ≤ n)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) :
    modelToG e (anisoPerp (K := K) (by omega : 1 ≤ n) b c) ≃*
      matrixProjectiveDerived (coordinateQuadPlus (n - 1) k₀) :=
  (modelToGEquiv e (anisoPerp (K := K) (by omega : 1 ≤ n) b c)).symm.trans
    ((anisoPerpModelEquiv hn hirr).trans (plusCongr φ (n - 1)))

end Perp

section Norm

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_normalized_anisoTorus_two (hset : SeitzSetting G L) {n : ℕ} (hn : 6 ≤ n)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hN : ∀ htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))) ⟨t, htX⟩)
        (((modelToG e (anisoPerp (K := K) (by omega) b c)).subgroupOf
            (centralizer (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG e (anisoTorus (K := K) (by omega) b c) : Set G))))) (n - 1) 1)
    (hrow : OmegaRowAt t (modelToG e (anisoTorus (K := K) (by omega) b c))
      (modelToG e (anisoPerp (K := K) (by omega) b c)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) {k₀ : Subfield F} [CharP k₀ 2] (hσk : ∀ x, x ∈ k₀ ↔ σ x = x)
    (φ : K ≃+* k₀) :
    ∃ hDE : modelToG e (anisoPerp (K := K) (by omega) b c) ≤
        centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)),
      ∃ π : centralizerPerfectCore (modelToG e (anisoTorus (K := K) (by omega) b c)) ≃*
          matrixProjectiveDerived (coordinateQuadPlus (n - 1) F),
        ∀ d, π (Subgroup.inclusion hDE d) =
          incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (n - 1) k₀)
            (anisoPerpFieldEquivN (by omega) hirr e φ d) := by
  set X := modelToG e (anisoTorus (K := K) (by omega) b c) with hXdef
  set D := modelToG e (anisoPerp (K := K) (by omega) b c) with hDdef
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, htX, -, -, -, -, -, hZ⟩ :=
    neighbour_data_anisoTorus (X := X) (D := D) (by omega) hirr e htC rfl rfl
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_anisoTorus (X := X) (D := D)
    hset.standardSetting.standard htC ht hKt (by omega) hirr e rfl rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting (X := X) (D := D)
    hset hKc (by omega) hirr e htC ht rfl htX rfl
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp (D := D) hKc (by omega) hirr e rfl
  set s := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ with hs
  set Db := (D.subgroupOf (centralizer (X : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) with hDb
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 :=
    (Subgroup.orderOf_coe (⟨t, htX⟩ : centralizer (X : Set G))).symm.trans ht
  have hs2' : orderOf s = 2 := orderOf_mk_oddCore ht'
  have hs2 : s ^ 2 = 1 := hs2' ▸ pow_orderOf_eq_one s
  have hDperf : ⁅Db, Db⁆ = Db := SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2
  have hD1 : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨Kc, hKcomp, hK⟩ := hN htX
  obtain ⟨rw', hr, hrK⟩ := neighbourRowOmega_of_alternative hKcomp hK
  obtain ⟨htX', hrow'⟩ := hrow
  have hr1 : rw' = .field := NeighbourRowOmega.unique hs2 hDperf hD1 hr hrow'
  have hKt' : Kc.map (MulAut.conj s).toMonoidHom = Kc := hrK.1 hr1
  have hDX : D ≤ centralizer (X : Set G) :=
    (hD ▸ map_subtype_le _ : D ≤ L ⊓ _).trans inf_le_right
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hLie) hD1
  obtain ⟨hfield, -⟩ := hK.field (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2' hcomp
    (ne_four_one_of_six_le hn) (omegaEvenTypeDetAt (n - 1)) (Or.inl rfl) hDm' hKcomp
  have hNC := neighbourCore_of_field htC ht hLt htX hD hDq hZ hXo hsyl hKcomp hfield hKt'
  have hDK : Db ≤ Kc := by
    obtain ⟨-, ⟨-, hDK, -, -⟩ | ⟨hKt'', -⟩⟩ := hfield
    · exact hDK.le
    · exact absurd hKt' hKt''
  obtain ⟨hsN, hout, -, hmodel, -, q, hqs, hqker, hkodd, -, -, hDE, hqinj, hqrange⟩ := hNC
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
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hmodel F
    (by rw [hF]; norm_num)
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comp_eq_incl hσ hσk (by omega : 5 ≤ n - 1)
    (ψS.trans (statedOmegaPlusEquiv F (n - 1) (by omega))) hτ hout hD'c hD'm _ hqinj hεr
    (anisoPerpFieldEquivN (by omega) hirr e φ)
  have hinj : Function.Injective q := by
    have : Group.IsPerfect (centralizerPerfectCore X) :=
      isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
    exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hmodel (centralizerPerfectCore X) this
      q hqs hqker.le hkodd
  exact ⟨hDE, (MulEquiv.ofBijective q ⟨hinj, hqs⟩).trans ψ, fun d => hψ d⟩

end Norm

section PlusPerp

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]
  {m : ℕ} {b c : K}

@[expose] noncomputable def plusAnisoPerpFieldEquiv (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (plusAnisoQuad K m b c)) {k₀ : Type} [Field k₀]
    (φ : K ≃+* k₀) :
    modelToG e (plusAnisoPerp (K := K) m b c) ≃*
      matrixProjectiveDerived (coordinateQuadMinus (m + 1) k₀ (by omega) (φ b) (φ c)) :=
  (modelToGEquiv e (plusAnisoPerp (K := K) m b c)).symm.trans
    ((plusAnisoPerpEquiv hm hirr).trans ((MulEquiv.ofBijective (projHom _)
      ⟨projHom_injective (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ m + 1) b c
        (⟨0, by omega⟩ : Fin (m + 1 - 1))).exists_ne_zero, projHom_surjective _⟩).trans
      (minusCongr φ (by omega) b c)))

end PlusPerp

section NormPlus

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_normalized_plusAnisoTorus_two (hset : SeitzSetting G L) {m : ℕ} (hm : 4 ≤ m)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 2) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hN : ∀ htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr) : Set G),
      NeighbourOvergroupOmega (QuotientGroup.mk' (oddCore (centralizer
          (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr) : Set G))) ⟨t, htX⟩)
        (((modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoPerp (K := K) m b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
              (plusAnisoTorus m hirr) : Set G))))) (m + 1) 1)
    (hrow : OmegaRowAt t (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
        (plusAnisoTorus m hirr))
      (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c)) .field)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) {k₀ : Subfield F} [CharP k₀ 2] (hσk : ∀ x, x ∈ k₀ ↔ σ x = x)
    (φ : K ≃+* k₀) :
    ∃ hDE : modelToG (e.trans (plusAnisoProjEquiv m hirr).symm) (plusAnisoPerp (K := K) m b c) ≤
        centralizerPerfectCore (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
          (plusAnisoTorus m hirr)),
      ∃ π : centralizerPerfectCore (modelToG (e.trans (plusAnisoProjEquiv m hirr).symm)
            (plusAnisoTorus m hirr)) ≃*
          matrixProjectiveDerived (coordinateQuadMinus (m + 1) F (by omega)
            ((φ b : k₀) : F) ((φ c : k₀) : F)),
        ∀ d, π (Subgroup.inclusion hDE d) =
          incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
            (plusAnisoPerpFieldEquiv (by omega) hirr (e.trans (plusAnisoProjEquiv m hirr).symm)
              φ d) := by
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  set X := modelToG e' (plusAnisoTorus m hirr) with hXdef
  set D := modelToG e' (plusAnisoPerp (K := K) m b c) with hDdef
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, htX, -, -, -, -, -, hZ⟩ :=
    neighbour_data_plusAnisoTorus (X := X) (D := D) (by omega) hirr e' htC rfl rfl
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_plusAnisoTorus (X := X) (D := D)
    hset.standardSetting.standard htC ht hKt (by omega) hirr e' rfl rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_plusAnisoTorus (X := X) (D := D)
    hset.standardSetting.standard htC ht hKt (by omega) hirr e' rfl htX rfl
  obtain ⟨hLie, -⟩ := lieModel_map_plusAnisoPerp (D := D) hKc (by omega) hirr e' rfl
  have hmf : (m + 1, 1) ≠ (4, 1) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  set s := QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ with hs
  set Db := (D.subgroupOf (centralizer (X : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) with hDb
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 :=
    (Subgroup.orderOf_coe (⟨t, htX⟩ : centralizer (X : Set G))).symm.trans ht
  have hs2' : orderOf s = 2 := orderOf_mk_oddCore ht'
  have hs2 : s ^ 2 = 1 := hs2' ▸ pow_orderOf_eq_one s
  have hDperf : ⁅Db, Db⁆ = Db := SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2
  have hD1 : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  obtain ⟨Kc, hKcomp, hK⟩ := hN htX
  obtain ⟨rw', hr, hrK⟩ := neighbourRowOmega_of_alternative hKcomp hK
  obtain ⟨htX', hrow'⟩ := hrow
  have hr1 : rw' = .field := NeighbourRowOmega.unique hs2 hDperf hD1 hr hrow'
  have hKt' : Kc.map (MulAut.conj s).toMonoidHom = Kc := hrK.1 hr1
  have hDX : D ≤ centralizer (X : Set G) :=
    (hD ▸ map_subtype_le _ : D ≤ L ⊓ _).trans inf_le_right
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hLie) hD1
  obtain ⟨hfield, -⟩ := hK.field (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2' hcomp
    hmf (omegaEvenTypeDetAt (m + 1)) (Or.inr rfl) hDm' hKcomp
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
  obtain ⟨ψ, hψ, -⟩ := exists_mulEquiv_comp_eq_incl_minus hσ hσk (by omega : 5 ≤ m + 1)
    (φ b) (φ c) hirr₀ (ψS.trans (statedOmegaPlusEquiv F (m + 1) (by omega))) hτ hD'c hD'm _
    hqinj hεr (plusAnisoPerpFieldEquiv (by omega) hirr e' φ)
  have hinj : Function.Injective q := by
    have : Group.IsPerfect (centralizerPerfectCore X) :=
      isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
    exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hmodel (centralizerPerfectCore X) this
      q hqs hqker.le hkodd
  exact ⟨hDE, (MulEquiv.ofBijective q ⟨hinj, hqs⟩).trans ψ, fun d => hψ d⟩

end NormPlus

open CFSG.Quasithin (perfectCore) in
@[expose] def OmegaMinusTwoEnnolaModelInput : Prop :=
  ∀ (r : ℕ) (_ : 4 ≤ r), ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → ∀ σ : F ≃+* F,
    orderOf σ = 2 → ∀ (k₀ : Subfield F) [CharP k₀ 2], (∀ x, x ∈ k₀ ↔ σ x = x) →
    ∀ φ : K ≃+* k₀,
    ∃ τ : (Fin (r + 1) → Fˣ) →*
        matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c),
      (rootParam 0).map τ = anisoTorus (K := K) (by omega) b c ∧
      (∀ k : Fin (r + 1), ∃ w, ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) ∧
      (∃ g ∈ normalizer (StatedOmega (StatedQuadPlus (r + 1) F) :
          Set (GL (Fin (r + 1) ⊕ Fin (r + 1)) F)),
        ∀ t : Fin (r + 1) → Fˣ, t 0 = 1 → ∃ hD : τ t ∈ anisoPerp (K := K) (by omega) b c,
          g * (((statedOmegaPlusEquiv F (r + 1) (by omega)).symm
            (incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (r + 1) k₀)
              (plusCongr φ (r + 1) (anisoPerpModelEquiv (n := r + 2) (by omega) hirr
                ⟨τ t, hD⟩))) : StatedOmega (StatedQuadPlus (r + 1) F)) :
              GL (Fin (r + 1) ⊕ Fin (r + 1)) F) * g⁻¹ =
            minusNeighbourDiag (RingHom.id F) 0 t) ∧
      ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam k).map τ :
        Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))))

@[expose] noncomputable def plusAnisoPerpModelFieldEquiv {K : Type} [Field K] [Finite K]
    [CharP K 2] {m : ℕ} (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {k₀ : Type} [Field k₀] (φ : K ≃+* k₀) :
    plusAnisoPerp (K := K) m b c ≃*
      matrixProjectiveDerived (coordinateQuadMinus (m + 1) k₀ (by omega) (φ b) (φ c)) :=
  (plusAnisoPerpEquiv hm hirr).trans ((MulEquiv.ofBijective (projHom _)
    ⟨projHom_injective (isHypCoord_coordinateQuadMinus (K := K) (by omega : 1 ≤ m + 1) b c
      (⟨0, by omega⟩ : Fin (m + 1 - 1))).exists_ne_zero, projHom_surjective _⟩).trans
    (minusCongr φ (by omega) b c))

open CFSG.Quasithin (perfectCore) in
@[expose] def OmegaPlusTwoEnnolaModelInput : Prop :=
  ∀ (m : ℕ) (_ : 4 ≤ m), ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], Nat.card F = 4 → ∀ σ : F ≃+* F,
    orderOf σ = 2 → ∀ (k₀ : Subfield F) [CharP k₀ 2], (∀ x, x ∈ k₀ ↔ σ x = x) →
    ∀ φ : K ≃+* k₀,
    ∃ τ : (Fin (m + 1) → Fˣ) →* matrixProjectiveDerived (plusAnisoQuad K m b c),
      (rootParam 0).map τ = plusAnisoTorus m hirr ∧
      (∀ k : Fin (m + 1), ∃ w, ∀ s, w * τ s * w⁻¹ = τ (s ∘ Fin.cycleRange k)) ∧
      (∃ ρ : matrixProjectiveDerived (coordinateQuadMinus (m + 1) F (by omega)
          ((φ b : k₀) : F) ((φ c : k₀) : F)) ≃* StatedOmega (StatedQuadPlus (m + 1) F),
        ∀ t : Fin (m + 1) → Fˣ, t 0 = 1 → ∃ hD : τ t ∈ plusAnisoPerp (K := K) m b c,
          ((ρ (incl k₀ (TwistedE6Pilot.isExtension_coordinateQuadMinus k₀ (by omega) (φ b) (φ c))
              (plusAnisoPerpModelFieldEquiv (by omega) hirr φ ⟨τ t, hD⟩)) :
              StatedOmega (StatedQuadPlus (m + 1) F)) : GL (Fin (m + 1) ⊕ Fin (m + 1)) F) =
            minusNeighbourDiag (RingHom.id F) 0 t) ∧
      ⊤ ≤ ⨆ k, perfectCore (centralizer ((rootParam k).map τ :
        Set (matrixProjectiveDerived (plusAnisoQuad K m b c))))

section ModelReduction

open CFSG.Quasithin (perfectCore) in
theorem perfectCore_modelToG_q2 {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    {L : Subgroup G} (e : L ≃* P) (B : Subgroup P) :
    perfectCore (modelToG e B) = modelToG e (perfectCore B) := by
  rw [modelToG, modelToG, ← CFSG.Quasithin.map_perfectCore, ← CFSG.Quasithin.map_perfectCore]

theorem omegaMinusTwoFieldFrameGenInput_of_model (h : OmegaMinusTwoEnnolaModelInput) :
    OmegaMinusTwoFieldFrameGenInput := by
  intro G _ _ L hset n hn K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow hpar
  obtain ⟨r, rfl⟩ : ∃ r, n = r + 2 := ⟨n - 2, by omega⟩
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2]; rfl) hσ hfix]
    norm_num
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  obtain ⟨τm, hX, hW, ⟨g, hg, hval⟩, hgen⟩ :=
    h r (by omega) K b c hirr hK2 F hF σ hσ ι.fieldRange hσk ι.rangeRestrictFieldEquiv
  obtain ⟨hDE, πn, hπn⟩ := exists_normalized_anisoTorus_two hset (by omega) hK2 hirr e ht hKt hN
    hrow hF hσ hσk ι.rangeRestrictFieldEquiv
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ?_⟩
  set τ : (Fin (r + 1) → Fˣ) →* G := (L.subtype.comp e.symm.toMonoidHom).comp τm with hτ
  have hmapτ : ∀ P : Subgroup (Fin (r + 1) → Fˣ), P.map τ = modelToG e (P.map τm) := by
    intro P
    rw [modelToG, Subgroup.map_map, Subgroup.map_map]
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [hmapτ, hX]
  · intro k
    obtain ⟨w, hw⟩ := hW k
    refine ⟨((e.symm w : L) : G), (e.symm w).2, fun s' => ?_⟩
    change ((e.symm w : L) : G) * ((e.symm (τm s') : L) : G) * ((e.symm w : L) : G)⁻¹ =
      ((e.symm (τm (s' ∘ Fin.cycleRange k)) : L) : G)
    rw [← hw, map_mul, map_mul, map_inv]
    rfl
  · let S := StatedOmega (StatedQuadPlus (r + 1) F)
    refine ⟨πn.trans ((statedOmegaPlusEquiv F (r + 1) (by omega)).symm.trans
      (S.normalizerMonoidHom ⟨g, hg⟩)), fun t' ht' => ?_⟩
    obtain ⟨hD, hv⟩ := hval t' ht'
    have hτD : τ t' ∈ modelToG e (anisoPerp (K := K) _ b c) := symm_mem_modelToG e hD
    refine ⟨hDE hτD, ?_⟩
    have h1 : (⟨τ t', hDE hτD⟩ : centralizerPerfectCore (modelToG e (anisoTorus (K := K) _ b c))) =
        Subgroup.inclusion hDE ⟨τ t', hτD⟩ := rfl
    have h2 : (modelToGEquiv e (anisoPerp (K := K) _ b c)).symm ⟨τ t', hτD⟩ = ⟨τm t', hD⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h3 := hπn ⟨τ t', hτD⟩
    rw [anisoPerpFieldEquivN, MulEquiv.trans_apply, MulEquiv.trans_apply, h2] at h3
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, h3,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hv
  · have hgen' : modelToG e (⊤ : Subgroup (matrixProjectiveDerived
        (coordinateQuadMinus (r + 2) K (by omega) b c))) ≤
        modelToG e (⨆ k, CFSG.Quasithin.perfectCore (centralizer ((rootParam k).map τm :
          Set (matrixProjectiveDerived (coordinateQuadMinus (r + 2) K (by omega) b c))))) :=
      UnitaryPilot.modelToG_mono e hgen
    rw [UnitaryPilot.modelToG_top, UnitaryPilot.modelToG_iSup] at hgen'
    refine hgen'.trans (iSup_le fun k => le_iSup_of_le k ?_)
    rw [hmapτ, UnitaryPilot.inf_centralizer_modelToG, perfectCore_modelToG_q2]

theorem omegaPlusTwoFieldFrameGenInput_of_model (h : OmegaPlusTwoEnnolaModelInput) :
    OmegaPlusTwoFieldFrameGenInput := by
  intro G _ _ L hset m hm K _ _ _ b c hirr hK2 e t ht hKt hnn hN hrow hpar
  obtain ⟨F, _, _, ι, σ, hσ, hfix⟩ := SymplecticPilot.exists_quadraticExtension K
  have : CharP F 2 := charP_of_injective_ringHom ι.injective 2
  have hF : Nat.card F = 4 := by
    rw [SymplecticPilot.natCard_eq_two_pow_two_mul_of_fix ι (f := 1) (by rw [hK2]; rfl) hσ hfix]
    norm_num
  have : CharP ι.fieldRange 2 := RingHom.charP ι.fieldRange.subtype Subtype.val_injective 2
  have hσk : ∀ x, x ∈ ι.fieldRange ↔ σ x = x := fun x => by
    rw [hfix, RingHom.mem_fieldRange, Set.mem_range]
  obtain ⟨τm, hX, hW, ⟨ρ, hval⟩, hgen⟩ :=
    h m hm K b c hirr hK2 F hF σ hσ ι.fieldRange hσk ι.rangeRestrictFieldEquiv
  set e' := e.trans (plusAnisoProjEquiv m hirr).symm with he'
  obtain ⟨hDE, πn, hπn⟩ := exists_normalized_plusAnisoTorus_two hset hm hK2 hirr e ht hKt hN
    hrow hF hσ hσk ι.rangeRestrictFieldEquiv
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, ?_⟩
  set τ : (Fin (m + 1) → Fˣ) →* G := (L.subtype.comp e'.symm.toMonoidHom).comp τm with hτ
  have hmapτ : ∀ P : Subgroup (Fin (m + 1) → Fˣ), P.map τ = modelToG e' (P.map τm) := by
    intro P
    rw [modelToG, Subgroup.map_map, Subgroup.map_map]
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [hmapτ, hX]
  · intro k
    obtain ⟨w, hw⟩ := hW k
    refine ⟨((e'.symm w : L) : G), (e'.symm w).2, fun s' => ?_⟩
    change ((e'.symm w : L) : G) * ((e'.symm (τm s') : L) : G) * ((e'.symm w : L) : G)⁻¹ =
      ((e'.symm (τm (s' ∘ Fin.cycleRange k)) : L) : G)
    rw [← hw, map_mul, map_mul, map_inv]
    rfl
  · refine ⟨πn.trans ρ, fun t' ht' => ?_⟩
    obtain ⟨hD, hv⟩ := hval t' ht'
    have hτD : τ t' ∈ modelToG e' (plusAnisoPerp (K := K) m b c) := symm_mem_modelToG e' hD
    refine ⟨hDE hτD, ?_⟩
    have h1 : (⟨τ t', hDE hτD⟩ : centralizerPerfectCore (modelToG e' (plusAnisoTorus m hirr))) =
        Subgroup.inclusion hDE ⟨τ t', hτD⟩ := rfl
    have h2 : (modelToGEquiv e' (plusAnisoPerp (K := K) m b c)).symm ⟨τ t', hτD⟩ =
        ⟨τm t', hD⟩ := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    have h3 := hπn ⟨τ t', hτD⟩
    rw [plusAnisoPerpFieldEquiv, MulEquiv.trans_apply, h2] at h3
    rw [MulEquiv.trans_apply, h1]
    exact (congrArg (fun x => ((ρ x : StatedOmega (StatedQuadPlus (m + 1) F)) :
      GL (Fin (m + 1) ⊕ Fin (m + 1)) F)) h3).trans hv
  · have hgen' : modelToG e' (⊤ : Subgroup (matrixProjectiveDerived (plusAnisoQuad K m b c))) ≤
        modelToG e' (⨆ k, CFSG.Quasithin.perfectCore (centralizer ((rootParam k).map τm :
          Set (matrixProjectiveDerived (plusAnisoQuad K m b c))))) :=
      UnitaryPilot.modelToG_mono e' hgen
    rw [UnitaryPilot.modelToG_top, UnitaryPilot.modelToG_iSup] at hgen'
    refine hgen'.trans (iSup_le fun k => le_iSup_of_le k ?_)
    rw [hmapτ, UnitaryPilot.inf_centralizer_modelToG, perfectCore_modelToG_q2]

theorem omegaMinusTwoInput_of_model (h10 : OmegaMinusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (h : OmegaMinusTwoEnnolaModelInput) :
    OmegaMinusTwoInput :=
  omegaMinusTwoInput_of_frameGen h10 hcat (omegaMinusTwoFieldFrameGenInput_of_model h)

theorem omegaPlusTwoInput_of_model (h10 : OmegaPlusTwoTenInput)
    (hcat : ∀ m : ℕ, 5 ≤ m → OmegaCatalogueClausesAt m) (h : OmegaPlusTwoEnnolaModelInput) :
    OmegaPlusTwoInput :=
  omegaPlusTwoInput_of_frameGen h10 hcat (omegaPlusTwoFieldFrameGenInput_of_model h)

end ModelReduction

end CFSG.SeitzReduction.OmegaPilot
