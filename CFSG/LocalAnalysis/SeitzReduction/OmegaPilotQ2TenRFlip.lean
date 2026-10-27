module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenRNorm
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotFiveCover
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

@[expose] def OmegaMinusTwoTenFlipModelInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
    ∀ (k₀ : Type) [Field k₀] [Finite k₀] [CharP k₀ 2] (φ : K ≃+* k₀),
    ∃ w : matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c),
      w ∈ normalizer (anisoTorus (K := K) (n := 5) (by norm_num) b c :
        Set (matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c))) ∧
      w ∈ normalizer (anisoPerp (K := K) (n := 5) (by norm_num) b c :
        Set (matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c))) ∧
      ∀ x x' : anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c,
        (x' : matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) = w * x * w⁻¹ →
        plusCongr φ (5 - 1) (anisoPerpModelEquiv (by norm_num) hirr x') =
          plusFlipAut (5 - 1) k₀ (by norm_num)
            (plusCongr φ (5 - 1) (anisoPerpModelEquiv (by norm_num) hirr x))

section Norm


variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_normalized_anisoTorus_five_of_flip (hset : SeitzSetting G L) {K : Type}
    [Field K] [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = modelToG e (anisoTorus (K := K) (by norm_num) b c))
    (htX : t ∈ centralizer (X : Set G))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKcomp : IsComponent Kc)
    (hK : OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)
      (((modelToG e (anisoPerp (K := K) (by norm_num) b c)).subgroupOf
          (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc 4 1)
    (hKt' : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
        ⟨t, htX⟩)).toMonoidHom = Kc)
    (hlie : LieModel Kc .POmegaPlus 4 2 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) {σ : F ≃+* F}
    (hσ : orderOf σ = 2) {k₀ : Subfield F} [CharP k₀ 2] (hσk : ∀ x, x ∈ k₀ ↔ σ x = x)
    (φ : K ≃+* k₀) {w : matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)}
    (hwX : w ∈ normalizer (anisoTorus (K := K) (n := 5) (by norm_num) b c :
      Set (matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c))))
    (hwD : w ∈ normalizer (anisoPerp (K := K) (n := 5) (by norm_num) b c :
      Set (matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c))))
    (hwJ : ∀ x x' : anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c,
      (x' : matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) = w * x * w⁻¹ →
      plusCongr φ (5 - 1) (anisoPerpModelEquiv (by norm_num) hirr x') =
        plusFlipAut (5 - 1) k₀ (by norm_num)
          (plusCongr φ (5 - 1) (anisoPerpModelEquiv (by norm_num) hirr x))) :
    ∃ hDE : modelToG e (anisoPerp (K := K) (by norm_num) b c) ≤ centralizerPerfectCore X,
      ∃ π : centralizerPerfectCore X ≃* matrixProjectiveDerived (coordinateQuadPlus (5 - 1) F),
        ∀ d, π (Subgroup.inclusion hDE d) =
          incl k₀ (E7Pilot.isExtension_coordinateQuadPlus (5 - 1) k₀)
            (anisoPerpFieldEquivN (by norm_num) hirr e φ d) := by
  set D := modelToG e (anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c) with hDdef
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, -, -, -, -, -, -, hZ⟩ :=
    neighbour_data_anisoTorus (X := X) (D := D) (by norm_num) hirr e htC hX rfl
  obtain ⟨hLt, hD, hDq, hXo⟩ := bLift_inputs_anisoTorus (X := X) (D := D)
    hset.standardSetting.standard htC ht hKt (by norm_num) hirr e hX rfl
  obtain ⟨hcomp, hsyl, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting (X := X) (D := D)
    hset hKc (by norm_num) hirr e htC ht hX htX rfl
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp (D := D) hKc (by norm_num) hirr e rfl
  set Db := (D.subgroupOf (centralizer (X : Set G))).map
    (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) with hDb
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 :=
    (Subgroup.orderOf_coe (⟨t, htX⟩ : centralizer (X : Set G))).symm.trans ht
  have hs2' : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_mk_oddCore ht'
  have hD1 : Db ≠ ⊥ := ne_bot_of_isQuasisimple hcomp.2.2
  have hDX : D ≤ centralizer (X : Set G) :=
    (hD ▸ map_subtype_le _ : D ≤ L ⊓ _).trans inf_le_right
  have hDm' := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq
    (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hLie) hD1
  obtain ⟨hfield, -⟩ := OmegaNeighbourAlternative.field_of_lieModel
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hs2' hcomp (omegaEvenTypeDetAt 4)
    (Or.inl rfl) hDm' hKcomp hK hKt' hlie
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
  have hinj : Function.Injective q := by
    have : Group.IsPerfect (centralizerPerfectCore X) :=
      isPerfect_iff.mpr (F4Pilot.commutator_centralizerPerfectCore X)
    exact SeitzQ2.oddSchurTrivial_of_lieModel_POmegaPlus hmodel (centralizerPerfectCore X) this
      q hqs hqker.le hkodd
  obtain ⟨s, hs⟩ : ∃ s : G, s = ((e.symm w : L) : G) := ⟨_, rfl⟩
  have hsX : s ∈ normalizer (X : Set G) := by
    rw [hX, hs]
    exact UnitaryPilot.symm_mem_normalizer_modelToG e hwX
  have hsD : s ∈ normalizer (D : Set G) := hs ▸ UnitaryPilot.symm_mem_normalizer_modelToG e hwD
  have hsE : s ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _ hsX
  obtain ⟨θ, hθ⟩ : ∃ θ : MulAut Kc, θ = autOfQuotient q hqs hqker
      ((centralizerPerfectCore X).normalizerMonoidHom ⟨s, hsE⟩) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : MulAut D, a = D.normalizerMonoidHom ⟨s, hsD⟩ := ⟨_, rfl⟩
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
  set j := anisoPerpFieldEquivN (by norm_num : 4 ≤ 5) hirr e φ with hj
  have hjx : ∀ x : anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c,
      j (modelToGEquiv e (anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c) x) =
        plusCongr φ (5 - 1) (anisoPerpModelEquiv (by norm_num) hirr x) := by
    intro x
    rw [hj, anisoPerpFieldEquivN, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hγ : MulAut.congr j a = plusFlipAut (5 - 1) k₀ (by norm_num) := by
    ext y
    obtain ⟨d, rfl⟩ := j.surjective y
    obtain ⟨x, rfl⟩ := (modelToGEquiv e (anisoPerp (K := K) (n := 5) _ b c)).surjective d
    change j (a (j.symm (j _))) = _
    rw [MulEquiv.symm_apply_apply]
    have hx' : w * x * w⁻¹ ∈ anisoPerp (K := K) (n := 5) _ b c :=
      (mem_normalizer_iff.1 hwD x).1 x.2
    have h2 : a (modelToGEquiv e (anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c) x) =
        modelToGEquiv e (anisoPerp (K := K) (by norm_num : 1 ≤ 5) b c) ⟨_, hx'⟩ := by
      apply Subtype.ext
      rw [ha, Subgroup.normalizerMonoidHom_apply_apply_coe, UnitaryPilot.coe_modelToGEquiv_apply,
        UnitaryPilot.coe_modelToGEquiv_apply]
      simp only [hs, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, hjx, hjx]
    exact hwJ x ⟨_, hx'⟩ rfl
  have hγF := plusFlipAut_smul_pointFamily (5 - 1) k₀ (by norm_num)
  have hγX := plusFlipAut_smul_plusCX (5 - 1) k₀ (by norm_num)
  have hγX' := plusFlipAut_smul_plusCXstar (5 - 1) k₀ (by norm_num)
  rw [← hγ] at hγF hγX hγX'
  obtain ⟨ψS⟩ := nonempty_mulEquiv_statedOmegaPlus_of_lieModel (by omega) hmodel F
    (by rw [hF]; norm_num)
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_comp_eq_incl_four hσ hσk
    (ψS.trans (statedOmegaPlusEquiv F 4 (by omega))) hτ hout hD'c hD'm _ hqinj hεr j θ a hθa
    hγF hγX hγX'
  exact ⟨hDE, (MulEquiv.ofBijective q ⟨hinj, hqs⟩).trans ψ, fun d => hψ d⟩

theorem omegaMinusTwoTenNormalizedInput_of_flip (hflip : OmegaMinusTwoTenFlipModelInput) :
    OmegaMinusTwoTenNormalizedInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt _ htX Kc hKc hK hKt' hlie F _ _ _ hF σ hσ
    k₀ _ hσk φ
  obtain ⟨w, hwX, hwD, hwJ⟩ := hflip K b c hirr hK2 k₀ φ
  exact exists_normalized_anisoTorus_five_of_flip hset hK2 hirr e ht hKt rfl htX hKc hK hKt' hlie
    hF hσ hσk φ hwX hwD hwJ

end Norm

end CFSG.SeitzReduction.OmegaPilot
