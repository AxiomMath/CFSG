module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenBHR8
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotQ2TenFrame
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotPositionOuter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallestGraph
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusUniqueBoundsAut
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadPlus coordinateQuadMinus regular_coordinateQuadMinus)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Generic

theorem card_sup_le_mul_of_le_centralizer {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hAB : A ≤ centralizer (B : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    (mem_centralizer_iff.1 (hAB a.2) b b.2).symm
  have hrange : (MonoidHom.noncommCoprod A.subtype B.subtype hcomm).range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd _)

theorem card_centralizer_quotient_mul_card_le {H : Type*} [Group H] [Finite H]
    (N : Subgroup H) [N.Normal] (hN : Odd (Nat.card N)) {t : H} (ht : t * t = 1)
    {X : Subgroup H} (hXN : X ≤ N) (hXt : X ≤ centralizer ({t} : Set H)) :
    Nat.card (centralizer ({(t : H ⧸ N)} : Set (H ⧸ N))) * Nat.card X ≤
      Nat.card (centralizer ({t} : Set H)) := by
  set M := centralizer ({t} : Set H) with hM
  set φ : M →* H ⧸ N := (QuotientGroup.mk' N).comp M.subtype with hφ
  have hC : centralizer ({(t : H ⧸ N)} : Set (H ⧸ N)) ≤ φ.range := by
    intro c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    have hct := mem_centralizer_singleton_iff.1 hc
    have hx : x⁻¹ * t * x * t ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      have htt : (t : H ⧸ N) * t = 1 := by rw [← QuotientGroup.mk_mul, ht]; rfl
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      calc (x : H ⧸ N)⁻¹ * t * x * t = (x : H ⧸ N)⁻¹ * (t * x) * t := by group
        _ = (x : H ⧸ N)⁻¹ * (x * t) * t := by rw [hct]
        _ = (x : H ⧸ N)⁻¹ * x * (t * t) := by group
        _ = 1 := by rw [htt]; group
    obtain ⟨z, hz, hxz⟩ := LinearPilot.exists_commute_lift_of_odd hN ht hx
    refine ⟨⟨x * z, mem_centralizer_singleton_iff.2 hxz⟩, ?_⟩
    simp [hφ, (QuotientGroup.eq_one_iff z).2 hz]
  have hX : X.subgroupOf M ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hXN (mem_subgroupOf.1 hx)
  have hXc : Nat.card (X.subgroupOf M) = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXt).toEquiv
  have hkr : Nat.card φ.ker * Nat.card φ.range = Nat.card M := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  calc Nat.card (centralizer ({(t : H ⧸ N)} : Set (H ⧸ N))) * Nat.card X
      ≤ Nat.card φ.range * Nat.card φ.ker :=
        Nat.mul_le_mul (Subgroup.card_le_of_le hC) (hXc ▸ Subgroup.card_le_of_le hX)
    _ = Nat.card M := by rw [mul_comm, hkr]

end Generic

section Automizer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_outer_le_two_of_mulEquiv_minus_five {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) :
    Nat.card (Outer L) ≤ 2 := by
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  have h := card_outer_coordinateMinus_dvd (n := 5) le_rfl hKc (by norm_num) hirr
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact (Nat.le_of_dvd (by norm_num) h).trans (by norm_num)

theorem card_centralizer_anisoTorus_five_le (hset : SeitzSetting G L) {K : Type} [Field K]
    [Finite K] [CharP K 2] (hK2 : Nat.card K = 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (htX : t ∈ centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)) :
    Nat.card (centralizer ({QuotientGroup.mk' (oddCore (centralizer
        (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩} :
      Set (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G) ⧸
        oddCore (centralizer (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))))) ≤
      4 * 174182400 := by
  set X := modelToG e (anisoTorus (K := K) (by norm_num) b c) with hXdef
  set D := modelToG e (anisoPerp (K := K) (by norm_num) b c) with hDdef
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, -, hXC, hXodd, -, hDC, -, -⟩ :=
    neighbour_data_anisoTorus (by norm_num) hirr e htC hXdef hDdef
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp hKc le_rfl hirr e hDdef
  have hDcard : Nat.card D = 174182400 :=
    (card_of_lieModel_POmega_two (.inl rfl) hLie).trans (by decide)
  have hLX : L ⊓ centralizer (X : Set G) = X ⊔ D := by
    rw [hXdef, hDdef, modelToG, modelToG, F4Pilot.inf_centralizer_map_symm,
      centralizer_anisoTorus (by norm_num) hirr, Subgroup.map_sup, Subgroup.map_sup]
  have hXD : X ≤ centralizer (D : Set G) := le_centralizer_iff.mp (hDC.trans inf_le_left)
  have hLXc : Nat.card (L ⊓ centralizer (X : Set G) : Subgroup G) ≤ Nat.card X * 174182400 := by
    rw [hLX, ← hDcard]
    exact card_sup_le_mul_of_le_centralizer hXD
  set H := centralizer (X : Set G) with hHdef
  have ht2 : (⟨t, htX⟩ : H) * ⟨t, htX⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← ht, pow_orderOf_eq_one]; rfl)
  have hXN : X.subgroupOf H ≤ oddCore H := fun x hx =>
    LinearPilot.mem_oddCore_centralizer_of_le_centralizer_odd hXC hXodd (mem_subgroupOf.1 hx)
  have hXt : X.subgroupOf H ≤ centralizer ({(⟨t, htX⟩ : H)} : Set H) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_iff.1 htX x (mem_subgroupOf.1 hx))
  have h1 := card_centralizer_quotient_mul_card_le (oddCore H)
    (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore H) ht2 hXN hXt
  have hXc : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv
  rw [hXc] at h1
  set M := (centralizer ({(⟨t, htX⟩ : H)} : Set H)).map H.subtype with hMdef
  have hMc : Nat.card M = Nat.card (centralizer ({(⟨t, htX⟩ : H)} : Set H)) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hMt : M ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y * ⟨t, htX⟩ = ⟨t, htX⟩ * y := mem_centralizer_singleton_iff.1 hy
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val hy'
  have hMX : M ≤ H := map_subtype_le _
  have hCN := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard
    hset.standardSetting.standard htC ht
  have h2 := E7Pilot.natCard_le_two_mul_card_outer_mul_card_inf ht hKt hCN hMt
  have hout := card_outer_le_two_of_mulEquiv_minus_five hK2 hirr e
  have h3 : Nat.card (M ⊓ L : Subgroup G) ≤ Nat.card (L ⊓ centralizer (X : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf inf_le_right (inf_le_left.trans hMX))
  have hXpos : 0 < Nat.card X := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right (h1.trans ?_) hXpos
  rw [← hMc]
  calc Nat.card M ≤ 2 * Nat.card (Outer L) * Nat.card (M ⊓ L : Subgroup G) := h2
    _ ≤ 2 * 2 * (Nat.card X * 174182400) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hout) (h3.trans hLXc)
    _ = 4 * 174182400 * Nat.card X := by ring

end Automizer

section FieldSporadic

open CFSG.LocalAnalysis.ComponentInitial

theorem fieldRow_sporadic_data (hspor : OmegaEightSporadicStatement) {Y : Type} [Group Y]
    [Finite Y] (hO : pPrimeCore 2 Y = ⊥) {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) (hDm : LieModel (D ⧸ center D) tag 4 2 1)
    {Kc : Subgroup Y} (hKc : IsComponent Kc) (hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc)
    (hDK : D ≤ Kc) (hsN : s ∈ normalizer (Kc : Set Y))
    (hout : Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hZodd : Odd (Nat.card (center Kc))) (hsp : NativeSporadic.SporadicRep (Kc ⧸ center Kc)) :
    tag = .POmegaPlus ∧ Nat.card (Kc ⊓ centralizer ({s} : Set Y) : Subgroup Y) = 1045094400 := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc₀, -, -, -, -, hiff, hfix, -⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  have hDq := hD.2.2
  have hDKc : ⁅D, Kc⁆ ≠ ⊥ := by
    intro h
    have h1 : ⁅D, D⁆ ≤ ⁅D, Kc⁆ := commutator_mono le_rfl hDK
    rw [h, SymplecticPilot.commutator_eq_self_of_isQuasisimple hDq, le_bot_iff] at h1
    exact ne_bot_of_isQuasisimple hDq h1
  have hDcomp : IsComponent (D.subgroupOf (Kc ⊓ centralizer ({s} : Set Y))) := by
    rcases (hiff Kc hKc).1 hDKc with h | h
    · subst h
      exact (hfix hKt).2
    · have h2 := CentralizerComponents.map_conj_map_conj hs2 Kc₀
      rw [← h, hKt] at h2
      subst h2
      exact (hfix hKt).2
  obtain ⟨hD'c, hD'm, -, -⟩ :=
    UnitaryPilot.isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK hDs hDcomp hDm
  have hZ : center Kc = ⊥ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hZodd
  have hq := hKc.1
  have := hq.2.1
  have hSimp : IsSimpleGroup Kc := (quotientCenterMulEquiv hZ).symm.isSimpleGroup
  have hna : ∃ a b : Kc, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨quotientCenterMulEquiv hZ a, quotientCenterMulEquiv hZ b, fun h => hab ?_⟩
    apply (quotientCenterMulEquiv hZ).injective
    rw [map_mul, map_mul, h]
  have hspK : NativeSporadic.SporadicRep Kc := by
    obtain ⟨nm, ⟨φ⟩⟩ := hsp
    exact ⟨nm, ⟨(quotientCenterMulEquiv hZ).symm.trans φ⟩⟩
  have hτ := orderOf_normalizerMonoidHom_of_not_mem_range hs2 hout
  obtain ⟨-, htag', -, hcard⟩ := hspor Kc hSimp hna hspK _ hτ tag _ htag hD'c hD'm
  refine ⟨htag', ?_⟩
  rw [← F4Pilot.map_fixedSubgroup_normalizerMonoidHom Kc hsN,
    Subgroup.card_map_of_injective Kc.subtype_injective]
  exact hcard

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_fieldRow_sporadic_anisoTorus_five (hset : SeitzSetting G L)
    (hspor : OmegaEightSporadicStatement) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus 5 K (by norm_num) b c)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G} (hX : X = modelToG e (anisoTorus (K := K) (by norm_num) b c))
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = modelToG e (anisoPerp (K := K) (by norm_num) b c))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hKt' : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom = Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hZodd : Odd (Nat.card (center Kc))) (hsp : NativeSporadic.SporadicRep (Kc ⧸ center Kc)) :
    False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc2 : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, -, -, -, -, hDC, hDq, hZ⟩ := neighbour_data_anisoTorus (by norm_num) hirr e htC hX hDe
  obtain ⟨hLie, -⟩ := lieModel_map_anisoPerp hKc2 le_rfl hirr e hDe
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_anisoTorus_of_seitzSetting hset hKc2 (by norm_num) hirr e htC ht hX htX hDe
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hDm := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple
    (hDC.trans inf_le_left) hDq (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hLie)
    (ne_bot_of_isQuasisimple hcomp.2.2)
  obtain ⟨-, hcard⟩ := fieldRow_sporadic_data hspor
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (orderOf_mk_oddCore ht') hcomp (.inl rfl)
    hDm hKc hKt' hDK hsN hout hZodd hsp
  subst hX
  have hle := card_centralizer_anisoTorus_five_le hset hK2 hirr e ht hKt htX
  have h1 := Subgroup.card_le_of_le (inf_le_right (a := Kc) (b := centralizer
    ({QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩} : Set _)))
  have h2 : (1045094400 : ℕ) ≤ 4 * 174182400 := hcard ▸ h1.trans hle
  exact absurd h2 (by norm_num)

theorem false_of_fieldRow_sporadic_plusAnisoTorus_three (hset : SeitzSetting G L)
    (hspor : OmegaEightSporadicStatement) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK2 : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {X : Subgroup G}
    (hX : X = modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoTorus 3 hirr))
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoPerp (K := K) 3 b c))
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hKt' : Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))
      ⟨t, htX⟩)).toMonoidHom = Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hout : Kc.normalizerMonoidHom ⟨_, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range)
    (hZodd : Odd (Nat.card (center Kc))) (hsp : NativeSporadic.SporadicRep (Kc ⧸ center Kc)) :
    False := by
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hKc2 : Nat.card K = 2 ^ 1 := by rw [hK2, pow_one]
  obtain ⟨-, -, -, -, -, hDC, hDq, hZ⟩ := neighbour_data_plusAnisoTorus le_rfl hirr
    (e.trans (plusAnisoProjEquiv 3 hirr).symm) htC hX hDe
  obtain ⟨hLie, -⟩ := lieModel_map_plusAnisoPerp hKc2 le_rfl hirr
    (e.trans (plusAnisoProjEquiv 3 hirr).symm) hDe
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_plusAnisoTorus hset.standardSetting.standard
    htC ht hKt le_rfl hirr (e.trans (plusAnisoProjEquiv 3 hirr).symm) hX htX hDe
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hDm := UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple
    (hDC.trans inf_le_left) hDq (LinearPilot.lieModel_quotient_center_of_center_eq_bot hZ hLie)
    (ne_bot_of_isQuasisimple hcomp.2.2)
  obtain ⟨htag, -⟩ := fieldRow_sporadic_data hspor
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (orderOf_mk_oddCore ht') hcomp (.inr rfl)
    hDm hKc hKt' hDK hsN hout hZodd hsp
  cases htag

end FieldSporadic

section Inputs

@[expose] def OmegaMinusTwoTenFieldLieInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K),
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → Nat.card K = 2 →
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
          LieModel Kc .POmegaPlus 4 2 2 → False

@[expose] def OmegaPlusTwoTenFieldLieInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
      (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0), Nat.card K = 2 →
      ∀ (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (3 + 2) K)) (t : G),
        orderOf t = 2 → centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
        ¬ (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoPerp (K := K) 3 b c)).subgroupOf
            (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer
            (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G))))).Normal →
        ∀ (htX : t ∈ centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
            (plusAnisoTorus 3 hirr) : Set G))
          (Kc : Subgroup (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
              (plusAnisoTorus 3 hirr) : Set G) ⧸ oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G)))),
          IsComponent Kc →
          OmegaNeighbourAlternative (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)
            (((modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoPerp (K := K) 3 b c)).subgroupOf
                (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))).map
              (QuotientGroup.mk' (oddCore (centralizer
                (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                  (plusAnisoTorus 3 hirr) : Set G))))) Kc 4 1 →
          Kc.map (MulAut.conj (QuotientGroup.mk' (oddCore (centralizer
              (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
                (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)).toMonoidHom = Kc →
          LieModel Kc .POmegaPlus 4 2 2 → False

theorem omegaMinusTwoTenFieldInput_of_lie (hspor : OmegaEightSporadicStatement)
    (hlie : OmegaMinusTwoTenFieldLieInput) : OmegaMinusTwoTenFieldInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn hN hr
  obtain ⟨htX, hrow⟩ := hr
  obtain ⟨Kc, hKc, hK⟩ := hN htX
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_anisoTorus_of_seitzSetting
    (X := modelToG e (anisoTorus (K := K) (by norm_num) b c))
    (D := modelToG e (anisoPerp (K := K) (by norm_num) b c)) hset
    (by rw [hK2, pow_one] : Nat.card K = 2 ^ 1) (by norm_num) hirr e htC ht rfl htX rfl
  have ht' : orderOf (⟨t, htX⟩ : centralizer
      (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hs2 := (orderOf_mk_oddCore ht') ▸ pow_orderOf_eq_one
    (QuotientGroup.mk' (oddCore (centralizer
      (modelToG e (anisoTorus (K := K) (by norm_num) b c) : Set G))) ⟨t, htX⟩)
  obtain ⟨r, hr', hriff⟩ := neighbourRowOmega_of_alternative hKc hK
  have hr1 : r = .field := NeighbourRowOmega.unique hs2
    (SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2)
    (ne_bot_of_isQuasisimple hcomp.2.2) hr' hrow
  have hKt' := hriff.1 hr1
  obtain ⟨hDKK, ⟨-, hDK, hsK, hsN, hout, hZodd, hlist⟩ | ⟨hKt'', -⟩⟩ := hK
  · rcases hlist with hlie' | ⟨-, -, hsp⟩
    · have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd
        (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hZodd
      exact hlie G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc
        ⟨hDKK, .inl ⟨hKt', hDK, hsK, hsN, hout, hZodd, .inl hlie'⟩⟩ hKt'
        (lieModel_of_mulEquiv (quotientCenterMulEquiv hZ) hlie')
    · exact false_of_fieldRow_sporadic_anisoTorus_five hset hspor hK2 hirr e ht hKt rfl htX rfl
        hKc hKt' hDK.le hsN hout hZodd hsp
  · exact absurd hKt' hKt''

theorem omegaPlusTwoTenFieldInput_of_lie (hspor : OmegaEightSporadicStatement)
    (hlie : OmegaPlusTwoTenFieldLieInput) : OmegaPlusTwoTenFieldInput := by
  intro G _ _ L hset K _ _ _ b c hirr hK2 e t ht hKt hnn hN hr
  obtain ⟨htX, hrow⟩ := hr
  obtain ⟨Kc, hKc, hK⟩ := hN htX
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨hcomp, -, -⟩ := neighbour_standard_plusAnisoTorus
    (X := modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoTorus 3 hirr))
    (D := modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm) (plusAnisoPerp (K := K) 3 b c))
    hset.standardSetting.standard htC ht hKt le_rfl hirr _ rfl htX rfl
  have ht' : orderOf (⟨t, htX⟩ : centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
      (plusAnisoTorus 3 hirr) : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hs2 := (orderOf_mk_oddCore ht') ▸ pow_orderOf_eq_one
    (QuotientGroup.mk' (oddCore (centralizer (modelToG (e.trans (plusAnisoProjEquiv 3 hirr).symm)
      (plusAnisoTorus 3 hirr) : Set G))) ⟨t, htX⟩)
  obtain ⟨r, hr', hriff⟩ := neighbourRowOmega_of_alternative hKc hK
  have hr1 : r = .field := NeighbourRowOmega.unique hs2
    (SymplecticPilot.commutator_eq_self_of_isQuasisimple hcomp.2.2)
    (ne_bot_of_isQuasisimple hcomp.2.2) hr' hrow
  have hKt' := hriff.1 hr1
  obtain ⟨hDKK, ⟨-, hDK, hsK, hsN, hout, hZodd, hlist⟩ | ⟨hKt'', -⟩⟩ := hK
  · rcases hlist with hlie' | ⟨-, -, hsp⟩
    · have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd
        (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hZodd
      exact hlie G L hset K b c hirr hK2 e t ht hKt hnn htX Kc hKc
        ⟨hDKK, .inl ⟨hKt', hDK, hsK, hsN, hout, hZodd, .inl hlie'⟩⟩ hKt'
        (lieModel_of_mulEquiv (quotientCenterMulEquiv hZ) hlie')
    · exact false_of_fieldRow_sporadic_plusAnisoTorus_three hset hspor hK2 hirr e ht hKt rfl htX
        rfl hKc hKt' hDK.le hsN hout hZodd hsp
  · exact absurd hKt' hKt''


theorem omegaMinusTwoTenInput_of_lie (hcat : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) (hlie : OmegaMinusTwoTenFieldLieInput) :
    OmegaMinusTwoTenInput :=
  omegaMinusTwoTenInput_of_inputs (omegaMinusTwoTenHR8Input_of_clauses hcat hspor)
    (omegaMinusTwoTenFieldInput_of_lie hspor hlie)

theorem omegaPlusTwoTenInput_of_lie (hcat : OmegaCatalogueClausesAt 4)
    (hspor : OmegaEightSporadicStatement) (hlie : OmegaPlusTwoTenFieldLieInput) :
    OmegaPlusTwoTenInput :=
  omegaPlusTwoTenInput_of_hr8_field (omegaPlusTwoTenHR8Input_of_clauses hcat hspor)
    (omegaPlusTwoTenFieldInput_of_lie hspor hlie)

end Inputs

end CFSG.SeitzReduction.OmegaPilot
