module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2Position
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFourHR8
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Small

variable {Y : Type} [Group Y]

@[expose] def NeighbourOvergroupSLmInner (s : Y) (D : Subgroup Y) (m f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D < Kc ∧ s ∈ Kc ∧ s ∉ centralizer (Kc : Set Y) ∧
    center Kc = ⊥ ∧ SLmSmall (Kc ⧸ center Kc) m f

@[expose] def NeighbourOvergroupSLmSmall (s : Y) (D : Subgroup Y) (m f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D < Kc ∧ Kc.map (MulAut.conj s).toMonoidHom = Kc ∧
    s ∉ centralizer (Kc : Set Y) ∧ center Kc = ⊥ ∧ SLmSmall (Kc ⧸ center Kc) m f

theorem NeighbourOvergroupSLmInner.small {s : Y} {D : Subgroup Y} {m f : ℕ}
    (h : NeighbourOvergroupSLmInner s D m f) : NeighbourOvergroupSLmSmall s D m f := by
  obtain ⟨Kc, hKc, hDK, hsK, hsC, hZ, hsm⟩ := h
  exact ⟨Kc, hKc, hDK, mem_normalizer_iff_map_conj_eq.1 (le_normalizer hsK), hsC, hZ, hsm⟩

theorem not_neighbourOvergroupSLmSmall {s : Y} {D : Subgroup Y} {m f : ℕ}
    (hmf : 5 ≤ m ∨ 2 ≤ f) : ¬ NeighbourOvergroupSLmSmall s D m f := by
  rintro ⟨Kc, -, -, -, -, -, hsm⟩
  exact E6Pilot.not_slmSmall hmf hsm

theorem neighbour_overgroup_slm_center_or_inner_of_pPrimeCore_eq_bot {m f : ℕ} (hm : 3 ≤ m)
    (hcat : SLmCatalogueClausesAt m) [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) :
    NeighbourOvergroupSLm s D m f ∨ NeighbourOvergroupSLmInner s D m f := by
  have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
  have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
  have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
    (isComponentOf_iff_isComponent_subgroupOf hDs).1
      ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
  obtain ⟨-, Kc, hKc, -, hDKK, -, -, hfix, hswap⟩ :=
    exists_isComponent_orbit_of_isComponent_centralizer hO hs2 hDs hDc
  by_cases hKt : Kc.map (MulAut.conj s).toMonoidHom = Kc
  · obtain ⟨hDK, hDcomp⟩ := hfix hKt
    have hDne : D ≠ Kc := by
      rintro rfl
      exact hnn (F4Pilot.normal_of_isComponent_of_standard hKc hstd)
    have hsN : s ∈ normalizer (Kc : Set Y) := mem_normalizer_iff_map_conj_eq.2 hKt
    have hKs : ¬ Kc ≤ centralizer ({s} : Set Y) := by
      intro hKs
      rw [inf_eq_left.mpr hKs] at hDcomp
      exact hDne (F4Pilot.eq_of_isComponent_subgroupOf hKc.1 hDK hDcomp)
    have hτ2 := F4Pilot.orderOf_normalizerMonoidHom_eq_two Kc hsN hs2 hKs
    obtain ⟨hD'c, hD'm, hD'map⟩ :=
      isComponent_fixedSubgroup_of_le_of_quotient hsN hDK hDs hDcomp hDm
    have hcatK := hsec Kc hKc
    by_cases hsK : s ∈ Kc
    · right
      have hin := F4Pilot.normalizerMonoidHom_mem_range_conj Kc hsN hsK
      have hsmall := E6Pilot.fixedCentralizerTwoSmall_of_card_le_two _ hDK hsyl _ hD'map
      obtain ⟨-, -, _, -, -, -, hsm⟩ := hcat.2.2.2.2.2 Kc hKc.1 _ hτ2 m f _ hD'c hD'm
      have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc (hsm hin hsmall).1
      have hsC : s ∉ centralizer (Kc : Set Y) := fun h =>
        hKs fun k hk => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 h k hk)
      exact ⟨Kc, hKc, lt_of_le_of_ne hDK hDne, hsK, hsC, hZ,
        slm_inner_small_of_clauses hcat hKc.1 hcatK _ hτ2 hm _ hD'c hD'm hin hsmall⟩
    · left
      exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, lt_of_le_of_ne hDK hDne, hsK, hsN,
        slm_overgroup_catalogue hcat hKc.1 hcatK _ hτ2 hm _ hD'c hD'm
          (F4Pilot.fixedCentralizerTwoFree_of_card_le_two hsN hs hsK hDs hDK hsyl _ hD'map)⟩⟩
  · left
    obtain ⟨hcomm, -, hdiag, -⟩ := hswap hKt
    exact ⟨Kc, hKc, hDKK, .inr ⟨hKt, hcomm,
      center_eq_bot_and_nonempty_mulEquiv_of_swap hO hs hKc hKt hcomm hdiag hDs hsyl⟩⟩

end Small

theorem NeighbourOvergroupSLm.field_or_small {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ} (hm : 3 ≤ m)
    (hdet : SLmEvenTypeDetAt m) (hDm : LieModel (D ⧸ center D) .PSL m 2 f)
    (h : NeighbourOvergroupSLm s D m f) :
    (NeighbourOvergroupSLmField s D m f ∧ center D = ⊥) ∨ NeighbourOvergroupSLmSmall s D m f := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩ := h
  · rcases hov.2.2 with hlie | hsmall
    · left
      have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hov.2.1
      have hmodel : LieModel Kc .PSL m 2 (2 * f) := LieType.CurtisTits.lieModel_of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hlie
      have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
      have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
      have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
        (isComponentOf_iff_isComponent_subgroupOf hDs).1
          ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
      have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
      obtain ⟨hD'c, hD'm, -⟩ :=
        isComponent_fixedSubgroup_of_le_of_quotient hsN hDK.le hDs hDcomp hDm
      have hτ2 : orderOf (Kc.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        refine orderOf_eq_prime (F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2) fun h1 => ?_
        apply hov.1
        rw [h1]
        exact one_mem _
      have hall := forall_isPComponent_lieModel_of_not_inner hm hdet hmodel hτ2 hov.1 hD'c hD'm
      have hD'Z : center ((D.subgroupOf Kc).subgroupOf
          (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩))) = ⊥ :=
        F4Pilot.center_eq_bot_of_isQuasisimple hD'c.1
          (isSimpleGroup_of_lieModel_PSL (hall _ (isPComponent_two_of_isComponent hD'c)))
      have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
        rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
        intro x hx
        exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
      refine ⟨⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, hsN, hov.1, hZ, hmodel, hall⟩⟩, ?_⟩
      rw [← map_center_eq (F4Pilot.subgroupOfSubgroupOfEquiv hDK.le hDfix), hD'Z,
        Subgroup.map_bot]
    · have hZ := E6Pilot.center_eq_bot_of_isComponent_of_odd hO hKc hov.2.1
      have hsC : s ∉ centralizer (Kc : Set Y) := by
        intro h
        apply hov.1
        have h1 : (⟨s, hsN⟩ : normalizer (Kc : Set Y)) ∈ Kc.normalizerMonoidHom.ker := by
          rw [Subgroup.normalizerMonoidHom_ker]
          exact h
        exact ⟨1, by rw [map_one, MonoidHom.mem_ker.mp h1]⟩
      exact .inr ⟨Kc, hKc, hDK, hKt, hsC, hZ, hsmall⟩
  · refine .inl ⟨⟨Kc, hKc, hDKK, .inr ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩, ?_⟩
    rw [← map_center_eq φ, hZ, Subgroup.map_bot]

theorem neighbour_overgroup_slm_center_or_inner {m f : ℕ} (hm : 3 ≤ m)
    (hcat : SLmCatalogueClausesAt m) {G : Type} [Group G] [Finite G]
    (hKP : CFSG.Assembly.KProper Catalog G) {X : Subgroup G}
    (hXG : centralizer (X : Set G) ≠ ⊤) {t : G} (htX : t ∈ centralizer (X : Set G))
    (ht : orderOf t = 2) {D : Subgroup G} (hDX : D ≤ centralizer (X : Set G))
    (hDq : CFSG.IsQuasisimple D) (hDm : LieModel (D ⧸ center D) .PSL m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f ∨
      NeighbourOvergroupSLmInner (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) :=
    fun Kc hKc => F4Pilot.catalog_center_quotient_of_kProper hKP hXG hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact neighbour_overgroup_slm_center_or_inner_of_pPrimeCore_eq_bot hm hcat
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn
    (lieModel_quotient_center_map_oddCore hDX hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2))

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_hyps_linear_two (hset : SeitzSetting G L) {n : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    centralizer (X : Set G) ≠ ⊤ ∧ D ≤ centralizer (X : Set G) ∧ CFSG.IsQuasisimple D ∧
      LieModel (D ⧸ center D) .PSL (n - 2) 2 1 ∧
      CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      (∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsPGroup 2 U →
        U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
        Nat.card U ≤ 2) ∧
      CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) ∧
      ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  obtain ⟨-, -, -, hXc, -, hDC, -, ⟨φ⟩, -, -⟩ :=
    neighbour_data_torusQ1 e hn hab htC hX₀ hX₀c hX hDe
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_torusQ1_of_seitzSetting hset hK1 e hn htC ht hab hX₀ hX₀c hX htX hDe
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  have hDq : CFSG.IsQuasisimple D :=
    hDe ▸ isQuasisimple_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  have hXne : X ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, hK] at hXc
    omega
  exact ⟨centralizer_ne_top_of_ne_bot_of_isSimpleGroup hset.standardSetting.simple
      hset.standardSetting.nonab hXne, hDC.trans inf_le_left, hDq,
    lieModel_quotient_center_of_mulEquiv_specialLinear hK1 (by omega) φ, hcomp, hsyl, hstd,
    not_normal_neighbour_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX hDe⟩

theorem neighbour_overgroup_linear_two_or_inner (hset : SeitzSetting G L) {n : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) {K : Type} [Field K] (hK : Nat.card K = 2)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) 1 ∨
      NeighbourOvergroupSLmInner (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) 1 := by
  obtain ⟨hXG, hDX, hDq, hDm, hcomp, hsyl, hstd, hnn⟩ :=
    neighbour_hyps_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX htX hDe
  exact neighbour_overgroup_slm_center_or_inner (by omega) hcat hset.standardSetting.kProper hXG
    htX ht hDX hDq hDm hcomp hsyl hstd hnn

theorem NeighbourOvergroupSLm.field_or_small_oddCore {X : Subgroup G} {t : G}
    (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.IsQuasisimple D) {m f : ℕ} (hm : 3 ≤ m)
    (hdet : SLmEvenTypeDetAt m) (hDm : LieModel (D ⧸ center D) .PSL m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (h : NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f) :
    (NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥) ∨
      NeighbourOvergroupSLmSmall (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f := by
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact h.field_or_small (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _)
    (orderOf_mk_oddCore ht') hcomp hm hdet
    (lieModel_quotient_center_map_oddCore hDX hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2))

theorem neighbour_overgroup_linear_two_field_or_small (hset : SeitzSetting G L) {n : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) (hdet : SLmEvenTypeDetAt (n - 2)) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    (NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) 1 ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥) ∨
      NeighbourOvergroupSLmSmall (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) 1 := by
  obtain ⟨-, hDX, hDq, hDm, hcomp, -, -, -⟩ :=
    neighbour_hyps_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX htX hDe
  rcases neighbour_overgroup_linear_two_or_inner hset hcat hK e hn htC ht hab hX₀ hX₀c hX htX
      hDe with h | h
  · exact h.field_or_small_oddCore htX ht hDX hDq (by omega) hdet hDm hcomp
  · exact .inr h.small

theorem neighbour_overgroup_linear_two_field (hset : SeitzSetting G L) {n : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) (hdet : SLmEvenTypeDetAt (n - 2)) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K) (hn : 7 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) 1 ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  rcases neighbour_overgroup_linear_two_field_or_small hset hcat hdet hK e (by omega) htC ht hab
      hX₀ hX₀c hX htX hDe with h | h
  · exact h
  · exact absurd h (not_neighbourOvergroupSLmSmall (Or.inl (by omega)))

end Seitz

end CFSG.SeitzReduction.LinearPilot
