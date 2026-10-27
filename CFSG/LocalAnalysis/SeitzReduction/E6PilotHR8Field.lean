module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR8Instances
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetSix
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (SLmEvenTypeDetAt SLmCatalogueClausesAt)

theorem forall_isPComponent_lieModel_of_not_inner {m : ℕ} (hm : 3 ≤ m)
    (hdet : SLmEvenTypeDetAt m) {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : LieModel S .PSL m 2 (2 * f)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSL m 2 f) :
    ∀ P : Subgroup (fixedSubgroup σ), IsPComponent 2 P → LieModel P .PSL m 2 f := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL m 2 (2 * f) :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hS).1
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases LinearPilot.psl_outer_fixed_exact hadm hS σ hσ hout with
    h | h | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · intro P hP
    obtain ⟨-, hmP, -⟩ := h P hP
    rwa [Nat.mul_div_cancel_left f (by norm_num : 0 < 2)] at hmP
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := LinearPilot.typeDet_of_simple hdet hD.1
      (LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) hDm hadm' hmD
    exact absurd htt (by decide)
  · exact (LinearPilot.no_component_statedSp hdet hk hr Φ hD hm hDm).elim
  · exact (h D hDp).elim

@[expose] def NeighbourOvergroupSLField {Y : Type} [Group Y] (s : Y) (D : Subgroup Y) (m f : ℕ) :
    Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f) ∧
          ∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)), IsPComponent 2 P →
            LieModel P .PSL m 2 f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ Nonempty (Kc ⧸ center Kc ≃* D)))

theorem NeighbourOvergroupSL.field {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ} (hm : 3 ≤ m)
    (hmf : 5 ≤ m ∨ 2 ≤ f) (hdet : SLmEvenTypeDetAt m) (hDm : LieModel D .PSL m 2 f)
    (h : NeighbourOvergroupSL s D m f) : NeighbourOvergroupSLField s D m f := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | hswap⟩ := h
  · obtain ⟨hZ, hmodel⟩ := lieModel_of_slmOvergroup_of_pPrimeCore_eq_bot hO hKc hov hmf
    have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
    have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
      (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    obtain ⟨hD'c, hD'm, -⟩ := isComponent_fixedSubgroup_of_le hsN hDK.le hDs hDcomp hDm
    have hτ2 : orderOf (Kc.normalizerMonoidHom ⟨s, hsN⟩) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime (F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN hs2) fun h1 => ?_
      apply hov.1
      rw [h1]
      exact one_mem _
    exact ⟨Kc, hKc, hDKK, .inl ⟨hKt, hDK, hsK, hsN, hov.1, hZ, hmodel,
      forall_isPComponent_lieModel_of_not_inner hm hdet hmodel hτ2 hov.1 hD'c hD'm⟩⟩
  · exact ⟨Kc, hKc, hDKK, .inr hswap⟩

theorem NeighbourOvergroupSL.field_oddCore {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) {m f : ℕ} (hm : 3 ≤ m) (hmf : 5 ≤ m ∨ 2 ≤ f)
    (hdet : SLmEvenTypeDetAt m) (hDm : LieModel D .PSL m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (h : NeighbourOvergroupSL (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f) :
    NeighbourOvergroupSLField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f := by
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact h.field (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (orderOf_mk_oddCore ht') hcomp
    hm hmf hdet (lieModel_PSL_map_oddCore hDX hDm (ne_bot_of_isQuasisimple hcomp.2.2))

section E6

open CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem neighbour_overgroup_E6_nonsplit_field_of_not_normal (hcat : SLmCatalogueClausesAt 6)
    {G : Type} [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {A : Subgroup (adjointGroup .E6 K)} (hAJ : A ≤ posJ K) (hA : Nat.card A = Nat.card K + 1)
    (hcyc : IsCyclic A) {X : Subgroup G} (hX : X = (A.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    NeighbourOvergroupSLField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf := F4Pilot.one_le_of_natCard_eq_two_pow hK
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hcomp := (neighbour_standard_E6_nonsplit_of_one_le hset.standard htK.1 ht hKt hf hK e hAJ
    hA hcyc hX htX hDe).1
  have hXJ : X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rw [hX]
    exact map_mono (map_mono hAJ)
  exact (neighbour_overgroup_E6_nonsplit_of_not_normal hcat hset hK e ht hKt hAJ hA hcyc hX htX
    hDe hnn).field_oddCore htX ht (hDe ▸ map_a5Levi_le_centralizer e hXJ) (by norm_num)
    (Or.inl (by norm_num)) LinearPilot.slmEvenTypeDetAt_six (hDe ▸ lieModel_map_map_a5Levi hK e)
    hcomp

theorem neighbour_overgroup_E6_torus_field (hcat : SLmCatalogueClausesAt 6) {G : Type}
    [Group G] [Finite G] {L : Subgroup G} (hset : StandardSetting G L) {f : ℕ} (hf : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (e : L ≃* adjointGroup .E6 K) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hF5 : FactF5E6 K) {X : Subgroup G}
    (hX : (∃ A : Subgroup (adjointGroup .E6 K), A ≤ posJ K ∧ IsCyclic A ∧
        Nat.card A = Nat.card K + 1 ∧ X = (A.map e.symm.toMonoidHom).map L.subtype) ∨
      X = (((EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K)).map
        e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G))
    {D : Subgroup G} (hDe : D = ((a5Levi K).map e.symm.toMonoidHom).map L.subtype) :
    NeighbourOvergroupSLField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) 6 f := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hK
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hK
  have hf1 : 1 ≤ f := by omega
  have hq : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hTJ : (EPilot.highTorusLine .E6 K).subgroupOf (adjointGroup .E6 K) ≤ posJ K :=
    fun _ hx => mem_subgroupOf.2
      (EPilot.highTorusLine_le_highRootSL2 (Or.inl rfl) (mem_subgroupOf.1 hx))
  obtain ⟨hcomp, hXJ⟩ : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))) ∧
      X ≤ ((posJ K).map e.symm.toMonoidHom).map L.subtype := by
    rcases hX with ⟨A, hAJ, hcyc, hA, hX⟩ | hX
    · refine ⟨(neighbour_standard_E6_nonsplit_of_one_le hset.standard htK.1 ht hKt hf1 hK e hAJ
        hA hcyc hX htX hDe).1, ?_⟩
      rw [hX]
      exact map_mono (map_mono hAJ)
    · have hTodd : Odd (Nat.card ((EPilot.highTorusLine .E6 K).subgroupOf
          (adjointGroup .E6 K))) := by
        rw [Nat.card_congr
          (subgroupOfEquivOfLe (highTorusLine_le_adjointGroup (Or.inl rfl))).toEquiv]
        exact odd_card_highTorusLine hf1 hK
      refine ⟨(neighbour_standard_E6_of_centralizer_eq_sup hset.standard htK.1 ht hKt hf hK e
        (centralizer_highTorusLine_eq (Or.inl rfl) hq)
        highTorusLine_subgroupOf_le_centralizer_perpLevi
        highTorusLine_subgroupOf_le_centralizer_self hTodd hX htX hDe).1, ?_⟩
      rw [hX]
      exact map_mono (map_mono hTJ)
  exact (neighbour_overgroup_E6_torus hcat hset hf hK e ht hKt hF5 hX htX hDe).field_oddCore htX
    ht (hDe ▸ map_a5Levi_le_centralizer e hXJ) (by norm_num) (Or.inl (by norm_num))
    LinearPilot.slmEvenTypeDetAt_six (hDe ▸ lieModel_map_map_a5Levi hK e) hcomp

end E6

end CFSG.SeitzReduction.E6Pilot
