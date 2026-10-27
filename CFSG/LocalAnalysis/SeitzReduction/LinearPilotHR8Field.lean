module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotHR8RootTorus
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSL
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem forall_isPComponent_lieModel_of_not_inner {m : ℕ} (hm : 3 ≤ m)
    (hdet : SLmEvenTypeDetAt m) {S : Type} [Group S] [Finite S] {f : ℕ}
    (hS : LieModel S .PSL m 2 (2 * f)) {σ : MulAut S} (hσ : orderOf σ = 2)
    (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) .PSL m 2 f) :
    ∀ P : Subgroup (fixedSubgroup σ), IsPComponent 2 P → LieModel P .PSL m 2 f := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL m 2 (2 * f) :=
    (ComponentClassification.CatLeaf.statedClassicalModel_of_lieModel_psl hS).1
  have hDp : IsPComponent 2 D := isPComponent_two_of_isComponent hD
  rcases psl_outer_fixed_exact hadm hS σ hσ hout with
    h | h | ⟨k, _, _, r, hk, hr, ⟨Φ⟩⟩ | h
  · intro P hP
    obtain ⟨-, hmP, -⟩ := h P hP
    rwa [Nat.mul_div_cancel_left f (by norm_num : 0 < 2)] at hmP
  · obtain ⟨hadm', hmD⟩ := h D hDp
    obtain ⟨htt, -, -⟩ := typeDet_of_simple hdet hD.1 (isSimpleGroup_of_lieModel_PSU hmD) hDm
      hadm' hmD
    exact absurd htt (by decide)
  · exact (no_component_statedSp hdet hk hr Φ hD hm hDm).elim
  · exact (h D hDp).elim

@[expose] def NeighbourOvergroupSLmField {Y : Type} [Group Y] (s : Y) (D : Subgroup Y)
    (m f : ℕ) : Prop :=
  ∃ Kc : Subgroup Y, IsComponent Kc ∧ D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
          center Kc = ⊥ ∧ LieModel Kc .PSL m 2 (2 * f) ∧
          ∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)), IsPComponent 2 P →
            LieModel P .PSL m 2 f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)))

theorem NeighbourOvergroupSLm.field {Y : Type} [Group Y] [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ} (hm : 3 ≤ m)
    (hmf : 5 ≤ m ∨ 2 ≤ f) (hdet : SLmEvenTypeDetAt m)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f) (h : NeighbourOvergroupSLm s D m f) :
    NeighbourOvergroupSLmField s D m f ∧ center D = ⊥ := by
  obtain ⟨Kc, hKc, hDKK, ⟨hKt, hDK, hsK, hsN, hov⟩ | ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩ := h
  · obtain ⟨hZ, hmodel⟩ := E6Pilot.lieModel_of_slmOvergroup_of_pPrimeCore_eq_bot hO hKc hov hmf
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
  · refine ⟨⟨Kc, hKc, hDKK, .inr ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩, ?_⟩
    rw [← map_center_eq φ, hZ, Subgroup.map_bot]

theorem NeighbourOvergroupSLm.field_oddCore {G : Type} [Group G] [Finite G] {X : Subgroup G}
    {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.IsQuasisimple D) {m f : ℕ} (hm : 3 ≤ m)
    (hmf : 5 ≤ m ∨ 2 ≤ f) (hdet : SLmEvenTypeDetAt m)
    (hDm : LieModel (D ⧸ center D) .PSL m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (h : NeighbourOvergroupSLm (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
      ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) m f ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  exact h.field (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) (orderOf_mk_oddCore ht') hcomp
    hm hmf hdet
    (lieModel_quotient_center_map_oddCore hDX hDq hDm (ne_bot_of_isQuasisimple hcomp.2.2))

section Seitz

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem neighbour_overgroup_rootTorus_field (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : SLmCatalogueClausesAt (n - 2)) (hdet : SLmEvenTypeDetAt (n - 2)) {K : Type}
    [Field K] (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n}
    (hab : a ≠ b) {X : Subgroup G}
    (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {g y : G} (hyD : y ∈ D) (hy : orderOf y = 2) (hg : g⁻¹ * t * g = t * y) :
    NeighbourOvergroupSLmField (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) (n - 2) f ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥ := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hq : 4 ≤ Nat.card K := (four_le_card_iff_two_le hKc).2 hf
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨hcomp, -, -⟩ :=
    neighbour_standard_rootTorus_of_seitzSetting hset hKc hf e hn htC ht hab hX htX hDe
  obtain ⟨-, -, -, -, -, -, hDC, -, ⟨φ⟩, -, -⟩ :=
    neighbour_data_rootTorus e hn hq hab htC hX hDe
  have hDq : CFSG.IsQuasisimple D :=
    hDe ▸ isQuasisimple_map_blockSL e (by omega) (by omega) (Or.inl (by omega))
  exact (neighbour_overgroup_rootTorus hset hcat hKc hf e hn htC ht hab hX htX hDe hyD hy
    hg).field_oddCore htX ht (hDC.trans inf_le_left) hDq (by omega) (Or.inr hf) hdet
    (lieModel_quotient_center_of_mulEquiv_specialLinear hKc (by omega) φ) hcomp

end Seitz

end CFSG.SeitzReduction.LinearPilot
