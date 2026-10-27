module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneComponent
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.ProperTwoGeneratedCore.Assembly

open CFSG.Open CFSG.ShultStronglyClosedTI

section General

variable {X : Type} [Group X] [Finite X]

theorem exists_orderOf_eq_two_of_isPGroup {P : Subgroup X} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ w ∈ P, orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hn
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)
  exact ⟨w, w.2, by rw [Subgroup.orderOf_coe, hw]⟩

theorem mem_of_normal_of_forall_component_mem (hodd : pPrimeCore 2 X = ⊥) {t : X}
    (htc : t ∈ Subgroup.center X) (ht : orderOf t = 2) (htO : t ∈ CFSG.pCore 2 X)
    (hrank : CFSG.Open.pRank 2 (CFSG.pCore 2 X) = 1)
    (hcomp : ∀ J : Subgroup X, CFSG.IsComponent J → t ∈ J) {L : Subgroup X} [hL : L.Normal]
    (hne : L ≠ ⊥) : t ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra htL
  have hLodd : pPrimeCore 2 L = ⊥ := by
    have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hL.isSubnormal
    rwa [hodd, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at h
  have hLtwo : CFSG.pCore 2 L = ⊥ := by
    set P := (CFSG.pCore 2 L).map L.subtype with hP
    have hPn : P.Normal := ⟨fun p hp g => CFSG.Walter.conj_mem_map_of_characteristic
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hL]; exact Subgroup.mem_top g) hp⟩
    have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup.map L.subtype
    have hPO : P ≤ CFSG.pCore 2 X := le_sSup ⟨hPn, hP2⟩
    by_contra hne'
    have hPne : P ≠ ⊥ := by
      rw [hP, Ne, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
      exact hne'
    obtain ⟨w, hwP, hw⟩ := exists_orderOf_eq_two_of_isPGroup hP2 hPne
    have hwt := eq_of_mem_twoCore_of_rank_one htc ht htO hrank (hPO hwP) hw
    exact htL (hwt ▸ Subgroup.map_subtype_le _ hwP)
  have hLlayer : CFSG.layer L = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun K hK => ?_)
    have hKX : CFSG.IsComponent (K.map L.subtype) := (CFSG.isComponent_iff_open _).mpr
      (CFSG.ComponentClassification.LocalComponents.of_subnormal_subgroup L
        (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hL.isSubnormal) K
        ((CFSG.isComponent_iff_open K).mp hK))
    exact absurd (Subgroup.map_subtype_le K (hcomp _ hKX)) htL
  have hGF : CFSG.generalizedFitting L = ⊥ := by
    rw [CFSG.generalizedFitting, CFSG.Fitting_eq_pcore L 2 hLodd, hLtwo, hLlayer, sup_bot_eq]
  apply hne
  rw [eq_bot_iff]
  intro l hl
  have hmem : (⟨l, hl⟩ : L) ∈ CFSG.generalizedFitting L := by
    refine CFSG.centralizer_generalizedFitting_le L ?_
    rw [hGF, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
    rw [hh, one_mul, mul_one]
  rw [hGF, Subgroup.mem_bot] at hmem
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)

end General

variable {G : Type} [Group G] [Finite G]

end CFSG.ProperTwoGeneratedCore.Assembly
