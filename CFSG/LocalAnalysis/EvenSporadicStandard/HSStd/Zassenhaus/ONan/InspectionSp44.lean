module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionArms
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.InspectionCommon
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallLie
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.CenterFree
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Sp44NoEight

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem isCyclic_outer_of_lieModel_psp_two_two_two {N : Type} [Group N]
    (hN : LieModel N .PSp 2 2 2) : IsCyclic (Outer N) := by
  have hM := LieModel.statedClassicalModel_of_ne_zero (n := 2) (by norm_num) hN
  obtain ⟨⟨-, hm1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm1 hK
  have houtK :=
    (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (f := 2) hm1 hFr hord hzp).2.2.2.2.1
  exact (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).isCyclic.mpr houtK

theorem exists_subgroup_card_nine_of_card_eq_360 {N : Type} [Group N] [Finite N]
    (H : Subgroup N) (hH : Nat.card H = 360) : ∃ P : Subgroup N, P ≤ H ∧ Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨P', hP'⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := H) 3 (n := 2) (by rw [hH]; norm_num)
  exact ⟨P'.map H.subtype, Subgroup.map_subtype_le P', by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP']; norm_num⟩

theorem false_of_card_eq_360_le_centralizer_psp_two_two_two {N : Type} [Group N] [Finite N]
    (hN : LieModel N .PSp 2 2 2) {z : N} (hz : orderOf z = 2) {A : Subgroup N}
    (hAz : A ≤ centralizer ({z} : Set N)) (hcard : Nat.card A = 360) : False := by
  obtain ⟨P, hPA, hP⟩ := exists_subgroup_card_nine_of_card_eq_360 A hcard
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz
    norm_num at hz
  refine CFSG.EvenSporadicStandard.M22Std.P21H.no_involution_centralizes_nine_sp44
    hN z hzz hz1 P hP ?_
  intro x hx
  have hxA : x ∈ A := hPA hx
  have hxc : x ∈ centralizer ({z} : Set N) := hAz hxA
  exact (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm

theorem false_of_outer_involution_psp_two_two_two {Y : Type} [Group Y] [Finite Y]
    {N : Subgroup Y} [N.Normal] (hN : LieModel N .PSp 2 2 2) (hC : centralizer (N : Set Y) ≤ N)
    {w h : Y} (hw : orderOf w = 2) (hwN : w ∉ N) (hh : orderOf h = 8) (hwh : w * h = h * w)
    (hh2 : h ^ 2 ∈ N) : False := by
  have hcyc : IsCyclic (Y ⧸ N) :=
    isCyclic_quotient_of_isCyclic_outer hC (isCyclic_outer_of_lieModel_psp_two_two_two hN)
  obtain ⟨x, hxN, hx⟩ := exists_mem_orderOf_eq_eight hcyc hw hwN hh hwh hh2
  have hx8 : orderOf (⟨x, hxN⟩ : ↥N) = 8 := by rw [Subgroup.orderOf_mk, hx]
  exact orderOf_ne_eight_of_lieModel_psp_two_two_two hN (⟨x, hxN⟩ : ↥N) hx8

theorem inspectionArm_psp_two_two_two : InspectionArm fun N _ => LieModel N .PSp 2 2 2 := by
  intro Y _ _ N hN hC hQ P _ _ _ _ hw
  haveI := hN
  exfalso
  have hZ : center ↥N = ⊥ := center_eq_bot_of_lieModel_psp_two_two_two hQ
  have hidx : N.index ≤ 4 :=
    index_le_of_card_mulAut_le hC hZ (card_mulAut_le_of_lieModel_psp_two_two_two hQ)
  obtain ⟨w, hw2, H, A, hH, hwH, ⟨h, hhH, hh8⟩, _, hAH, hAN, hA, _, _, hsq⟩ :=
    exists_simple_le_of_pgl29 (N := N) (by omega) hw
  have hAw : A ≤ centralizer ({w} : Set Y) := hAH.trans hH
  by_cases hwN : w ∈ N
  · refine false_of_card_eq_360_le_centralizer_psp_two_two_two hQ
      (z := ⟨w, hwN⟩) (A := A.subgroupOf N) ?_ ?_ ?_
    · rw [Subgroup.orderOf_mk, hw2]
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hxw : (x : Y) ∈ centralizer ({w} : Set Y) := hAw hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hxw
      simpa using hxw
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, hA]
  · have hwh : w * h = h * w := (Subgroup.mem_centralizer_singleton_iff.1 (hH hhH)).symm
    have hh2 : h ^ 2 ∈ N := hAN (hsq h hhH)
    exact false_of_outer_involution_psp_two_two_two hQ hC hw2 hwN hh8 hwh hh2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
