module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.OutSmallBasic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

theorem card_mulAut_le_of_lieModel_psu_three_five {N : Type} [Group N] [Finite N]
    (h : LieModel N .PSU 3 5 1) : Nat.card (MulAut N) ≤ 6 * Nat.card N := by
  have hM := LieModel.statedClassicalModel_of_ne_zero (n := 3) (by norm_num) h
  have hout : Nat.card (Outer N) ≤ 6 := by
    have hb :=
      (CFSG.LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound N 3 5 1 hM).2.2.1
    have hbnd : 2 * 1 * Nat.gcd 3 (5 ^ 1 + 1) = 6 := by norm_num
    rw [hbnd] at hb
    exact le_of_eq hb
  exact card_mulAut_le_of_card_outer_le hout

theorem card_mulAut_le_of_lieModel_psl_three_seven {N : Type} [Group N] [Finite N]
    (h : LieModel N .PSL 3 7 1) : Nat.card (MulAut N) ≤ 6 * Nat.card N := by
  have hM := LieModel.statedClassicalModel_of_ne_zero (n := 3) (by norm_num) h
  have hout : Nat.card (Outer N) ≤ 6 := by
    have hd :=
      (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound N 3 7 1 hM).2.2.2.2
        (by norm_num : 3 ≤ 3)
    have hbnd : 2 * 1 * Nat.gcd 3 (7 ^ 1 - 1) = 6 := by norm_num
    rw [hbnd] at hd
    exact Nat.le_of_dvd (by norm_num) hd
  exact card_mulAut_le_of_card_outer_le hout

theorem card_mulAut_le_of_lieModel_psl_five_two {N : Type} [Group N] [Finite N]
    (h : LieModel N .PSL 5 2 1) : Nat.card (MulAut N) ≤ 2 * Nat.card N := by
  have hM := LieModel.statedClassicalModel_of_ne_zero (n := 5) (by norm_num) h
  have hout : Nat.card (Outer N) ≤ 2 := by
    have hd :=
      (CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound N 5 2 1 hM).2.2.2.2
        (by norm_num : 3 ≤ 5)
    have hbnd : 2 * 1 * Nat.gcd 5 (2 ^ 1 - 1) = 2 := by norm_num
    rw [hbnd] at hd
    exact Nat.le_of_dvd (by norm_num) hd
  exact card_mulAut_le_of_card_outer_le hout

theorem card_mulAut_le_of_lieModel_psp_two_two_two {N : Type} [Group N] [Finite N]
    (h : LieModel N .PSp 2 2 2) : Nat.card (MulAut N) ≤ 4 * Nat.card N := by
  have hM := LieModel.statedClassicalModel_of_ne_zero (n := 2) (by norm_num) h
  obtain ⟨⟨-, hm1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨Fr, hFr, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hm1 hK
  have houtK :=
    (CFSG.ComponentClassification.UnbalancedCatalog.SpChain.exceptionalAut_structure
      (f := 2) hm1 hFr hord hzp).2.2.2.2.2.1
  have hout : Nat.card (Outer N) ≤ 4 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv,
      houtK]
  exact card_mulAut_le_of_card_outer_le hout

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
