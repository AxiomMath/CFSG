module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S3Catalog
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvL2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvM12
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HOvSeven

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Open

theorem eq_bot_of_normal_odd_of_fusionZStar {D : Type} [Group D] (hZ : fusionZStar D = ⊥)
    (N : Subgroup D) (hN : N.Normal) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have h1 : N ≤ fusionOddCore D :=
    le_sSup (show N ∈ {N : Subgroup D | N.Normal ∧ Odd (Nat.card N)} from ⟨hN, hodd⟩)
  have h2 : fusionOddCore D ≤ fusionZStar D := by
    intro x hx
    show QuotientGroup.mk' (fusionOddCore D) x ∈ Subgroup.center (D ⧸ fusionOddCore D)
    rw [show QuotientGroup.mk' (fusionOddCore D) x = 1 from (QuotientGroup.eq_one_iff x).2 hx]
    exact one_mem _
  exact le_bot_iff.1 (h1.trans (h2.trans hZ.le))

theorem haradaOvergroups_proved :
    HaradaOvergroups := by
  intro D _ _ hZ t ht e hcase
  have hZ' : ∀ N : Subgroup D, N.Normal → Odd (Nat.card N) → N = ⊥ := fun N hN hodd =>
    eq_bot_of_normal_odd_of_fusionZStar hZ N hN hodd
  rcases hcase with hL | hL | hL | h7 | hM
  · exact HOv.not_exists_elemAbelian_sixteen_of_psl_two_twentyfive hZ' ht e hL
  · exact HOv.not_exists_elemAbelian_sixteen_of_psl_three_five hZ' ht e hL
  · exact HOv.not_exists_elemAbelian_sixteen_of_psu_three_five hZ' ht e hL
  · obtain ⟨e7⟩ := h7
    rintro ⟨A, hA, hc⟩
    exact HOv.not_exists_sq_eq_one_sixteen_of_mulEquiv_perm_seven e7
      ⟨A, fun x hx => hA.2 x hx, hc⟩
  · exact HOv.not_exists_elemAbelian_sixteen_of_m12 hM

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
