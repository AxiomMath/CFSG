module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.NoSL29Reduction
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.LieModelOrders
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.J2

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

theorem center_eq_bot_of_isSimpleGroup_of_not_prime_card {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : center G = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G)).resolve_right fun ht =>
    h ((@Group.is_simple_iff_prime_card G _ (Subgroup.center_eq_top_iff.1 ht)).1 inferInstance)

theorem center_eq_bot_of_mulEquiv_of_not_prime_card {N S : Type*} [Group N] [Group S]
    [IsSimpleGroup S] (e : N ≃* S) (h : ¬ (Nat.card S).Prime) : center N = ⊥ := by
  haveI : IsSimpleGroup N := e.isSimpleGroup
  exact center_eq_bot_of_isSimpleGroup_of_not_prime_card (by
    rw [Nat.card_congr e.toEquiv]
    exact h)

theorem center_eq_bot_of_lieModel {N : Type} [Group N] {t : CFSG.Open.StatedLieTag} {n p f : ℕ}
    (ht : t ∈ classicalTags) (hn : n ≠ 0) (h : LieModel N t n p f)
    (hp : ¬ (CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (p ^ f)).Prime) : center N = ⊥ := by
  haveI : IsSimpleGroup N := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h
  exact center_eq_bot_of_isSimpleGroup_of_not_prime_card (by
    rw [CFSG.Blueprint.LieModel.card_eq_lieOrd hn h]
    exact hp)

theorem center_eq_bot_of_lieModel_psu_three_five {N : Type} [Group N]
    (h : LieModel N .PSU 3 5 1) : center N = ⊥ := by
  refine center_eq_bot_of_lieModel (t := .PSU) (n := 3) (p := 5) (f := 1)
    (by decide) (by norm_num) h ?_
  have hord : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSU 3 (5 ^ 1) = 126000 := by
    decide +kernel
  rw [hord]
  norm_num

theorem center_eq_bot_of_lieModel_psl_three_seven {N : Type} [Group N]
    (h : LieModel N .PSL 3 7 1) : center N = ⊥ := by
  refine center_eq_bot_of_lieModel (t := .PSL) (n := 3) (p := 7) (f := 1)
    (by decide) (by norm_num) h ?_
  have hord : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 3 (7 ^ 1) = 1876896 := by
    decide +kernel
  rw [hord]
  norm_num

theorem center_eq_bot_of_lieModel_psl_five_two {N : Type} [Group N]
    (h : LieModel N .PSL 5 2 1) : center N = ⊥ := by
  refine center_eq_bot_of_lieModel (t := .PSL) (n := 5) (p := 2) (f := 1)
    (by decide) (by norm_num) h ?_
  have hord : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 5 (2 ^ 1) = 9999360 := by
    decide +kernel
  rw [hord]
  norm_num

theorem center_eq_bot_of_lieModel_psp_two_two_two {N : Type} [Group N]
    (h : LieModel N .PSp 2 2 2) : center N = ⊥ := by
  refine center_eq_bot_of_lieModel (t := .PSp) (n := 2) (p := 2) (f := 2)
    (by decide) (by norm_num) h ?_
  have hord : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSp 2 (2 ^ 2) = 979200 := by
    decide +kernel
  rw [hord]
  norm_num

theorem center_eq_bot_of_isSporadic {N : Type} [Group N] {s : TauCeti.SporadicName}
    (hsimple : IsSimpleGroup (Carrier s)) (hcard : ¬ (Nat.card (Carrier s)).Prime)
    (h : IsSporadic N s) : center N = ⊥ := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (Carrier s) := hsimple
  exact center_eq_bot_of_mulEquiv_of_not_prime_card e hcard

theorem center_eq_bot_of_isSporadic_m22 {N : Type} [Group N]
    (h : IsSporadic N .M22) : center N = ⊥ := by
  refine center_eq_bot_of_isSporadic (s := .M22)
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2) ?_ h
  show ¬ (Nat.card NativeSporadic.M22).Prime
  rw [CFSG.Sporadic.Mathieu.card_M22]
  norm_num

theorem center_eq_bot_of_isSporadic_m23
    {N : Type} [Group N]
    (h : IsSporadic N .M23) : center N = ⊥ := by
  refine center_eq_bot_of_isSporadic (s := .M23)
    (CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2) ?_ h
  have hcard : Nat.card NativeSporadic.M23 = 10200960 := by
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq]
    exact (Nat.card_eq_fintype_card (α := CFSG.M23.M23Group.H0)).trans
      CFSG.M23.M23Group.card_M23
  show ¬ (Nat.card NativeSporadic.M23).Prime
  rw [hcard]
  norm_num

theorem center_eq_bot_of_isSporadic_m24 {N : Type} [Group N]
    (h : IsSporadic N .M24) : center N = ⊥ := by
  refine center_eq_bot_of_isSporadic (s := .M24)
    (CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2) ?_ h
  show ¬ (Nat.card NativeSporadic.M24).Prime
  rw [CFSG.Sporadic.Mathieu.card_M24]
  norm_num

theorem center_eq_bot_of_isSporadic_hs {N : Type} [Group N]
    (h : IsSporadic N .HS) : center N = ⊥ := by
  refine center_eq_bot_of_isSporadic (s := .HS)
    CFSG.Sporadic.HS.isSimpleGroup_HS ?_ h
  show ¬ (Nat.card NativeSporadic.HS).Prime
  rw [CFSG.Sporadic.HS.card_HS]
  norm_num

theorem center_eq_bot_of_isSporadic_ru {N : Type} [Group N]
    (h : IsSporadic N .Ru) : center N = ⊥ := by
  refine center_eq_bot_of_isSporadic (s := .Ru)
    CFSG.Sporadic.Ru.isSimpleGroup_Ru ?_ h
  show ¬ (Nat.card NativeSporadic.Ru).Prime
  rw [CFSG.Sporadic.Ru.card_Ru]
  norm_num

theorem center_eq_bot_of_isSporadic_j2 {N : Type} [Group N]
    (h : IsSporadic N .J2) : center N = ⊥ := by
  refine center_eq_bot_of_isSporadic (s := .J2)
    CFSG.Sporadic.J2.isSimpleGroup_J2 ?_ h
  show ¬ (Nat.card NativeSporadic.J2).Prime
  rw [CFSG.Sporadic.J2.card_J2]
  norm_num

theorem onanCenterFree_holds :
    ONanCenterFree := by
  intro N _ _ h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact center_eq_bot_of_lieModel_psu_three_five h
  · exact center_eq_bot_of_lieModel_psl_three_seven h
  · exact center_eq_bot_of_isSporadic_m22 h
  · exact center_eq_bot_of_isSporadic_m23 h
  · exact center_eq_bot_of_isSporadic_m24 h
  · exact center_eq_bot_of_isSporadic_hs h
  · exact center_eq_bot_of_isSporadic_ru h
  · exact center_eq_bot_of_lieModel_psl_five_two h
  · exact center_eq_bot_of_isSporadic_j2 h
  · exact center_eq_bot_of_lieModel_psp_two_two_two h

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan
