module

public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporFix
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporLie
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.SporadicNoA6
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpP1SporChev2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ComponentClassification.GS82PumpInputs.SporSmall

open CFSG Subgroup Blueprint Assembly.LowTwoRank CatLeaf SporLie SporChev2
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_dvd_fixed {S : Type} [Group S] {σ : MulAut S} {P : Subgroup S}
    (h : ProperFixedComponent σ P) :
    Nat.card (P ⧸ Open.fusionZStar P) ∣ Nat.card (fixedSubgroup σ) :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le h.2.1)

theorem orderOf_eq_two {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {σ : MulAut S}
    {P : Subgroup S} (h : ProperFixedComponent σ P) : orderOf σ = 2 :=
  orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => h.1 y) h.ne_one


variable {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {σ : MulAut S} {P : Subgroup S}
  {τ : StatedLieTag} {n r f : ℕ}

theorem inChev2_of_dvd_1920 {X : Type} [Group X] (hr2 : r ≠ 2) (hL : LieModel X τ n r f)
    (hd : Nat.card X ∣ 1920) : GH74.GLS.InChev2 X :=
  inChev2_of_tuple_five hL (tuple_of_dvd_1920 hr2 hL hd)

theorem inChev2_of_dvd_21504 {X : Type} [Group X] (hr2 : r ≠ 2) (hL : LieModel X τ n r f)
    (hd : Nat.card X ∣ 21504) : GH74.GLS.InChev2 X :=
  inChev2_of_tuple_seven hL (tuple_of_dvd_21504 hr2 hL hd)

section M11


theorem false_of_m11 (e : S ≃* NativeSporadic.M11) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f) : False := by
  have hd := card_dvd_fixed h
  rw [CatFC.card_fixedSubgroup_m11 e (orderOf_eq_two h)] at hd
  exact false_of_dvd_48 hr2 hL hd

end M11

section M12


theorem false_of_m12 (e : S ≃* NativeSporadic.M12) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hd := card_dvd_fixed h
  rcases CatFC.card_fixedSubgroup_m12 e (orderOf_eq_two h) with hc | hc | hc <;> rw [hc] at hd
  · exact hnot (inChev2_of_dvd_1920 hr2 hL (hd.trans (by norm_num)))
  · exact false_of_dvd_192 hr2 hL hd
  · exact hnot (inChev2_of_dvd_1920 hr2 hL (hd.trans (by norm_num)))

end M12

section M22


theorem false_of_m22 (e : S ≃* NativeSporadic.M22) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hd := card_dvd_fixed h
  rcases SporFix.card_fixedSubgroup_m22 e (orderOf_eq_two h) with hc | hc | hc <;>
    rw [hc] at hd
  · exact false_of_dvd_384 hr2 hL hd
  · exact false_of_dvd_320 hr2 hL hd
  · exact hnot (inChev2_of_dvd_21504 hr2 hL (hd.trans (by norm_num)))

end M22

section M23


theorem false_of_m23 (e : S ≃* NativeSporadic.M23) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hd := card_dvd_fixed h
  rw [SporFix.card_fixedSubgroup_m23 e (orderOf_eq_two h)] at hd
  exact hnot (inChev2_of_dvd_21504 hr2 hL (hd.trans (by norm_num)))

end M23

section M24


theorem false_of_m24 (e : S ≃* NativeSporadic.M24) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hd := card_dvd_fixed h
  rcases SporFix.card_fixedSubgroup_m24 e (orderOf_eq_two h) with hc | hc <;> rw [hc] at hd
  · exact hnot (inChev2_of_dvd_21504 hr2 hL hd)
  · exact hnot (inChev2_of_tuple_five hL (tuple_of_dvd_7680 hr2 hL hd))

end M24

section J1


theorem false_of_j1 (hna : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.J1)
    (h : ProperFixedComponent σ P) (hr2 : r ≠ 2) (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hd := card_dvd_fixed h
  rw [SporFix.card_fixedSubgroup_j1 hna e h] at hd
  exact hnot (inChev2_of_dvd_1920 hr2 hL (hd.trans (by norm_num)))

end J1

section J2


theorem false_of_j2 (e : S ≃* NativeSporadic.J2) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) : False := by
  have hd := card_dvd_fixed h
  rcases SporFix.card_fixedSubgroup_j2 e (orderOf_eq_two h) with hc | hc | hc <;> rw [hc] at hd
  · exact hnot (inChev2_of_dvd_1920 hr2 hL (hd.trans (by norm_num)))
  · exact hnot (inChev2_of_dvd_21504 hr2 hL (hd.trans (by norm_num)))
  · exact hnot (inChev2_of_dvd_1920 hr2 hL hd)

end J2

section J3


theorem lieModel_of_j3 (e : S ≃* NativeSporadic.J3) (h : ProperFixedComponent σ P) (hr2 : r ≠ 2)
    (hL : LieModel (P ⧸ Open.fusionZStar P) τ n r f)
    (hnot : ¬ GH74.GLS.InChev2 (P ⧸ Open.fusionZStar P)) :
    LieModel (P ⧸ Open.fusionZStar P) .PSL 2 17 1 := by
  have hd := card_dvd_fixed h
  rcases CatFC.card_fixedSubgroup_j3 e (orderOf_eq_two h) with hc | hc <;> rw [hc] at hd
  · exact (hnot (inChev2_of_dvd_1920 hr2 hL hd)).elim
  · have ht := tuple_of_dvd_2448 hr2 hL hd
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ht
    exact hL

end J3

end CFSG.ComponentClassification.GS82PumpInputs.SporSmall
