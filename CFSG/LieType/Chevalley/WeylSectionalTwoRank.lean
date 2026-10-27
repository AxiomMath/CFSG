module

public import CFSG.LieType.Chevalley.SectionalTwoRankMonomial
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.Monster.B.Geometry.F4Weyl
public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.GH74

private theorem card_weylGroup_E6_eq :
    Nat.card (WeylGroup .E6) = 51840 := by
  have : Fintype (WeylGroup .E6) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E6_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

private theorem card_weylGroup_E7_eq :
    Nat.card (WeylGroup .E7) = 2903040 := by
  have : Fintype (WeylGroup .E7) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E7_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]

theorem card_weylGroup_D4_le :
    Nat.card (WeylGroup Tag.D4) ≤ 192 := by
  classical
  have : Fintype (WeylGroup Tag.D4) := Fintype.ofFinite _
  choose e he hw using CFSG.RankThree.Chevalley.exists_mem_d4WeylTab
  have hinj : Function.Injective e := fun w w' h =>
    ext_single fun i => by rw [hw w i, hw w' i, h]
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← Finset.card_image_of_injective _ hinj]
  calc (Finset.univ.image e).card ≤ CFSG.RankThree.Chevalley.d4WeylTab.toFinset.card :=
        Finset.card_le_card fun x hx => by
          obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hx
          exact List.mem_toFinset.2 (he w)
    _ ≤ CFSG.RankThree.Chevalley.d4WeylTab.length := List.toFinset_card_le _
    _ = 192 := by decide +kernel

theorem sectionalTwoRankLE_weylGroup_D4 :
    SectionalTwoRankLE (WeylGroup Tag.D4) 7 :=
  sectionalTwoRankLE_of_not_two_pow_dvd fun h => by
    have h1 := Nat.le_of_dvd Nat.card_pos h
    have h2 := card_weylGroup_D4_le
    norm_num at h1
    omega

theorem sectionalTwoRankLE_weylGroup_F4 :
    SectionalTwoRankLE (WeylGroup .F4) 7 :=
  sectionalTwoRankLE_of_not_two_pow_dvd (by
    rw [CFSG.Monster.B.Geometry.card_f4WeylGroup]
    norm_num)

theorem sectionalTwoRankLE_weylGroup_E6 :
    SectionalTwoRankLE (WeylGroup .E6) 7 :=
  sectionalTwoRankLE_of_not_two_pow_dvd (by
    rw [card_weylGroup_E6_eq]
    norm_num)

theorem sectionalTwoRankLE_weylGroup_E7 :
    SectionalTwoRankLE (WeylGroup .E7) 10 :=
  sectionalTwoRankLE_of_not_two_pow_dvd (by
    rw [card_weylGroup_E7_eq]
    norm_num)

end CFSG.LieType.Chevalley

end
