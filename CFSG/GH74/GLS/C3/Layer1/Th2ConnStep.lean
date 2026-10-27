module

public import CFSG.GH74.GLS.C3.Layer1.Th2Conn

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem rConnN_three_four_high [Finite G] {X A W B : Subgroup G}
    (hAW4 : IsE 4 X (A ⊔ W)) (hAW3 : IsE 3 X (A ⊔ W)) (hW3X : IsE 3 X W)
    (hB4 : IsE 4 X B) (hWB : W ≤ B) (hB3 : IsE 3 X B) : RConnN 3 4 X A B := by
  have s1 : ConnStep 3 4 X A (A ⊔ W) :=
    connStep_of_le_elem (r := 3) (n := 4) (X := X) (W := A ⊔ W) (A' := A)
      (A'' := A ⊔ W) hAW4 (show A ≤ A ⊔ W from le_sup_left)
      (show A ⊔ W ≤ A ⊔ W from le_rfl) hAW3
  have s2 : ConnStep 3 4 X (A ⊔ W) W :=
    connStep_of_le_elem (r := 3) (n := 4) (X := X) (W := A ⊔ W) (A' := A ⊔ W)
      (A'' := W) hAW4 (show A ⊔ W ≤ A ⊔ W from le_rfl)
      (show W ≤ A ⊔ W from le_sup_right) hW3X
  have s3 : ConnStep 3 4 X W B :=
    connStep_of_le_elem (r := 3) (n := 4) (X := X) (W := B) (A' := W) (A'' := B)
      hB4 (show W ≤ B from hWB) (show B ≤ B from le_rfl) hB3
  exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single s1)
    (Relation.ReflTransGen.trans (Relation.ReflTransGen.single s2)
      (Relation.ReflTransGen.single s3))

theorem eq_of_le_of_isElementaryAbelian_pRank_three [Finite G] {A C : Subgroup G}
    (hAC : A ≤ C) (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hCel : CFSG.IsElementaryAbelian 2 ↥C)
    (hArk : pRank 2 ↥A = 3) (hCrk : pRank 2 ↥C = 3) : A = C := by
  have hcardA : Nat.card ↥A = 2 ^ 3 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hAel, hArk]
  have hcardC : Nat.card ↥C = 2 ^ 3 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hCel, hCrk]
  exact Subgroup.eq_of_le_of_card_ge hAC (by rw [hcardA, hcardC])

theorem rConnN_three_four_low [Finite G] {X A W B : Subgroup G}
    (hAel : CFSG.IsElementaryAbelian 2 ↥A)
    (hAWel : CFSG.IsElementaryAbelian 2 ↥(A ⊔ W))
    (hA3 : 3 ≤ pRank 2 ↥A) (hAWle3 : pRank 2 ↥(A ⊔ W) ≤ 3)
    (hWel : CFSG.IsElementaryAbelian 2 ↥W) (hW3 : 3 ≤ pRank 2 ↥W)
    (hB4 : IsE 4 X B) (hWB : W ≤ B) (hB3 : IsE 3 X B) : RConnN 3 4 X A B := by
  have hAle : pRank 2 ↥A ≤ pRank 2 ↥(A ⊔ W) :=
    C3.Layer1.Back.pRank_mono' le_sup_left
  have hArk : pRank 2 ↥A = 3 := le_antisymm (hAle.trans hAWle3) hA3
  have hWele : pRank 2 ↥W ≤ pRank 2 ↥(A ⊔ W) :=
    C3.Layer1.Back.pRank_mono' le_sup_right
  have hWrk : pRank 2 ↥W = 3 := le_antisymm (hWele.trans hAWle3) hW3
  have hAWrk : pRank 2 ↥(A ⊔ W) = 3 := le_antisymm hAWle3 (hA3.trans hAle)
  have hAeq : A = A ⊔ W :=
    eq_of_le_of_isElementaryAbelian_pRank_three le_sup_left hAel hAWel hArk hAWrk
  have hWA : W ≤ A := hAeq ▸ le_sup_right
  have hWeq : W = A :=
    eq_of_le_of_isElementaryAbelian_pRank_three hWA hWel hAel hWrk hArk
  have hAleB : A ≤ B := hWeq ▸ hWB
  exact Relation.ReflTransGen.single
    (connStep_of_le_elem (r := 3) (n := 4) (X := X) (W := B) (A' := A) (A'' := B)
      hB4 hAleB le_rfl hB3)


end CFSG.GH74.GLS.Th2
