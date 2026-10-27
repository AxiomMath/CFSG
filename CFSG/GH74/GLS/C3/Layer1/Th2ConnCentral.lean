module

public import CFSG.GH74.GLS.C3.Layer1.Th2ConnStep

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem rConnN_three_four_of_central_aux [Finite G] {R W X B : Subgroup G}
    (hWc : W ≤ Subgroup.centralizer (R : Set G))
    (hWel : CFSG.IsElementaryAbelian 2 ↥W) (hW3 : 3 ≤ pRank 2 ↥W)
    (hB : IsSn 4 R B) (hBX : B ≤ X) (hWB : W ≤ B)
    (hXR : X ≤ R) (hWX : W ≤ X) :
    ∀ A : Subgroup G, IsE 3 X A → RConnN 3 4 X A B := by
  have hB4 : IsE 4 X B := ⟨hBX, hB.1.2.1, hB.2⟩
  have hB3 : IsE 3 X B := isE_mono_rank hB4 (by norm_num)
  have hW3X : IsE 3 X W := ⟨hWX, hWel, hW3⟩
  intro A hA
  obtain ⟨hAX, hAel, hA3⟩ := hA
  have hAWcomm : ∀ a ∈ A, ∀ w ∈ W, a * w = w * a := by
    intro a ha w hw
    exact Subgroup.mem_centralizer_iff.1 (hWc hw) a (hXR (hAX ha))
  have hAWel : CFSG.IsElementaryAbelian 2 ↥(A ⊔ W) :=
    isElementaryAbelian_sup (K := A) (L := W) hAel hWel hAWcomm
  have hAWX : A ⊔ W ≤ X := sup_le hAX hWX
  by_cases h4 : 4 ≤ pRank 2 ↥(A ⊔ W)
  · have hAW4 : IsE 4 X (A ⊔ W) := ⟨hAWX, hAWel, h4⟩
    have hAW3 : IsE 3 X (A ⊔ W) := isE_mono_rank hAW4 (by norm_num)
    exact rConnN_three_four_high hAW4 hAW3 hW3X hB4 hWB hB3
  · exact rConnN_three_four_low hAel hAWel hA3 (by omega) hWel hW3 hB4 hWB hB3

theorem rConnN_three_four_of_central [Finite G] {R W B : Subgroup G}
    (hWR : W ≤ R) (hWc : W ≤ Subgroup.centralizer (R : Set G))
    (hWel : CFSG.IsElementaryAbelian 2 ↥W) (hW3 : 3 ≤ pRank 2 ↥W)
    (hB : IsSn 4 R B) :
    ∀ A : Subgroup G,
      IsE 3 (⨆ B' ∈ {B' : Subgroup G | IsSn 4 R B'}, B') A →
        RConnN 3 4 (⨆ B' ∈ {B' : Subgroup G | IsSn 4 R B'}, B') A B := by
  have hXR : (⨆ B' ∈ {B' : Subgroup G | IsSn 4 R B'}, B') ≤ R :=
    iSup₂_le fun B' hB' => hB'.1.1
  have hBX : B ≤ ⨆ B' ∈ {B' : Subgroup G | IsSn 4 R B'}, B' :=
    le_iSup₂ (f := fun B' (_ : B' ∈ {B' : Subgroup G | IsSn 4 R B'}) => B') B hB
  have hWB' : ∀ B' ∈ {B' : Subgroup G | IsSn 4 R B'}, W ≤ B' := by
    intro B' hB'
    obtain ⟨⟨hB'R, hB'el, hB'eq⟩, -⟩ := hB'
    rw [hB'eq]
    refine le_omega1_of_isElementaryAbelian hWel (le_inf hWR ?_)
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact Subgroup.mem_centralizer_iff.1 (hWc hw) b (hB'R hb)
  have hWB : W ≤ B := hWB' B hB
  have hWX : W ≤ ⨆ B' ∈ {B' : Subgroup G | IsSn 4 R B'}, B' := hWB.trans hBX
  intro A hA
  exact rConnN_three_four_of_central_aux (R := R) (W := W) (X := ⨆ B' ∈
    {B' : Subgroup G | IsSn 4 R B'}, B') (B := B) hWc hWel hW3 hB hBX hWB hXR hWX A hA

end CFSG.GH74.GLS.Th2
