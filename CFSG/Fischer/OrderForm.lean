module

public import CFSG.Sporadic.Fi23.Tr.Facts
public import CFSG.Sporadic.Fi22.InvCent
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Sporadic.Fi22.LH.Facts
public import CFSG.Sporadic.Fi22.Uniqueness
public import CFSG.Sporadic.Fi23.Uniqueness
public import CFSG.Sporadic.Fi24.EdgeSwapCert
public import CFSG.Sporadic.Fi24.Fischer

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_eq_of_mulEquiv {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}
    (iso : X ≃* Y) (h : iso '' E = F) : Nat.card X = Nat.card Y ∧ Nat.card E = Nat.card F := by
  refine ⟨Nat.card_congr iso.toEquiv, ?_⟩
  rw [← h]
  exact (Nat.card_image_of_injective iso.injective E).symm

theorem card_of_hasType_F22
    {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X)) (hT : HasType 0 X E) :
    Nat.card X = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ∧ Nat.card E = 3510 := by
  obtain ⟨iso, hiso⟩ := Sporadic.Fi22.fischer_uniqueness_zero polarFacts X E hP hZ hS hT
  obtain ⟨h1, h2⟩ := card_eq_of_mulEquiv iso hiso
  have hC : Nat.card (Carrier 0) = Nat.card Blueprint.NativeSporadic.Fi22 := rfl
  have hD : Nat.card Sporadic.Fi22.D22 = Nat.card Sporadic.Fi22.D :=
    Nat.card_image_of_injective Sporadic.Fi22.fi22EquivJ.symm.injective _
  rw [h1, h2, hC, hD, Sporadic.Fi22.card_Fi22, ← Nat.card_congr Sporadic.Fi22.ptD,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem card_of_hasType_F23
    {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X)) (hT : HasType 1 X E) :
    Nat.card X = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 ∧ Nat.card E = 31671 := by
  obtain ⟨iso, hiso⟩ := Sporadic.Fi23.fischer_uniqueness_one polarFacts hyperovalFacts
    (Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts) X E hP hZ hS hT
  obtain ⟨h1, h2⟩ := card_eq_of_mulEquiv iso hiso
  have hC : Nat.card (Carrier 1) = Nat.card Blueprint.NativeSporadic.Fi23 := rfl
  have hD : Nat.card Sporadic.Fi23.D23c = Nat.card Sporadic.Fi23.D23 :=
    Nat.card_image_of_injective Sporadic.Fi23.fi23EquivJ.symm.injective _
  rw [h1, h2, hC, hD, Sporadic.Fi23.card_Fi23, ← Nat.card_congr Sporadic.Fi23.ptD23,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num

theorem card_of_hasType_F24
    {X : Type} [Group X] {E : Set X} (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (hS : IsSimpleGroup (commutator X)) (hT : HasType 2 X E) :
    Nat.card X = 2 ^ 22 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 ∧
      Nat.card E = 306936 := by
  have hFF := Sporadic.Fi22.fi22Facts polarFacts hyperovalFacts
  obtain ⟨iso, hiso⟩ := Sporadic.Fi24.fischer_uniqueness_two polarFacts hyperovalFacts hFF
    (Sporadic.Fi23.fi23Facts hFF) Sporadic.Fi22.card_fixed_involution_D
    Sporadic.Fi22.eq_of_commute_centralizer Sporadic.Fi24.edgeSwap_a
    Sporadic.Fi23.d1_mem_localClass Sporadic.Fi23.involution_cover X E hP hZ hS hT
  obtain ⟨h1, h2⟩ := card_eq_of_mulEquiv iso hiso
  have hC : Nat.card (Carrier 2) = Nat.card Sporadic.Fi24.R :=
    (Nat.card_congr (Sporadic.Fi24.rEquivAut polarFacts hyperovalFacts hFF
      (Sporadic.Fi23.fi23Facts hFF) Sporadic.Fi22.card_fixed_involution_D
      Sporadic.Fi22.eq_of_commute_centralizer Sporadic.Fi24.edgeSwap_a
      Sporadic.Fi23.d1_mem_localClass Sporadic.Fi23.involution_cover).toEquiv).symm
  rw [h1, h2, hC, Sporadic.Fi24.card_R, ← Sporadic.Fi24.card_D24]
  refine ⟨by norm_num, ?_⟩
  exact Nat.card_image_of_injective (MulEquiv.injective _) _

end CFSG.Fischer
