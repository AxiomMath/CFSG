module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

open scoped commutatorElement

theorem lines_card_z2_sym5 {X : Type*} [Group X] (hX : IsShapeZ2TimesSym 5 X) :
    Nat.card X = 240 := by
  obtain ⟨e⟩ := hX
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  norm_num [Nat.factorial]

theorem lines_card_a5 {X : Type*} [Group X] (hX : IsShapeA5 X) : Nat.card X = 60 := by
  obtain ⟨e⟩ := hX
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num [Nat.factorial]

theorem lines_isShapeA5_derivedOf {G : Type} [Group G] {K : Subgroup G}
    (hK : IsShapeZ2TimesSym 5 ↥K) : IsShapeA5 ↥(derivedOf K) := by
  classical
  obtain ⟨e⟩ := hK
  have hZ : (⁅(⊤ : Subgroup (Z 2)), ⊤⁆ : Subgroup (Z 2)) = ⊥ := by
    rw [← _root_.commutator_def]
    exact (commutator_eq_bot_iff (Z 2)).mpr inferInstance
  have hS : (⁅(⊤ : Subgroup (Sym 5)), ⊤⁆ : Subgroup (Sym 5)) =
      alternatingGroup (Fin 5) := by
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (α := Fin 5) (by rw [Nat.card_fin])
  have hcomm : _root_.commutator (Z 2 × Sym 5) =
      (⊥ : Subgroup (Z 2)).prod (alternatingGroup (Fin 5)) := by
    rw [_root_.commutator_def, ← Subgroup.top_prod_top (G := Z 2) (N := Sym 5),
      Subgroup.commutator_prod_prod, hZ, hS]
  have hgmap : (_root_.commutator ↥K).map e.toMonoidHom = _root_.commutator (Z 2 × Sym 5) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  let eK : ↥(derivedOf K) ≃* ↥(_root_.commutator ↥K) :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥K) K.subtype K.subtype_injective).symm
  have iso1 : ↥(derivedOf K) ≃* ↥(alternatingGroup (Fin 5)) :=
    eK.trans <|
      (Subgroup.equivMapOfInjective (_root_.commutator ↥K) e.toMonoidHom e.injective).trans <|
      (MulEquiv.subgroupCongr hgmap).trans <|
      (MulEquiv.subgroupCongr hcomm).trans <|
      (Subgroup.prodEquiv (⊥ : Subgroup (Z 2)) (alternatingGroup (Fin 5))).trans <|
      MulEquiv.uniqueProd
  exact ⟨iso1⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
