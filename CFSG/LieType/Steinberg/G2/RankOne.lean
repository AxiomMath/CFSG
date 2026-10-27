module

public import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.LieType.Steinberg.Adjoint.RankOneString

public noncomputable section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K]

theorem g2_cartan_zero_one : Tag.cartan .G2 (0 : Fin 2) (1 : Fin 2) = -1 := by decide

theorem g2_cartan_one_zero : Tag.cartan .G2 (1 : Fin 2) (0 : Fin 2) = -3 := by decide

theorem g2_eq_one_of_mem_normalizer_one
    {u : adjointGroup .G2 K}
    (hu : u ∈ rootGroup (rootOperatorFamily .G2) K (Pi.single (1 : Fin 2) 1))
    (hn : u ∈ Subgroup.normalizer
      (rootGroup (rootOperatorFamily .G2) K (-Pi.single (1 : Fin 2) 1) :
        Set (adjointGroup .G2 K))) :
    u = 1 :=
  eq_one_of_mem_normalizer_of_cartan_eq_neg_three _ g2_cartan_one_zero hu hn

theorem g2_exists_sl2_hom_one :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = (rootOperatorFamily .G2).eltElement (simpleRoot .G2 (1 : Fin 2)) c) ∧
        ∀ c, φ (sl2Lower c) = (rootOperatorFamily .G2).eltElement (-simpleRoot .G2 (1 : Fin 2)) c :=
  exists_sl2_hom_of_cartan_eq_neg_three _ g2_cartan_one_zero

theorem g2_eq_one_of_mem_normalizer
    (i : Fin (Tag.rank .G2)) {u : adjointGroup .G2 K}
    (hu : u ∈ rootGroup (rootOperatorFamily .G2) K (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer
      (rootGroup (rootOperatorFamily .G2) K (-Pi.single i 1) : Set (adjointGroup .G2 K))) :
    u = 1 := by
  fin_cases i
  · exact eq_one_of_mem_normalizer _ g2_cartan_zero_one hu hn
  · exact g2_eq_one_of_mem_normalizer_one hu hn

theorem g2_exists_sl2_hom
    (i : Fin (Tag.rank .G2)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = (rootOperatorFamily .G2).eltElement (simpleRoot .G2 i) c) ∧
        ∀ c, φ (sl2Lower c) = (rootOperatorFamily .G2).eltElement (-simpleRoot .G2 i) c := by
  fin_cases i
  · exact exists_sl2_hom _ g2_cartan_zero_one
  · exact g2_exists_sl2_hom_one

end CFSG.LieType.Steinberg.Adjoint
