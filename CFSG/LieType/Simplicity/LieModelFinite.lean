module

public import CFSG.Blueprint.Catalog
import CFSG.LieType.Simplicity.Classical
import CFSG.LieType.Simplicity.Finiteness

public section

namespace CFSG.LieType.Simplicity

theorem finite_of_native_lieModel {G : Type} [Group G]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (h : CFSG.Blueprint.LieModel G t n p f) : Finite G := by
  rcases h with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
  · exact finite_of_statedClassicalModel h
  · exact fam_chevalley_exceptional_finiteness G t p f h
  · exact fam_ree_tits_finiteness G t p f h
  · exact fam_suzuki_finiteness G p f h

end CFSG.LieType.Simplicity
