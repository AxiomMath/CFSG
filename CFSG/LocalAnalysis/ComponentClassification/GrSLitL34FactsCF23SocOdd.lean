module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocBase
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddLie
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.ComponentClassification.GSThmB.Soc

open CFSG Subgroup CFSG.Assembly.LowTwoRank

theorem oddLieType_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ}
    (hm : Blueprint.LieModel X t n p f) (hp : p.Prime) (hp2 : p ≠ 2) : Blueprint.OddLieType X := by
  refine ⟨t, n, p, f, hp, hp2, ?_, hm⟩
  rcases hm with ⟨-, h1⟩ | ⟨rfl, -, h1⟩ | ⟨rfl, -, h1⟩ | ⟨-, -, h1⟩
  · exact h1.1
  · exact h1.1
  · exact h1.1
  · exact absurd h1.1 hp2

variable {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal] {α : G} {J : Subgroup G}

namespace Hyp

theorem false_of_oddLieType
    (h : Hyp N α J) (hGLS : CatLeaf.GLS3OddLieAutComponentsInput)
    (hodd : Blueprint.OddLieType N) : False := by
  have := h.simple
  exact (CatLeaf.not_held_not_L34_of_properFixedComponent_oddLie hGLS
    CatLeafProof.lieOrderFormulasInput h.nonabelian hodd h.properFixedComponent).2 h.isL34Type

theorem false_of_lieModel_odd
    (h : Hyp N α J) (hGLS : CatLeaf.GLS3OddLieAutComponentsInput) {t : StatedLieTag}
    {n p f : ℕ} (hm : Blueprint.LieModel N t n p f) (hp : p.Prime) (hp2 : p ≠ 2) : False :=
  h.false_of_oddLieType hGLS (oddLieType_of_lieModel hm hp hp2)

theorem false_of_alternating (h : Hyp N α J) {n : ℕ} (hn : 5 ≤ n)
    (θ : N ≃* alternatingGroup (Fin n)) : False :=
  CatLeaf.not_isL34Type_of_properFixedComponent_alternating hn θ h.properFixedComponent h.isL34Type

end Hyp

end CFSG.ComponentClassification.GSThmB.Soc
