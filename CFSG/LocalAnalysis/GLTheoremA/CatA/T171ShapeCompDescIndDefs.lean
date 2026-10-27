module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4

@[expose] def ComponentDescentIndAut : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G)
    {R : Type} [Group R] [Finite R] (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) (y : R)
    (hS : Setup p L J A d b),
    LargeEvenInduces θ (conjRel b) (MulAut.conj y) →
    ∀ hN : y ∈ Subgroup.normalizer
        (((J.subgroupOf L).map (piCenterQuot θ)) : Set R),
      ∃ e : PSimple p J ≃* PSimple p ((J.subgroupOf L).map (piCenterQuot θ)),
        MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm) =
          CFSG.LocalAnalysis.GLTheoremA.MI.indAut p
            ((J.subgroupOf L).map (piCenterQuot θ)) y⁻¹ (Subgroup.inv_mem _ hN)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
