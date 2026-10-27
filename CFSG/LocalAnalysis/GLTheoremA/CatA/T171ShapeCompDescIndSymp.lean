module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeCompDescIndNat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeSpBlockResidual

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

theorem sympComponentDescent_inv_holds :
    ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) (m n : ℕ)
      (K : Type) [Field K] [Finite K] (x y : StatedSp m K)
      (θ : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSp m K)),
      (hS : Setup p L J A d b) →
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = d⁻¹ * l * d)
        (MulAut.conj (proj m K x)) →
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * l * b)
        (MulAut.conj (proj m K y)) →
      ∀ (hN : proj m K y ∈ Subgroup.normalizer
          (((J.subgroupOf L).map (piCenterQuot θ)) :
            Set (StatedProj (StatedSp m K)))),
        ∃ e : PSimple p J ≃* PSimple p ((J.subgroupOf L).map (piCenterQuot θ)),
          MulAut.congr e (CFSG.LocalAnalysis.GLTheoremA.MI.indAut p J b hS.b_norm) =
            CFSG.LocalAnalysis.GLTheoremA.MI.indAut p ((J.subgroupOf L).map (piCenterQuot θ))
              (proj m K y)⁻¹ (Subgroup.inv_mem _ hN) := by
  intro G _ _ p L J A d b m n K _ _ x y θ hS _hd hind hN
  exact componentDescentIndAut_inv_holds p L J A d b θ (proj m K y) hS hind hN

theorem sympComponentDescent_holds : SympComponentDescent :=
  sympComponentDescent_inv_holds

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
