module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.LocalAnalysis.GLTheoremA.S10

@[expose] def InnerDiagInnerOrShape (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    Setup p L J A d b → catalogIs (PSimple p L) (onLie F) →
      InducesInnerMod p L b ∨ I171.I171LieShapeAt p L

@[expose] def InnerCompNonShape (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    Setup p L J A d b → catalogIs (PSimple p L) (onLie F) →
      ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b →
        InnDiagOn p (Subgroup.zpowers b) J

theorem shape15On_of_residuals {F : TauCeti.LieTypeIndex → Prop}
    (hOut : InnerDiagInnerOrShape F) (hIn : InnerCompNonShape F) : Shape15On F := by
  intro G _ _ p L J A d b hS hcat
  by_cases hshape : I171.I171LieShapeAt p L
  · exact hshape
  · have hmain : InducesInnerMod p L b ∨ I171.I171LieShapeAt p L :=
      hOut p L J A d b hS hcat
    rcases hmain with hin | hs
    · exact absurd (hIn p L J A d b hS hcat hshape hin) hS.nonID
    · exact absurd hs hshape

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
