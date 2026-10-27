module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

structure WSetup {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G) :
    Prop where
  prime : p.Prime
  odd : p ≠ 2
  qs : CFSG.Open.IsQuasisimple ↥L
  chev2 : IsChevSimple 2 (PSimple p L)
  elem : IsElemAbelian p A
  idiag : InnerDiagMarking A L
  faithful : A ⊓ Subgroup.centralizer (L : Set G) = ⊥
  d_mem : d ∈ A
  d_ne : d ≠ 1
  b_mem : b ∈ A
  pcomp : GLAPComponent p (L ⊓ Subgroup.centralizer ({d} : Set G)) J
  b_norm : b ∈ Subgroup.normalizer (J : Set G)

theorem Setup.toWSetup {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G}
    {d b : G} (hS : Setup p L J A d b) : WSetup p L J A d b :=
  ⟨hS.prime, hS.odd, hS.qs, hS.chev2, hS.elem, hS.idiag, hS.faithful, hS.d_mem, hS.d_ne,
    hS.b_mem, hS.pcomp, hS.b_norm⟩

instance {G : Type} [Group G] [Finite G] {p : ℕ} {L J A : Subgroup G} {d b : G} :
    CoeOut (Setup p L J A d b) (WSetup p L J A d b) :=
  ⟨Setup.toWSetup⟩

@[expose] def InnerCompNonShapeW (F : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] (p : ℕ) (L J A : Subgroup G) (d b : G),
    WSetup p L J A d b → catalogIs (PSimple p L) (onLie F) →
      ¬ I171.I171LieShapeAt p L → InducesInnerMod p L b →
        InnDiagOn p (Subgroup.zpowers b) J

theorem innerCompNonShape_of_W {F : TauCeti.LieTypeIndex → Prop}
    (h : InnerCompNonShapeW F) : InnerCompNonShape F := by
  intro G _ _ p L J A d b hS hcat hshape hin
  exact h p L J A d b (Setup.toWSetup hS) hcat hshape hin

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
