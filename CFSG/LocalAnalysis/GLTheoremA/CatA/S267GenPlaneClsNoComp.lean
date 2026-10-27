module

import CFSG.LocalAnalysis.GLTheoremA.S6.AltSetup
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Gen

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def PlaneNoComp (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup (MulAut G), IsElemAbelian p P → Nat.card P = p ^ 2 →
    ∀ J : Subgroup G, ¬ ∀ x ∈ P, x ≠ 1 → GLAPComponent p (fixSubgroup x) J

theorem PlaneNoComp.of_mulEquiv {p : ℕ} (hp : p.Prime) {G H : Type} [Group G] [Group H]
    [Finite G] (e : G ≃* H) (h : PlaneNoComp p H) : PlaneNoComp p G := by
  intro P hP hcard J hJ
  refine h (P.map (MulAut.congr e).toMonoidHom) (hP.map _) ?_ (J.map e.toMonoidHom) ?_
  · rw [← hcard]
    exact Subgroup.card_map_of_injective (MulAut.congr e).injective
  · rintro _ ⟨x, hxP, rfl⟩ hx1
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1]; exact map_one _)
    have hc := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_map_mulEquiv hp e (hJ x hxP hx1')
    have hfix := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e x
    change GLAPComponent p (fixSubgroup (MulAut.congr e x)) (J.map e.toMonoidHom)
    rw [hfix]
    exact hc

theorem genPlaneCompOn_of_planeNoComp {Q : TauCeti.LieTypeIndex → Prop}
    (h : ∀ (p : ℕ) (d : TauCeti.ValidLieTypeIndex),
      OddLie p (TauCeti.CFSGIndex.lie d).Group d → Q d.1 →
        PlaneNoComp p (TauCeti.CFSGIndex.lie d).Group) : GenPlaneCompOn Q := by
  intro p T _ _ d hd hQ
  obtain ⟨e⟩ := hd.iso
  haveI : Finite (TauCeti.CFSGIndex.lie d).Group := Finite.of_equiv T e
  have hd' : OddLie p (TauCeti.CFSGIndex.lie d).Group d :=
    ⟨hd.prime, hd.odd, ⟨MulEquiv.refl _⟩, hd.charOdd, hd.ne⟩
  exact PlaneNoComp.of_mulEquiv hd.prime e (h p d hd' hQ)

end CFSG.LocalAnalysis.GLTheoremA.S267.Gen
