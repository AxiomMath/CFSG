module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem glaPComponent_subgroupOf_restrictAut {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) {a b : MulAut S} {L I : Subgroup S} (hLa : L ≤ fixSubgroup a)
    (hLb : L.map b.toMonoidHom = L)
    (hI : GLAPComponent p (fixSubgroup a ⊓ fixSubgroup b) I) (hIL : I ≤ L) :
    GLAPComponent p
      (fixSubgroup (CFSG.LocalAnalysis.ComponentInitial.restrictAut b L hLb))
      (I.subgroupOf L) := by
  have hYX : fixSubgroup b ⊓ L ≤ fixSubgroup a ⊓ fixSubgroup b := by
    rintro y ⟨hyb, hyL⟩
    exact ⟨hLa hyL, hyb⟩
  have hIY : I ≤ fixSubgroup b ⊓ L := by
    intro i hi
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hI.1 hi)).2, hIL hi⟩
  have hYcomp : GLAPComponent p (fixSubgroup b ⊓ L) I :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp hI hIY hYX
  have hFix : (fixSubgroup b ⊓ L).subgroupOf L =
      fixSubgroup (CFSG.LocalAnalysis.ComponentInitial.restrictAut b L hLb) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · rintro ⟨hbx, -⟩
      apply Subtype.ext
      rw [CFSG.LocalAnalysis.ComponentInitial.coe_restrictAut, hbx]
    · intro hx
      refine ⟨?_, x.2⟩
      have h := congrArg Subtype.val hx
      rwa [CFSG.LocalAnalysis.ComponentInitial.coe_restrictAut] at h
  have h := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp
    (X := fixSubgroup b ⊓ L) (H := L) (K := I) inf_le_right hYcomp
  rwa [hFix] at h

end CFSG.LocalAnalysis.GLTheoremA.CatB.I2610

end
