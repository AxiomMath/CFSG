module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTFinU6S6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HSubT

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem u6ThreeDvdComp_holds : U6ThreeDvdComp := by
  intro T _ hT α hα3 _ L hL
  obtain ⟨e⟩ := nonempty_S6_of_isU6two hT
  let α₆ : MulAut LevelLieU6.S6 := e.symm.trans (α.trans e)
  have hα₆3 : α₆ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro x
    rw [conj_pow_apply, hα3, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]
  have hfix : fixSubgroup α₆ = (fixSub α).map e.toMonoidHom := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_map_equiv, mem_fixSub]
    show e (α (e.symm x)) = x ↔ α (e.symm x) = e.symm x
    constructor
    · intro h
      have := congrArg e.symm h
      simpa using this
    · intro h
      rw [h]
      simp
  have hL6 : IsComponentOf (L.map e.toMonoidHom) (fixSubgroup α₆) := by
    rw [hfix]
    exact isComponentOf_map_mulEquiv hL e
  have hd := three_dvd_card_of_component_fix α₆ hα₆3 hL6
  let eL : ↥L ≃* ↥(L.map e.toMonoidHom) := Subgroup.equivMapOfInjective L e.toMonoidHom e.injective
  rw [Nat.card_congr eL.toEquiv]
  exact hd

end CFSG.LocalAnalysis.GLTheoremA.HSubT

end
