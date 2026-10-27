module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TOuter
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XFIso
public import CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnAPI

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieComp

set_option linter.unusedSectionVars false


theorem u4InnOuter_d4two {S : Type} [Group S] [Finite S] (hcat : catalogIs S S9.isD4two)
    {u : MulAut S} (hu3 : u ^ 3 = 1) (hout : ∀ a : S, MulAut.conj a ≠ u)
    (hq : HasU4Quot (u4Fix u)) : False := by
  obtain ⟨-, K₀, _, _, hK₀, ⟨e⟩⟩ := D4XF.statedModel_of_d4two hcat
  have hK₀' : Nat.card K₀ = 2 := by rw [hK₀]; norm_num
  obtain ⟨eC⟩ := CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup K₀
  let e₂ := e.trans eC
  have hα : MulAut.congr e₂ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hout' : ∀ h : adjointGroup Tag.D4 K₀, MulAut.conj h ≠ MulAut.congr e₂ u := by
    intro h hh
    apply hout (e₂.symm h)
    refine MulEquiv.ext fun y => e₂.injective ?_
    have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.D4 K₀) => φ (e₂ y)) hh
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simpa using h1
  have hdvd := D4T.outer_card_dvd hK₀' (MulAut.congr e₂ u) hα hout'
  have hcard : Nat.card ↥(fixSubgroup u) = Nat.card ↥(fixSubgroup (MulAut.congr e₂ u)) :=
    Nat.card_congr (fixSubgroupCongrEquiv e₂ u).toEquiv
  have hfix : u4Fix u = fixSubgroup u := by ext x; exact Iff.rfl
  have h5 : 5 ∣ Nat.card ↥(fixSubgroup u) := by
    rw [← hfix]
    exact (show 5 ∣ 25920 by norm_num).trans hq.dvd_card
  have h5' : 5 ∣ CFSG.Open.ordTrialityD4 2 := h5.trans (hcard ▸ hdvd)
  revert h5'
  unfold CFSG.Open.ordTrialityD4
  decide +kernel

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
