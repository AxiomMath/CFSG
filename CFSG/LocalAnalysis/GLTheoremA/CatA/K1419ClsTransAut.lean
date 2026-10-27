module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144ILabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

private theorem i1419Rel_of_betaBar {Q : Type} [Group Q] [Finite Q] (β : MulAut Q) {x y : PQ Q}
    (h : H1419.betaBar β x = y) : I1419Rel β x y := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨l, β l, rfl, by rw [← H1419.betaBar_mk β l]; exact h, rfl⟩

theorem k1419ClsTransAut_holds : K1419ClsTransAutFact := by
  intro Q _ _ β hQ hNt hInn
  have hI144 : CFSG.LocalAnalysis.GLTheoremA.K144.I144Inner (PQ Q) (H1419.betaBar β) := by
    show GLAMarking (PQ Q) (fun _ _ _ I _ θ =>
      ∃ φ ∈ I, GLAInduces θ (fun x y : PQ Q => H1419.betaBar β x = y) φ)
    have hInn' : GLAMarking (PQ Q) (fun _ _ _ I _ θ => ∀ k : ℤ,
        ∃ φ ∈ I, GLAInduces θ (I1419Rel (β ^ k)) φ) := hInn
    refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_ hInn'
    intro lab R _ I F θ h
    obtain ⟨φ, hφ, hφind⟩ := h 1
    rw [zpow_one] at hφind
    exact ⟨φ, hφ, fun x y hxy => hφind x y (i1419Rel_of_betaBar β hxy)⟩
  obtain ⟨labK, hlab, hinnDiag⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K144I.innDiagKind_of_i144Inner hQ hI144
  refine ⟨labK, hlab, ?_, hinnDiag⟩
  intro hOne
  have hbar : H1419.betaBar β = 1 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.eq_one_of_trivial_centerQuot hQ.1 (H1419.betaBar β) hOne
  obtain ⟨l, hl⟩ := hNt
  exact hl (by rw [← H1419.betaBar_mk β l, hbar, MulAut.one_apply])

end CFSG.LocalAnalysis.GLTheoremA.K1419
