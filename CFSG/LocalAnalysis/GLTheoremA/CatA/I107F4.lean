module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107F2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

@[expose] def SurvivorLabelCat : Prop :=
  ∀ lab : GLALabel, GLAInLambda2 lab → survivor107 lab →
    Rk2LabelAll lab fun R [Group R] _ _ => catalogIs R S9.isList107

theorem catalogIs_of_mulEquiv_src {S R : Type} [Group S] [Group R] {Q : TauCeti.CFSGIndex → Prop}
    (h : catalogIs R Q) (e : S ≃* R) : catalogIs S Q := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans f⟩⟩

theorem rk2IsLabel_inLambda2 {S : Type} [Group S] {lab : GLALabel} (h : Rk2IsLabel S lab) : GLAInLambda2 lab := by
  obtain ⟨-, lab0, hlab0, hraw⟩ := h
  obtain ⟨R, _, I, F, hQ⟩ := rk2_rawDatum_exists hraw
  have hl : lab0 = lab := hQ.2.2.choose_spec
  subst hl
  exact hlab0

theorem i107CatAt_of_survivor (hSurv : SurvivorLabelCat) : I107CatAt := by
  intro S _ lab hS hrk hsurv
  have hlab : GLAInLambda2 lab := rk2IsLabel_inLambda2 hrk
  have h1 := hSurv lab hlab hsurv _ (rk2IsLabel_rawDatum hrk)
  obtain ⟨R, _, I, F, ⟨⟨hsR, hnaR, ⟨θ⟩⟩, hcat⟩⟩ := rk2_rawDatum_exists h1
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_quotient_nonab θ hnaR
  let e₀ : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact catalogIs_of_mulEquiv_src hcat (e₀.symm.trans θ)

end CFSG.LocalAnalysis.GLTheoremA

end
