module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieThreeBase
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieThreeE6
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Assembly
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthOdd
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthPlus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.OrthMinus
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.G2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.F4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E7
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E8
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.ReeG2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.D4
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4C3
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.ComponentClassification.CatLeaf
  CFSG.HardMathSupport.Dickson.Sec6 CFSG.HardMathSupport.Dickson.Sec6.I923
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.RankTwoClassical (statedProjEquiv)

theorem lieS3_noL2Layer
    {P : Type} [Group P] [Finite P] {t : StatedLieTag} {n f : ℕ}
    (hadm : StatedLieAdmissible t n 3 f) (ht : t ≠ .Tits) (hA : ¬ (t = .PSL ∧ n = 2))
    (hm : LieModel P t n 3 f) {ψ : MulAut P} (hψ3 : ψ ^ 3 = 1) (hψ : ψ ∉ inner P) :
    NoL2Layer ψ := by
  have hO : LieOrderFormulasInput := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  rcases fam_cover_three hadm ht with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact absurd h hA
  · obtain ⟨rfl, hn3, hcop⟩ := h
    have hC : StatedClassicalModel P .PSL n 3 f := (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [← hK] at hcop
    exact lieS3_noL2Layer_of_famOK (e0.trans (statedProjEquiv n K))
      (famOK_psl hO hn3 hcop hadm.1 hadm.2.1 hK) hψ3 hψ
  · obtain ⟨rfl, hn2, hex⟩ := h
    have hC : StatedClassicalModel P .PSp n 3 f := (lieModel_classical_iff (by decide)).mp hm
    obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
    rw [← hK] at hex
    exact lieS3_noL2Layer_of_famOK e0 (famOK_psp hO hn2 hadm.1 hadm.2.1 hK hex) hψ3 hψ
  · obtain ⟨rfl, hn3, hdiv⟩ := h
    obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
    have hne : ¬(n = 3 ∧ 3 ^ f = 2) := fun ⟨h1, h2⟩ => hadm.2.2.2 (by rw [h1, h2])
    exact lieS3_noL2Layer_of_famOK e0 (famOK_psu hO h hn3 hne hdiv) hψ3 hψ
  · exact noL2OuterAt_orthOdd hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_orthPlus hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_orthMinus hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_d4 hO triD4A2NoL2_holds triD4C3NoL2_holds P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_triD4 triD4A2NoL2_holds triD4C3NoL2_holds P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_g2 hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_f4 hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · obtain rfl := h
    exact lieS3_noL2_e6 hO hadm hm hψ3 hψ
  · obtain rfl := h
    exact lieS3_noL2_twE6 hO hadm hm hψ3 hψ
  · exact noL2OuterAt_e7 hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_e8 hO P t n 3 f hadm ht h hm ψ hψ3 hψ
  · exact noL2OuterAt_reeg2 hO P t n 3 f hadm ht h hm ψ hψ3 hψ

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
