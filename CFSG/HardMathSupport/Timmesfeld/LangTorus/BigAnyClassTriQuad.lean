module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyClass
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTri

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open scoped Matrix

set_option linter.unusedSectionVars false

section Class

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}

theorem LangSetup.bigAnyPBig_of_weylClass_tri (S : LangSetup τ L p) (hτ : SimplyLacedTag τ)
    (hp7 : 7 ≤ p) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : M * M = -M - 1)
    (h : S.IsWeylClass M) : BigAnyPBig S := by
  obtain ⟨Fr, hFr, hΦ, w, hn, hw, hMΓ⟩ := h
  refine bigAnyPBig_of_phi3 S hFr hΦ hn hτ (fun δ _ => ?_) hp7 hMΓ
  simp only [hw]
  rw [Matrix.mulVec_mulVec, hM, Matrix.sub_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]

end Class

theorem e8ThreeMat_rel : wordMat Tag.E8 e8ThreeWord * wordMat Tag.E8 e8ThreeWord =
    -wordMat Tag.E8 e8ThreeWord - 1 := by
  rw [e8Three_wordMat]
  decide +kernel

theorem e8FourMat_rel : wordMat Tag.E8 e8FourWord * wordMat Tag.E8 e8FourWord = -1 := by
  rw [e8Four_wordMat]
  decide +kernel

end CFSG.HardMathSupport.Timmesfeld.LangTorus
