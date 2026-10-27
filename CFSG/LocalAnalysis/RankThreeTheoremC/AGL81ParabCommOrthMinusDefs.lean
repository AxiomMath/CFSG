module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open CFSG.AGLEmbedding.LeviBlock CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

@[expose] def OmNormFix (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    (α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : Prop :=
  (∀ x ∈ orthParab r (minusTailForm K b c) d, α x ∈ orthParab r (minusTailForm K b c) d) ∧
    (∀ (l : Fin s) (B : Matrix.SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K),
      ∃ u : ↥(orthParab r (minusTailForm K b c) d),
        orthBlockHom (minusTailForm K b c) hd l u = 1 ∧
          (u : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) =
            α ((orthLeviSL hd (minusTailForm K b c) hr l B :
                ↥(orthParab r (minusTailForm K b c) d)) :
              ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) *
              ((orthLeviSL hd (minusTailForm K b c) hr l B :
                ↥(orthParab r (minusTailForm K b c) d)) :
                ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))⁻¹) ∧
    (1 ≤ r - d (Fin.last s) → ∀ (g : _) (hg : g ∈ orthResDer K b c (r - d (Fin.last s))),
      ∃ u : ↥(orthParab r (minusTailForm K b c) d),
        orthResHom (minusTailForm K b c) hd u = 1 ∧
          (u : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) =
            α ((orthLeviResElt b c hd (commutator_orthogonalGroup_quadTail_minus hr hirr)
                ⟨g, hg⟩ : ↥(orthParab r (minusTailForm K b c) d)) :
              ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) *
              ((orthLeviResElt b c hd (commutator_orthogonalGroup_quadTail_minus hr hirr)
                ⟨g, hg⟩ : ↥(orthParab r (minusTailForm K b c) d)) :
                ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))⁻¹)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
