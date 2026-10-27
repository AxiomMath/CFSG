module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenOutcomeFive
public import CFSG.LocalAnalysis.AGLEmbedding.AscEightFour
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AutSym.MulAutPerm

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open

theorem symAutInner : SymAutInner := fun _ _ _ h φ =>
  CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.AutSym.mulAut_perm_eq_conj h φ

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem outcomeFive_of_caseA'
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    {m r s : ℕ} (hm : 8 < m) (hmeven : Even m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) (hr1 : 1 ≤ r) (hrs : 2 * r + s = m)
    (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r) (hs6 : 6 ≤ s)
    (hEBX : EightBlockDataX S L r s) (hY : HasSym3LiftS S L (L ⊔ S)) :
    ∃ N r' : ℕ, Even N ∧ 2 * r' ≤ N ∧ 1 ≤ r' ∧ 6 ≤ N - 2 * r' ∧
      EightBlockData X S L r' (N - 2 * r') ∧ CFSG.QuasithinUnique.IsShort2 L ∧
      CFSG.RankThree.PartTwo.IsTypeScriptL L :=
  outcomeFive_of_caseA
    (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
    symAutInner hX hA hL hm hmeven e hN hr1 hrs hr hs6 hEBX hY


theorem outcomeOne_of_caseA_odd'
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    {m : ℕ} (hm : 8 < m) (hmodd : Odd m)
    (e : ↥(barM (L ⊔ S) L) ⧸ Subgroup.center ↥(barM (L ⊔ S) L) ≃* alternatingGroup (Fin m))
    (hN : NaturalSectionLSL S L m) (hY : HasSym3LiftS S L (L ⊔ S)) :
    InClassXBlock L :=
  outcomeOne_of_caseA_odd
    (CFSG.AGLEmbedding.asc81bEightFour_of_factorization
      CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved)
    hX hA hL hm hmodd e hN hY

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
