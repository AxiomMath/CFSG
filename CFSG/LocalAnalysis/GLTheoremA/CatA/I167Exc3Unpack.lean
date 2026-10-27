module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167Step0
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcParCent
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I167ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1
public import CFSG.Quasithin.Vol2.Ch11SecOE5B
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Timmesfeld

theorem exc3_family {S : Type} [Group S] (h : catalogIs S ExcBigIdx) :
    ∃ (k : DefChar.LieFamily) (qc : TauCeti.PrimePower) (hv : (LocalTwo.excIndex k qc).Valid),
      (k = .F4 ∨ k = .E6 ∨ k = .twistedE6 ∨ k = .E7 ∨ k = .E8) ∧ qc.p = 2 ∧
        Nonempty (S ≃* LocalTwo.CatT ⟨LocalTwo.excIndex k qc, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic c hc => simp [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] at hi
  | alternating a ha => simp [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] at hi
  | sporadic s => simp [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] at hi
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | E6 q =>
      have hq : q.p = 2 := by simpa [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] using hi
      exact ⟨.E6, q, hv, by simp, hq, ⟨e⟩⟩
    | F4 q =>
      have hq : q.p = 2 := by simpa [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] using hi
      exact ⟨.F4, q, hv, by simp, hq, ⟨e⟩⟩
    | twistedE6 q =>
      have hq : q.p = 2 := by simpa [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] using hi
      exact ⟨.twistedE6, q, hv, by simp, hq, ⟨e⟩⟩
    | E7 q =>
      have hq : q.p = 2 := by simpa [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] using hi
      exact ⟨.E7, q, hv, by simp, hq, ⟨e⟩⟩
    | E8 q =>
      have hq : q.p = 2 := by simpa [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] using hi
      exact ⟨.E8, q, hv, by simp, hq, ⟨e⟩⟩
    | _ => simp [ExcBigIdx, ExcE6Idx, ExcParIdx, onLie] at hi

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exc3_isQuasisimple_pQuot {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) :
    CFSG.Open.IsQuasisimple (PQuot p X) := by
  have hAll : Y10F.HasLabel (PQuot p X) (fun _ => True) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) H.hinn.2
  exact Y10F.hasLabel_isQuasisimple hAll

theorem exc3_nontrivial {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) :
    Nontrivial (PSimple p X) := by
  haveI : IsSimpleGroup (PSimple p X) := (exc3_isQuasisimple_pQuot H).2
  infer_instance

theorem exc3_not_centMod {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) :
    ¬ CentMod p X x :=
  exc_not_centMod H.hX (exc3_nontrivial H) H.hxX

theorem exc3_glaPComponent_cx {p : ℕ} {B X D J : Subgroup Ω} {x : Ω} (H : ExcHyp p B X D J x) :
    GLAPComponent p (X ⊓ Subgroup.centralizer ({x} : Set Ω)) J :=
  glaPComponent_inf_cx_of_eq_sup H.hDx H.hJ

end CFSG.LocalAnalysis.GLTheoremA.I167

end
