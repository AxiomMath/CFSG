module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdjDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw
public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I171
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley

private theorem catalogIs_of_mulEquiv {S R : Type} [Group S] [Group R] (e : S ≃* R)
    {Q : TauCeti.CFSGIndex → Prop} (h : catalogIs R Q) : catalogIs S Q := by
  obtain ⟨i, hi, ⟨e'⟩⟩ := h
  exact ⟨i, hi, ⟨e.trans e'⟩⟩

private theorem exists_twE6Idx_of_catalogIs {S : Type} [Group S]
    (h : catalogIs S (onLie (CharTwoOf isTwE6Idx))) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid),
      q.p = 2 ∧ Nonempty (S ≃* CFSG.LieType.SeitzGeneration.Cat
        ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic p hp => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic nm => simp [onLie] at hi
  | lie j =>
      obtain ⟨d, hv⟩ := j
      cases d with
      | twistedE6 q =>
          simp only [onLie, CharTwoOf, isTwE6Idx, TauCeti.LieTypeIndex.characteristic_twistedE6,
            true_and] at hi
          exact ⟨q, hv, hi, ⟨e⟩⟩
      | A n q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | twistedA n q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | B n q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | C n q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | D n q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | twistedD n q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | E6 q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | E7 q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | E8 q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | F4 q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | G2 q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | trialityD4 q => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | suzuki m => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | reeG2 m => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | reeF4 m => simp [onLie, CharTwoOf, isTwE6Idx] at hi
      | tits => simp [onLie, CharTwoOf, isTwE6Idx] at hi


theorem twE6Diag_of (hK : T171Sh.ExcKernelCompAction) (hD4 : TwE6D4Inner) (hL : CatLayer)
    (hC : CatChevComps) (hG : DiagOfCompAction) (hT : MarkTransport) (hI : ShapeModelDiagIso) :
    SimpleDiagModel (CharTwoOf isTwE6Idx) := by
  intro S _ _ p hp hp2 hcat hshape
  obtain ⟨q, hv, hq2, ⟨eS⟩⟩ := exists_twE6Idx_of_catalogIs hcat
  obtain ⟨K, _, σ, hKcard, hσ, ⟨eCat⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_twistedE6 q hv
  haveI hKfin : Finite K :=
    (Nat.card_ne_zero.mp (by
      rw [hKcard]
      exact pow_ne_zero 2 (pow_ne_zero q.exponent q.prime_p.ne_zero))).2
  haveI : Finite ↥(twistedE6RootGroup K σ) := by
    haveI : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
    exact Subtype.finite
  have eR : ↥(twistedE6RootGroup K σ) ≃* S := (eS.trans eCat).symm
  have hcatR : catalogIs ↥(twistedE6RootGroup K σ)
      (onLie fun d : TauCeti.LieTypeIndex => d.characteristic = 2) :=
    ⟨.lie ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩, by
      simp only [onLie, TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact hq2, ⟨eCat.symm⟩⟩
  have hnotshapeR : ¬ catalogIs ↥(twistedE6RootGroup K σ) (onLie (I171LieShape p)) :=
    fun h => hshape (catalogIs_of_mulEquiv eR.symm h)
  have hnot3 : p = 3 → ¬ 3 ∣ q.p ^ q.exponent + 1 := by
    intro hp3 hdvd
    exact hnotshapeR ⟨.lie ⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩, by
      simp only [onLie, I171LieShape, TauCeti.PrimePower.card_def]
      exact ⟨hp3, hq2, hdvd⟩, ⟨eCat.symm⟩⟩
  have hcomp : CompActionAt ↥(twistedE6RootGroup K σ) p := by
    intro x w hx1 hxp hwp hxw Kc hKc h360 hstab
    exact (T171Sh.twE6ComponentAction_holds hK T171Sh.twE6CentralizerConnOdd_holds)
      hp hp2 hq2 σ hKcard hσ hnot3 x w hx1 hxp hxw Kc hKc hstab h360
  have hd4 : D4ExitAt ↥(twistedE6RootGroup K σ) p := hD4 q hq2 K σ hKcard hσ p hp hp2 hnot3
  have hR : ShapeModelDiagAt ↥(twistedE6RootGroup K σ) p :=
    hG ↥(twistedE6RootGroup K σ) p hp hp2
      (hL ↥(twistedE6RootGroup K σ) p hp hp2 hcatR)
      (hC ↥(twistedE6RootGroup K σ) p hp hp2 hcatR) hcomp hd4
  exact hI hT ↥(twistedE6RootGroup K σ) S eR p hR

end CFSG.LocalAnalysis.GLTheoremA.F151

end
