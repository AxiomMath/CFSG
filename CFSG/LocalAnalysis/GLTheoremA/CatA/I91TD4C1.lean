module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T10
import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinctG2Exc
import CFSG.LocalAnalysis.GLTheoremA.CatA.K148DownMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFAK148G2
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM6TwoG2
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTSp8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I91T

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10

section Certificates


theorem td4C1NotExc_of_distinct
    (hG2X : ∀ (S : Type) [Group S] [Finite S] (q : TauCeti.PrimePower)
      (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      (S ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) → catalogIs S excIndex → False)
    (hU33X : ∀ (S : Type) [Group S] [Finite S], catalogIs S isU33 → catalogIs S excIndex → False) :
    TD4C1NotExc := by
  intro G _ _ X L b hL hchev hTD4 hb3 hNI hcent I hI _ hexc
  classical
  have hfix : Nat.sqrt (card2 3 L) ≤ 2 * twoPart (Nat.card ↥(lemma102_fixSub 3 hNI.1)) := by
    rw [← hcent, lemma102_centCard2_eq_fixSub 3 hNI.1]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  have hQI : CFSG.Open.IsQuasisimple (PQuot 3 I) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hI
  have hnc : ¬ IsMulCommutative (PQuot 3 I) :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.not_isMulCommutative_of_quasisimple hQI
  rcases k148_outer K148G2SimpleFact_holds K148TwoG2Fact_holds hL hchev hTD4 hNI.1 hb3 hNI hI hfix
    with ⟨q, hv, hq2, -, ⟨eG2⟩⟩ | hU3
  ·
    haveI : IsSimpleGroup (PQuot 3 I) := by
      haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
        (CFSG.Assembly.lie_finite_simple ⟨.G2 q, hv⟩).2
      exact MulEquiv.isSimpleGroup eG2
    have hcenter : Subgroup.center (PQuot 3 I) = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
    let eS : PSimple 3 I ≃* PQuot 3 I :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    have hexc' : catalogIs (PQuot 3 I) excIndex := (catalogIs_congr eS).1 hexc
    exact hG2X (PQuot 3 I) q hv hq2 eG2 hexc'
  ·
    haveI : IsSimpleGroup (PQuot 3 I) := by
      obtain ⟨i, hi, ⟨eU⟩⟩ := hU3
      cases i with
      | lie idx =>
        haveI : IsSimpleGroup idx.Group := (CFSG.Assembly.lie_finite_simple idx).2
        exact MulEquiv.isSimpleGroup eU
      | cyclic _ _ => exact False.elim hi
      | alternating _ _ => exact False.elim hi
      | sporadic _ => exact False.elim hi
    have hcenter : Subgroup.center (PQuot 3 I) = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
    let eS : PSimple 3 I ≃* PQuot 3 I :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    have hexc' : catalogIs (PQuot 3 I) excIndex := (catalogIs_congr eS).1 hexc
    exact hU33X (PQuot 3 I) hU3 hexc'

theorem td4C1NotExc_of_ctx (hc : CatDistinct.Ctx) : TD4C1NotExc :=
  td4C1NotExc_of_distinct (fun S _ _ q hv hq2 e h2 => CatDistinct.field_g2_exc hc S q hv hq2 e h2)
    (fun S _ _ h1 h2 => CatDistinct.field_u33_exc hc S h1 h2)

end Certificates

end CFSG.LocalAnalysis.GLTheoremA.I91T

end
