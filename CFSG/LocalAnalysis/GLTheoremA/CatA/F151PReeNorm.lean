module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PReeNormCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151PExcNormCore
import CFSG.GroupTheory.MulAutCongr
public import CFSG.LieType.SeitzGeneration.ExcParabolicReeF4
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267GenInnerLang

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup PerfectInLayer)

open CFSG.LocalAnalysis.GLTheoremA.S267.Gen

namespace CFSG.LocalAnalysis.GLTheoremA.F151

private theorem reeF4_extract
    {S : Type} [Group S] (hcat : catalogIs S (onLie (CharTwoOf isReeF4Idx))) :
    ∃ (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeF4 m).Valid),
      IsSimpleGroup S ∧ ¬ IsMulCommutative S ∧
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩).Group) := by
  classical
  rcases hcat with ⟨i, hi, ⟨e⟩⟩
  cases i with
  | lie dd =>
    obtain ⟨d, hd⟩ := dd
    cases d with
    | reeF4 m =>
      have hv : (TauCeti.LieTypeIndex.reeF4 m).Valid := hd
      obtain ⟨X, hfield, hfinite, hchar, hm1, hXcard, hsimple, ⟨eX⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_reeGamma_equiv_cat hv
      letI := hfield
      letI := hfinite
      haveI : CharP X CFSG.LieType.Ree.ReeTag.F4.prime := hchar
      haveI : IsSimpleGroup
          (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.reeF4 m, hv⟩).Group := hsimple
      have hsimpleS : IsSimpleGroup S := e.isSimpleGroup
      haveI : IsSimpleGroup S := hsimpleS
      have hnab : ¬ IsMulCommutative S := by
        haveI : IsSimpleGroup ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma X m) :=
          eX.symm.isSimpleGroup
        let eG : S ≃* ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma X m) := e.trans eX
        have hperf : commutator ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma X m) = ⊤ :=
          CFSG.LieType.Ree.ReeTag.commutator_reeGamma_eq_top hm1 hXcard
        have hmap : (commutator S).map eG.toMonoidHom = ⊤ := by
          rw [map_commutator_eq]
          have hran : eG.toMonoidHom.range = ⊤ := by
            simpa using eG.range_eq_top
          rw [hran]
          exact hperf
        intro hcomm
        haveI := hcomm
        have hbot : commutator S = ⊥ := commutator_eq_bot (G := S)
        rw [hbot, Subgroup.map_bot] at hmap
        exact bot_ne_top hmap
      exact ⟨m, hv, hsimpleS, hnab, ⟨e⟩⟩
    | A n q => exact hi.1.elim
    | twistedA n q => exact hi.1.elim
    | B n q => exact hi.1.elim
    | C n q => exact hi.1.elim
    | D n q => exact hi.1.elim
    | twistedD n q => exact hi.1.elim
    | E6 q => exact hi.1.elim
    | E7 q => exact hi.1.elim
    | E8 q => exact hi.1.elim
    | F4 q => exact hi.1.elim
    | G2 q => exact hi.1.elim
    | twistedE6 q => exact hi.1.elim
    | trialityD4 q => exact hi.1.elim
    | suzuki m => exact hi.1.elim
    | reeG2 m => exact hi.1.elim
    | tits => exact hi.1.elim
  | cyclic p hp' => exact hi.elim
  | alternating n hn => exact hi.elim
  | sporadic s => exact hi.elim

theorem reeF4Norm_of
    (hL : CatLayer) :
    SimpleNormModel (CharTwoOf isReeF4Idx) := by
  intro S _ _ p hp hp2 hcat _
  have hcat2 : catalogIs S (onLie fun d => d.characteristic = 2) := by
    rcases hcat with ⟨i, hi, he⟩
    cases i with
    | lie dd => exact ⟨.lie dd, hi.2, he⟩
    | cyclic p hp' => exact hi.elim
    | alternating n hn => exact hi.elim
    | sporadic s => exact hi.elim
  obtain ⟨m, hv, -, -, ⟨eS⟩⟩ := reeF4_extract hcat
  have hm1 : 1 ≤ m :=
    (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hR := CFSG.LieType.SeitzGeneration.reeTitsModel_cat_reeF4 hv
  obtain ⟨K, hfield, hfinite, hchar, hKcard, ⟨eK⟩⟩ :=
    CFSG.LieType.ChevTwo.Semi.exists_mulEquiv_reeGamma hm1 hR
  letI := hfield
  letI := hfinite
  haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := hchar
  haveI : Finite ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K m) := Subtype.finite
  let e : S ≃* ↥(CFSG.LieType.Ree.ReeTag.F4.reeGamma K m) := eS.trans eK
  intro x y hx1 hxp hyp hc J hJ
  have hPL : PerfectInLayer (MulAut.conj x) := hL S p hp hp2 hcat2 x hx1 hxp
  have hCN : CompNormal (MulAut.conj x) := by
    refine CFSG.LocalAnalysis.GLTheoremA.S267.Gen.compNormal_of_congr e
      (MulAut.conj x) ?_
    have hcongr : MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) :=
      CFSG.mulAut_congr_conj e x
    rw [hcongr]
    haveI : Fact p.Prime := ⟨hp⟩
    have hx' : orderOf (e x) = p :=
      (orderOf_injective e.toMonoidHom e.injective x).trans (orderOf_eq_prime hxp hx1)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rcases eq_or_lt_of_le hp3 with h3 | h3
    · rw [← h3] at hx'
      exact compNormal_reeF4_three hm1 hKcard (e x) hx'
    · exact compNormal_reeF4_of_three_lt hm1 hKcard hp h3 (e x) hx'
  exact mem_normalizer_glaPComponent_of_compNormal hc hPL hCN hJ

end CFSG.LocalAnalysis.GLTheoremA.F151

end
