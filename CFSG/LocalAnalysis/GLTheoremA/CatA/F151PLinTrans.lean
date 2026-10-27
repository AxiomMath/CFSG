module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs

import CFSG.Assembly.GL83StatedBridge
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I171

private theorem linNormTrans_aux (hiso : ShapeModelNormIso) (hmodel : LinNormModel)
    (S : Type) [Group S] [Finite S] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcat : catalogIs S (onLie (CharTwoOf KD264Lie.isLinearIdx)))
    (hshape : ¬ catalogIs S (onLie (I171LieShape p))) :
    ShapeModelNormAt S p := by
  obtain ⟨d, hv, hP, ⟨eS⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | A n q =>
    have hq2 : q.p = 2 := by
      have h := hP
      simp only [CharTwoOf, KD264Lie.isLinearIdx,
        TauCeti.LieTypeIndex.characteristic_A] at h
      exact h.2
    have hLM := CFSG.Models.lieModel_A n q hv eS
    have hsc : StatedClassicalModel S .PSL (n + 1) 2 q.exponent := by
      have := CFSG.Models.LieModel.statedClassicalModel hLM (t := .PSL) (by decide)
      simpa [hq2] using this
    obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hsc
    letI := hKf
    letI := hKfin
    have hn : 1 ≤ n := by
      have hval := hv
      rw [TauCeti.LieTypeIndex.valid_iff] at hval
      exact ((TauCeti.LieTypeIndex.inStandardRange_iff (.A n q)).mp hval.1).1
    have hN : 2 ≤ n + 1 := by omega
    have hnot : ¬ p ∣ Nat.gcd (n + 1) (2 ^ q.exponent - 1) := by
      intro hdiv
      apply hshape
      refine ⟨.lie ⟨.A n q, hv⟩, ?_, ⟨eS⟩⟩
      show I171LieShape p (.A n q)
      refine ⟨hq2, ?_⟩
      simpa [TauCeti.PrimePower.card_def, hq2] using hdiv
    have hmodelAt := hmodel (n + 1) q.exponent K hN hKcard p hp hp2 hnot
    have hcast : CFSG.Assembly.LargeEvenProj
          (CFSG.Assembly.LargeEvenSLGroup (Fin (n + 1)) K)
        ≃* CFSG.Assembly.LargeEvenProj (CFSG.Open.StatedSL (n + 1) K) :=
      MulEquiv.cast (M := fun H => CFSG.Assembly.LargeEvenProj H)
        (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (n + 1))
    haveI : Finite
        (CFSG.Assembly.LargeEvenProj (CFSG.Assembly.LargeEvenSLGroup (Fin (n + 1)) K)) :=
      Finite.of_equiv S (hcast.trans eK.symm).symm.toEquiv
    exact hiso _ S (hcast.trans eK.symm) p hmodelAt
  | _ => simp [CharTwoOf, KD264Lie.isLinearIdx] at hP

private theorem uniNormTrans_aux (hiso : ShapeModelNormIso) (hmodel : UniNormModel)
    (S : Type) [Group S] [Finite S] (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcat : catalogIs S (onLie (CharTwoOf KD264Lie.isUnitaryIdx)))
    (hshape : ¬ catalogIs S (onLie (I171LieShape p))) :
    ShapeModelNormAt S p := by
  obtain ⟨d, hv, hP, ⟨eS⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hcat
  cases d with
  | twistedA n q =>
    have hq2 : q.p = 2 := by
      have h := hP
      simp only [CharTwoOf, KD264Lie.isUnitaryIdx,
        TauCeti.LieTypeIndex.characteristic_twistedA] at h
      exact h.2
    have hLM := CFSG.Models.lieModel_twistedA n q hv eS
    have hsc : StatedClassicalModel S .PSU (n + 1) 2 q.exponent := by
      have hch : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n q, hv⟩ = 2 := by
        have h := TauCeti.LieTypeIndex.characteristic_twistedA n q
        rw [hq2] at h
        exact h
      have hfe : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n q, hv⟩ = q.exponent :=
        TauCeti.LieTypeIndex.fieldExponent_twistedA n q
      have h := CFSG.Models.LieModel.statedClassicalModel hLM (t := .PSU) (by decide)
      rwa [hch, hfe] at h
    obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hsc
    letI := hKf
    letI := hKfin
    have hn : 2 ≤ n := by
      have hval := hv
      rw [TauCeti.LieTypeIndex.valid_iff] at hval
      exact ((TauCeti.LieTypeIndex.inStandardRange_iff (.twistedA n q)).mp hval.1).1
    have hN : 3 ≤ n + 1 := by omega
    have hnot : ¬ p ∣ Nat.gcd (n + 1) (2 ^ q.exponent + 1) := by
      intro hdiv
      apply hshape
      refine ⟨.lie ⟨.twistedA n q, hv⟩, ?_, ⟨eS⟩⟩
      show I171LieShape p (.twistedA n q)
      refine ⟨hq2, ?_⟩
      simpa [TauCeti.PrimePower.card_def, hq2] using hdiv
    have hfield : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 q.exponent K :=
      CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hKcard
    have hmodelAt := hmodel (n + 1) q.exponent K hfield hN p hp hp2 hnot
    have hmodelAt' : ShapeModelNormAt
        (CFSG.Open.StatedProj (CFSG.Open.StatedSU (n + 1) (2 ^ q.exponent) K)) p :=
      hmodelAt
    haveI : Finite
        (CFSG.Open.StatedProj (CFSG.Open.StatedSU (n + 1) (2 ^ q.exponent) K)) :=
      Finite.of_equiv S eK.toEquiv
    exact hiso _ S eK.symm p hmodelAt'
  | _ => simp [CharTwoOf, KD264Lie.isUnitaryIdx] at hP

theorem linNormTrans_holds : LinNormTrans := by
  intro hiso hmodel S _ _ p hp hp2 hcat hshape
  exact linNormTrans_aux hiso hmodel S p hp hp2 hcat hshape

theorem uniNormTrans_holds : UniNormTrans := by
  intro hiso hmodel S _ _ p hp hp2 hcat hshape
  exact uniNormTrans_aux hiso hmodel S p hp hp2 hcat hshape

end CFSG.LocalAnalysis.GLTheoremA.F151

end
