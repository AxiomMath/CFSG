module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRest10
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLinearDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodUnitaryDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodSymplectic
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodD4Graph
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodF4
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodG2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodSRT
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodTrialityMain
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxExc2
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

structure KD264LieRest11 : Prop where
  e6 : LieInnGood fun d => ∃ q, d = .E6 q
  e7 : LieInnGood fun d => ∃ q, d = .E7 q
  e8 : LieInnGood fun d => ∃ q, d = .E8 q
  twE6 : LieInnGood fun d => ∃ q, d = .twistedE6 q
  a1 : LieCompAlg isLinearIdx
  a2 : LieCompAlg isUnitaryIdx
  a3 : LieCompAlg isClassicalBCDIdx
  a4 : LieCompAlg isTrialityIdx
  a5 : LieCompAlg isExcUntwistedIdx
  a6 : LieCompAlg isExcTwistedIdx

section Rest11


theorem kd264InnGood_of_exc (hE6 : LieInnGood fun d => ∃ q, d = .E6 q)
    (hE7 : LieInnGood fun d => ∃ q, d = .E7 q) (hE8 : LieInnGood fun d => ∃ q, d = .E8 q)
    (hTE6 : LieInnGood fun d => ∃ q, d = .twistedE6 q) : KD264InnGood := by
  rw [kd264InnGood_iff]
  rintro ⟨e, he⟩ p hp hp2 hpc h3 h5 -
  cases e with
  | A r q => exact lieInnGood_linear ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | twistedA r q => exact lieInnGood_unitary ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | B r q =>
    by_cases h : r = 2 ∨ q.p = 2
    · exact lieInnGood_symplectic ⟨_, he⟩ p hp hp2 hpc h3 h5 h
    · push_neg at h
      exact lieInnGood_orthogonal ⟨_, he⟩ p hp hp2 hpc h3 h5 h
  | C r q => exact lieInnGood_symplectic ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | D r q =>
    by_cases h : r = 4
    · subst h
      exact lieInnGood_D4 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
    · exact lieInnGood_orthogonal ⟨_, he⟩ p hp hp2 hpc h3 h5 h
  | twistedD r q => exact lieInnGood_orthogonal ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | E6 q => exact hE6 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
  | E7 q => exact hE7 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
  | E8 q => exact hE8 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
  | F4 q => exact lieInnGood_F4 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
  | G2 q => exact lieInnGood_G2 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
  | twistedE6 q => exact hTE6 ⟨_, he⟩ p hp hp2 hpc h3 h5 ⟨q, rfl⟩
  | trialityD4 q => exact lieInnGood_triality ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | suzuki m => exact lieInnGood_suzRee ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | reeG2 m => exact lieInnGood_suzRee ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | reeF4 m => exact lieInnGood_suzRee ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial
  | tits => exact lieInnGood_suzRee ⟨_, he⟩ p hp hp2 hpc h3 h5 trivial

theorem kd264CompIdx_of_alg (a1 : LieCompAlg isLinearIdx) (a2 : LieCompAlg isUnitaryIdx)
    (a3 : LieCompAlg isClassicalBCDIdx) (a4 : LieCompAlg isTrialityIdx) (a5 : LieCompAlg isExcUntwistedIdx)
    (a6 : LieCompAlg isExcTwistedIdx) : KD264CompIdx :=
  kd264CompIdx_of_families CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    lieCompIdx_linear lieCompIdx_unitary lieCompIdx_classicalBCD lieCompIdx_triality lieCompIdx_excUntwisted
    lieCompIdx_excTwisted a1 a2 a3 a4 a5 a6

theorem kd264LieRest10_of_rest11 (h : KD264LieRest11) : KD264LieRest10 :=
  ⟨kd264InnGood_of_exc h.e6 h.e7 h.e8 h.twE6, kd264CompIdx_of_alg h.a1 h.a2 h.a3 h.a4 h.a5 h.a6⟩

end Rest11

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
