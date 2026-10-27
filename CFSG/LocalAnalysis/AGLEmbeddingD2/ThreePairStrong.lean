module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairSolvable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Data
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

@[expose] def D2PairStrongThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], D2Global G → D1For G →
    ∀ (P : Sylow 3 G) (M A H R : Subgroup G), D2Escape 3 P M A H R → D2EscapeMax 3 P M R →
    3 ∈ GLBBetaFour G → AGLPair 3 M H R → GLBStronglyEmbedded 3 M → D2PerfectThreePrime H M →
    False

theorem d2IndexCaseAt_three_of_pairStrong {i : TauCeti.CFSGIndex}
    (hpair : D2PairAt i fun p => p = 3) (hsolv : D2SolvableAt i fun p => p = 3)
    (h84 : Asc81bEightFour) (hD2 : D1NoXBlock)
    (hS : D2PairStrongThree) : D2IndexCaseAt i fun p => p = 3 := by
  intro G _ _ hglob hD1 p hp3 P M A H R hesc hmax hβ Rbar K hRbar hK he
  subst hp3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU := hpair _ 3 rfl Rbar _ _ K hK he
  have hpr : AGLPair 3 M H R := hesc.toPair hglob.toAGLGlobal
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
  exact hS G hglob hD1 P M A H R hesc hmax hβ hpr
    (hesc.stronglyEmbedded_of_pair hglob hβ hpr h84 (hD2.noXBlockFor hglob.toD1Global))
    (d2PerfectThreePrime_of_isSolvable (hsolv _ 3 rfl Rbar _ _ K hK he))

theorem d2IndexCaseStrongAt_altSix_of_pairStrong (hS : D2PairStrongThree) :
    D2IndexCaseStrongAt (.alternating 6 (by norm_num)) := by
  intro G _ _ hglob hD1 P M A H R hesc hmax hβ hstr Rbar K hRbar hK he
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU := d2PairAt_altSix _ 3 rfl Rbar _ _ K hK he
  have hpr : AGLPair 3 M H R := hesc.toPair hglob.toAGLGlobal
    (hesc.twoCore_inf_eq_of_primeCore_inf_eq (hesc.primeCore_inf_eq_iff.mpr hU))
  exact hS G hglob hD1 P M A H R hesc hmax hβ hpr hstr
    (d2PerfectThreePrime_of_isSolvable (d2SolvableAt_altSix _ 3 rfl Rbar _ _ K hK he))

theorem d2IndexCaseStrongAt_u3_of_pairStrong (hKU : UnitaryBorelKFacts) (hS : D2PairStrongThree)
    (d : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.exponent = 1 ∧ d.1 = .twistedA 2 q)
    (h3 : d.1.characteristic = 3) : D2IndexCaseStrongAt (.lie d) := by
  intro G _ _ hglob hD1 P M A H R hesc hmax hβ hstr Rbar K hRbar hK ⟨e⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hdu, hnu⟩ := isUnitaryIndex_of_case h3.symm hd
  have hdata :=
    hesc.heisData_of_u3 hKU hglob.toAGLGlobal hRbar hK hdu hnu e
  exact hS G hglob hD1 P M A H R hesc hmax hβ hdata.pair hstr
    (d2PerfectThreePrime_of_le hdata.perfect_le)

end CFSG.AGLEmbeddingD2
