module

public import CFSG.RankThree.PartOne.CTP.SporadicNoncommFi24
public import CFSG.Sporadic.Bridge.Fi24Surj
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoSporMax
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem fi24Seven_sylow_facts
    {K : Type} [Group K] [Finite K]
    (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group)) :
    (Nat.card K).factorization 7 = 3 ∧
      ∀ T : Sylow 7 K, ∃ x ∈ (T : Subgroup K), ∃ y ∈ (T : Subgroup K), x * y ≠ y * x := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨eC⟩ := nonempty_mulEquiv_carrier_of_sporadicIndex (s := .Fi24Prime)
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv hK
  refine ⟨?_, fun T => ?_⟩
  · rw [Nat.card_congr eC.toEquiv]
    show (Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime).factorization 7 = 3
    rw [CFSG.Sporadic.Fi24.card_Fi24prime,
      show (1255205709190661721292800 : ℕ) = 7 ^ 3 * 3659491863529626009600 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 7), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain ⟨x, y, -, -, hxy, hQ⟩ := (CFSG.RankThree.PartOne.CTP.hasNoncommPair_Fi24_seven).map
    eC.symm.toMonoidHom eC.symm.injective
  obtain ⟨P, hP⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P T
  have hmem : ∀ z ∈ Subgroup.closure ({x, y} : Set K),
      (MulAut.conj g) • z ∈ (T : Subgroup K) := by
    intro z hz
    rw [← hg]
    exact Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) (P : Subgroup K) (hP hz)
  refine ⟨_, hmem x (Subgroup.subset_closure (by simp)), _,
    hmem y (Subgroup.subset_closure (by simp)), fun h => hxy ?_⟩
  apply (MulAut.conj g).injective
  rw [map_mul, map_mul]
  exact h

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
