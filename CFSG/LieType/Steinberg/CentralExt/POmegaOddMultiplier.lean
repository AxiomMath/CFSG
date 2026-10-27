module

public import CFSG.LieType.Steinberg.CentralExt.SpinOddCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CliffordAlgebra

namespace CFSG.LieType.Steinberg.CentralExt.SpinOddClosed

variable {n : ℕ} {K : Type} [Field K]

theorem card_ker_spinToStatedProj_quadOdd (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n) :
    Nat.card (spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)).ker = 2 := by
  obtain ⟨-, hkerZ, -⟩ := spinToStatedProj_quadOdd h2 hn
  have hodd : Odd (Fintype.card (Fin n ⊕ Fin n ⊕ Unit)) := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
    exact ⟨n, by ring⟩
  have hle := comap_statedScalars_le_ker_of_odd hodd h2 (coe_quadOdd n K)
    (exists_map_ne_zero_of_hypPair _ (oddPair K (⟨0, by omega⟩ : Fin n)))
    (range_spinMatrix_quadOdd h2 hn)
  have hge : (spinMatrix (quadOdd n K)).ker ≤ (StatedScalars _ K).comap (spinMatrix (quadOdd n K)) :=
    fun x hx => by
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hx]
      exact one_mem _
  have heq : (spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)).ker =
      (spinMatrix (quadOdd n K)).ker := by
    rw [hkerZ]
    exact le_antisymm hle hge
  have : Invertible (2 : K) := invertibleOfNonzero h2
  have hc : Nat.card (spinMatrix (quadOdd n K)).ker =
      ((spinMatrix (quadOdd n K)).ker : Set (spinGroup (quadOdd n K))).ncard :=
    Nat.card_coe_set_eq _
  rw [heq, hc, coe_ker_spinMatrix_quadOdd h2, Set.ncard_pair (spinGroup.negOne_ne_one _ _).symm]

theorem pomegaOdd_hopfMultiplier [Finite K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ n)
    (hK : 5 ≤ Nat.card K) :
    commutator (StatedProj (StatedOmega (StatedQuadOdd n K))) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier (StatedProj (StatedOmega (StatedQuadOdd n K))) ≃*
        Multiplicative (ZMod 2)) := by
  set q := spinToStatedProj (quadOdd n K) (range_spinMatrix_quadOdd h2 hn)
  obtain ⟨hq, -, hker⟩ := spinToStatedProj_quadOdd h2 hn
  have : Group.IsPerfect (spinGroup (quadOdd n K)) := isPerfect_spinGroup_quadOdd h2 hn
  have hperf : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadOdd n K))) :=
    Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  have e1 : CFSG.RankThree.PerfectCover.hopfMultiplier
      (StatedProj (StatedOmega (StatedQuadOdd n K))) ≃* q.ker :=
    MulEquiv.ofBijective _ (SL2Closed.hopfMultiplierToKer_bijective q hq hker.le
      fun π hπ hcen => spinOdd_exists_section_of_central h2 hn hK hπ hcen)
  have hcard := card_ker_spinToStatedProj_quadOdd h2 hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic q.ker := isCyclic_of_prime_card hcard
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e1.trans ((zmodCyclicMulEquiv hcyc).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hcard).toAddEquiv)))⟩

end CFSG.LieType.Steinberg.CentralExt.SpinOddClosed
