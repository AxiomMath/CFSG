module

public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.SigmaPrimeCoverage
import CFSG.FeitThompson.Local.SigmaCoreConjugation
import CFSG.FeitThompson.OddOrder.SigmaCentralizerTransitivity
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Definitions.KernelFilteredIrreducibleCharacters
public import CFSG.FeitThompson.Representations.TensorAndDualCharacters
public import Mathlib
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup Pointwise

universe u

variable {G : Type*} [Group G] [Finite G]

theorem exists_le_natCard_eq_pow_factorization_of_not_dvd_index {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (h : ¬ p ∣ H.index) :
    ∃ Q ≤ H, Nat.card ↥Q = p ^ (Nat.card G).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow p ↥H))
  refine ⟨(Q₀ : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _,
    natCard_eq_pow_factorization_iff.2 ⟨Q₀.2.map _, ?_⟩⟩
  rw [Subgroup.index_map_subtype]
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h' | h'
  · exact Q₀.not_dvd_index h'
  · exact h h'

theorem exists_isCoatom_le_sigmaCore_of_isPGroup [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hPbot : P ≠ ⊥) (hPp : IsPGroup p ↥P) :
    ∃ L : Subgroup G, IsCoatom L ∧ P ≤ sigmaCore L := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn, hcard⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := ↥P) hPp).1 ((nontrivial_iff_ne_bot P).2 hPbot)
  have hdvd : p ∣ Nat.card G :=
    dvd_trans (by rw [hcard]; exact dvd_pow_self p hn.ne') P.card_subgroup_dvd_card
  obtain ⟨T, hT, hpT⟩ := exists_isCoatom_mem_sigmaPrimes hna hp hdvd
  have hidxT : ¬ p ∣ (sigmaCore T).index := fun h =>
    isPiNumber_compl_iff.1 (isHallSubgroup_sigmaCore hna hodd hsolv hT).index p
      (Nat.mem_primeFactors.2 ⟨hp, h, Subgroup.index_ne_zero_of_finite⟩) hpT
  obtain ⟨Q, hQle, hQcard⟩ := exists_le_natCard_eq_pow_factorization_of_not_dvd_index hp hidxT
  obtain ⟨g, hg⟩ := exists_le_conj_smul_of_isPGroup hQcard hPp
  refine ⟨MulAut.conj g • T, isCoatom_conj_smul hT g, ?_⟩
  rw [sigmaCore_conj_smul]
  exact hg.trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.2 hQle)

theorem FPF_p_subgroup_sigma_core_placement :
    Statements.FPF_p_subgroup_sigma_core_placement.{u} := by
  intro G _ _ hG p hp P hPbot hPp
  have := hG.isSimpleGroup
  exact exists_isCoatom_le_sigmaCore_of_isPGroup hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable_of_ne_top hp hPbot hPp

end

end CFSG.FeitThompson.Proofs
