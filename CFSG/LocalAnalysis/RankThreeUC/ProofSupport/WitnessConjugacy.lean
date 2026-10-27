module


public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace ProofSupport

namespace WitnessConjugacy

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G]

private theorem map_symm_map (e : MulAut G) (H : Subgroup G) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  simpa using map_automorphism_symm_map H e.symm

theorem map_eq (hS : Standing G) {p : ℕ} (hpA : p ∈ rankThreeSigmaA G)
    {P Q : Sylow p G} {M N : Subgroup G} (hwM : IsWitness p P M) (hwN : IsWitness p Q N)
    (g : G) (hg : g • Q = P) :
    N.map (MulAut.conj g).toMonoidHom = M := by
  set e : MulAut G := MulAut.conj g with he
  have hPe : (P : Subgroup G) = (Q : Subgroup G).map e.toMonoidHom := by
    rw [← hg]
    exact (Subgroup.pointwise_smul_def (a := e) (Q : Subgroup G))
  have hPM : (P : Subgroup G) ≤ M := hwM.sylow_le hS hpA
  have hQN : (Q : Subgroup G) ≤ N := hwN.sylow_le hS hpA
  have hrk : 3 ≤ CFSG.Open.pRank p (P : Subgroup G) := selected_sylow_rank_at_least_three hS.rank p hpA P
  have hp1 : 1 < p := (sigmaA_prime p hpA).one_lt
  have hN'2 : IsTwoLocal (N.map e.toMonoidHom) := twoLocal_map_automorphism N hwN.maxLocal.1 e
  have hPN' : (P : Subgroup G) ≤ N.map e.toMonoidHom := hPe ▸ Subgroup.map_mono hQN
  have hN'M : N.map e.toMonoidHom ≤ M := by
    refine hwM.u2 _ hN'2 ?_
    have := pRank_mono p hp1 (le_inf hPN' hPM)
    omega
  have h1 : N ≤ M.map e.symm.toMonoidHom := by
    have := Subgroup.map_mono (f := e.symm.toMonoidHom) hN'M
    rwa [map_automorphism_symm_map] at this
  have h2 := hwN.maxLocal.2 _ (twoLocal_map_automorphism M hwM.maxLocal.1 e.symm) h1
  rw [← h2, map_symm_map]

end WitnessConjugacy

end ProofSupport

end CFSG.LocalAnalysis.RankThreeUC
