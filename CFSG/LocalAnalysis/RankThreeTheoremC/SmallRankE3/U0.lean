module

public import CFSG.LocalAnalysis.RankThreeUC.CoreWitness
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15SigmaA
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem fullCoreLocal_of_theoremD1_pair (hS : Setting G) (hD1 : TheoremD1 G) {p : ℕ}
    (hsig : rankThreeSigmaA G = {p}) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) (hU : rankThreeGamma 2 p (P : Subgroup G) ≤ M) :
    FullCoreLocal G := by
  intro q hq Q N hN
  have hp : p ∈ rankThreeSigmaA G := by rw [hsig]; rfl
  have hqp : q = p := by
    rw [hsig] at hq
    exact hq
  subst hqp
  have hprime := sigmaA_prime q hp
  have hfact : Fact q.Prime := ⟨hprime⟩
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) P Q
  let φ : MulAut G := MulAut.conj g
  have hQ : (Q : Subgroup G) = (P : Subgroup G).map φ.toMonoidHom := by
    rw [← hg]
    exact sylow_conjugate_eq_map q P g
  have hN₁ : rankThreeIsMaxTwoLocal (N.map φ.symm.toMonoidHom) :=
    rankThreeIsMaxTwoLocal_map hN.1 φ.symm
  have hQN : (Q : Subgroup G) ≤ N := (sylow_le_of_isCoreMaxLocal hS hp hN).1
  have hPN₁ : (P : Subgroup G) ≤ N.map φ.symm.toMonoidHom := by
    have h := Subgroup.map_mono (f := φ.symm.toMonoidHom) hQN
    rwa [hQ, map_automorphism_symm_map] at h
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  have heq : N.map φ.symm.toMonoidHom = M :=
    eq_of_isMaxTwoLocal_of_three_le_pRank hD1 hp hM hPM hP3.ge hN₁ hPN₁
  have hNM : N = M.map φ.toMonoidHom := by
    rw [← heq]
    have h := map_automorphism_symm_map N φ.symm
    rw [MulEquiv.symm_symm] at h
    exact h.symm
  rw [hQ, hNM, ← CFSG.LocalAnalysis.RankThreeUC.gamma_map_automorphism 2 q hprime.one_lt]
  exact Subgroup.map_mono hU

theorem fullCoreLocal_of_theoremD1_situation_three (hS : Setting G) (hD1 : TheoremD1 G)
    {P : Sylow 3 G} {M : Subgroup G} (hs : SmallRankSituation G 3 P M) : FullCoreLocal G :=
  fullCoreLocal_of_theoremD1_pair hS hD1
    (CFSG.LocalAnalysis.RankThreeUC.S15.sigmaA_eq_three hS.rank hs.mem_sigmaA)
    hs.isCoreMaxLocal hs.gamma_two_le

theorem fullCoreLocal_of_theoremD1_situation_five (hS : Setting G) (hD1 : TheoremD1 G)
    {P : Sylow 5 G} {M : Subgroup G} (hs : SmallRankSituation G 5 P M) : FullCoreLocal G :=
  fullCoreLocal_of_theoremD1_pair hS hD1
    (CFSG.LocalAnalysis.RankThreeUC.S15.sigmaA_eq_five hS.rank hs.mem_sigmaA)
    hs.isCoreMaxLocal hs.gamma_two_le

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
