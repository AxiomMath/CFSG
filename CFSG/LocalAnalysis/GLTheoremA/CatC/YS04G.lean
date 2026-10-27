module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04LinUni
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04E6
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.YS04G

theorem kd26g_lnEps (hG : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (Subgroup.center K)) {n q : ℕ} {lin : Bool}
    (hS : IsLnEps (K ⧸ Subgroup.center K) n q lin) (hpg : p ∣ Nat.gcd n (qEps lin q)) :
    n - 3 ≤ GLATwoLocalRank p K ∧
      (Nat.card (Subgroup.center K) = p ^ (Nat.gcd n (qEps lin q)).factorization p →
        n - 2 ≤ GLATwoLocalRank p K) := by
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ qEps lin q := hpg.trans (Nat.gcd_dvd_right _ _)
  cases lin with
  | true =>
    obtain ⟨m, F, _, _, hmn, hFq, ⟨e0⟩⟩ := exists_psl_of_isLnEps hS
    subst hmn
    have hq' : qEps true q = Nat.card F - 1 := by simp [qEps, hFq]
    rw [hq'] at hpq ⊢
    exact kd26g_linear hG hK hp hp2 hZ e0 hpn hpq
  | false =>
    obtain ⟨m, ℓ, f, F, _, hU, hmn, hℓq, h3, ⟨e0⟩⟩ := exists_psu_of_isLnEps hS
    subst hmn
    subst hℓq
    have hq' : qEps false (ℓ ^ f) = ℓ ^ f + 1 := by simp [qEps]
    rw [hq'] at hpq ⊢
    exact kd26g_unitary hG hK hp hp2 hZ hU e0 h3 hpn hpq

section E6Certs


theorem kd26g_of_griess (hG : GriessAllModelsStatement) : KD26g := by
  intro K _ _ hK p hp hp2 hZ _
  refine ⟨fun n q lin hS hpg => kd26g_lnEps hG hK hp hp2 hZ hS hpg, fun q lin hS hp3 h3 => ?_⟩
  subst hp3
  exact kd26g_e6 hZ hS h3

end E6Certs

section AllCerts


theorem kd26g_holds : KD26g :=
  kd26g_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

end AllCerts

end CFSG.LocalAnalysis.GLTheoremA
