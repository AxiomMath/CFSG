module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtToralIb

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.barM_cover (h : D1PhaseThree p P M H R) {V : Subgroup G}
    (hVHM : V ≤ H ⊓ M) (hVp : ⁅V, V⁆ = V) {L : Subgroup G}
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) :
    ⁅barM M V, barM M V⁆ = barM M V ∧
      barM M V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∧
      barM M V ≤ Subgroup.normalizer (barM M (pCoreOf 2 H ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.toMSideAt.barM_cover (hVHM.trans h.inf_eq_inf_normalizer_twoCore.le) hVp hVL

theorem D1PhaseThree.zbar_mem_sup_of_cover (h : D1PhaseThree p P M H R)
    (hSch : KFactCatalogSchreier) {V : Subgroup G} (hVHM : V ≤ H ⊓ M) (hVp : ⁅V, V⁆ = V)
    {z : G} (hzV : z ∈ V) (hzM : z ∈ M) {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hVL : V ≤ Subgroup.normalizer (L : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
      barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
  h.toMSideAt.zbar_mem_sup_of_cover (fun hM => h.not_le (hM ▸ le_top)) hSch
    (hVHM.trans h.inf_eq_inf_normalizer_twoCore.le) hVp hzV hzM hL hVL

theorem D1PhaseThree.false_of_toral_three_ib (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hSch : KFactCatalogSchreier)
    (hK : CitedBlockToralThreeIb)
    (hperf : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ¬ 3 ^ 2 ∣ Nat.card V)
    {z : G} (hzR : z ∈ R) (hzo : orderOf z = 3) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hcov : ∃ V : Subgroup G, V ≤ H ⊓ M ∧ ⁅V, V⁆ = V ∧ z ∈ V ∧
      ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → V ≤ Subgroup.normalizer (L : Set G))
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {T : Subgroup G} (hzT : z ∉ T) (hRz : ∀ r ∈ R, z * r = r * z) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hfus : ∀ r ∈ R, r ∉ T → r ∈ fusionSet R z)
    (hinv : ∀ t ∈ T, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹)
    (hE : ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) : False := by
  subst hp3
  have hKS := h.inf_eq_inf_normalizer_twoCore
  obtain ⟨V, hVHM, hVp, hzV, hVN⟩ := hcov
  refine h.toMSideAt.false_of_toral_three_ib (fun hM => h.not_le (hM ▸ le_top)) h.le_M
    h.normalizer_le h84 h85 h93 hD2 hSch hK (fun W hW hWp => hperf W (hKS ▸ hW) hWp) hzR hzo ?_
    ⟨V, hKS ▸ hVHM, hVp, hzV, hVN⟩ hsyl hzT hRz hexp hfus hinv hE
  rw [h.normalizer_twoCore_H]
  exact fun x hx => hCz hx.2

end CFSG.AGLEmbedding
