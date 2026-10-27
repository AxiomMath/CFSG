module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeKFacts
import CFSG.LocalAnalysis.AGLEmbedding.MSideAtToral

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_toral_three (h : D1PhaseThree p P M H R) (hp3 : p = 3)
    (h84 : Asc81bEightFour) (h85 : Asc81bEightFive) (h86 : Asc81bEightSix)
    (h93 : Asc81bNineThree) (hD2 : D1NoXBlock) (hK : CitedBlockToralThree)
    (hperf : ∀ Y : Subgroup G, Y ≤ H ⊓ M → ⁅Y, Y⁆ = Y → Nat.Coprime 3 (Nat.card Y))
    {z : G} (hzR : z ∈ R) (hzo : orderOf z = 3) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hsyl : ∃ S : Sylow 3 ↥(M ⊓ Subgroup.centralizer ({z} : Set G)),
      (S : Subgroup _).map (M ⊓ Subgroup.centralizer ({z} : Set G)).subtype = R)
    {T : Subgroup G} (hzT : z ∉ T) (hRz : ∀ r ∈ R, z * r = r * z) (hexp : ∀ r ∈ R, r ^ 3 = 1)
    (hfus : ∀ r ∈ R, r ∉ T → r ∈ fusionSet R z)
    (hinv : ∀ t ∈ T, t ≠ 1 → ∃ n ∈ M, n * z * n⁻¹ = z ∧ n * t * n⁻¹ = t⁻¹)
    (hE : ∃ E : Subgroup G, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) : False := by
  subst hp3
  have hKS := h.inf_eq_inf_normalizer_twoCore
  refine h.toMSideAt.false_of_toral_three h.le_M h.normalizer_le h84 h85 h86 h93 hD2 hK
    (fun Y hY => hperf Y (hKS ▸ hY)) hzR hzo ?_ hsyl hzT hRz hexp hfus hinv hE
  rw [h.normalizer_twoCore_H]
  exact fun x hx => hCz hx.2

end CFSG.AGLEmbedding
