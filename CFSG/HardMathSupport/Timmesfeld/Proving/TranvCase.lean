module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.GLTheoremB.BlockDefs

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {X : Type*} [Group X]

theorem transv_conclusion_of_mem_centralizer {p : ℕ} {K B T D : Subgroup X}
    (hcomp : GLAPComponent p K K) (hPi : LocalAnalysis.GLTheoremB.IsPiGroup p ↥K)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hTK : ¬ T ≤ Subgroup.centralizer (K : Set X)) {d : X} (hdD : d ∈ D) (hd1 : d ≠ 1)
    (hdK : K ≤ Subgroup.centralizer ({d} : Set X)) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X), (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧ LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧ K = ⨆ d ∈ 𝒟, Kf d := by
  refine ⟨{d}, fun _ => K, ?_, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact ⟨hdD, hd1⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    have hKC : K ⊓ Subgroup.centralizer ({x} : Set X) = K := by
      rw [hx]
      exact inf_eq_left.mpr hdK
    refine ⟨?_, sup_le hBN hTN, hPi, hTK⟩
    rw [hKC]
    exact hcomp
  · simp

theorem inducedAutGroup_eq_bot_of_le_centralizer {T K : Subgroup X}
    (hT : T ≤ Subgroup.centralizer (K : Set X)) : inducedAutGroup T K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_bot]
  have hyC : ((y : Subgroup.normalizer (K : Set X)) : X) ∈ Subgroup.centralizer (K : Set X) :=
    hT (Subgroup.mem_subgroupOf.mp hy)
  have hker : y ∈ (K.normalizerMonoidHom).ker := by
    rw [Subgroup.normalizerMonoidHom_ker]
    exact Subgroup.mem_subgroupOf.mpr hyC
  exact MonoidHom.mem_ker.mp hker

theorem not_le_centralizer_of_natCard_inducedAutGroup {T K : Subgroup X}
    (h : Nat.card (inducedAutGroup T K) = 2) : ¬ T ≤ Subgroup.centralizer (K : Set X) := by
  intro hT
  rw [inducedAutGroup_eq_bot_of_le_centralizer hT, Subgroup.card_bot] at h
  exact absurd h (by norm_num)

end CFSG.HardMathSupport.Timmesfeld.Proving

end
