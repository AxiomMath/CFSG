module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoverFork

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.LieType CFSG.LieType.Universal
open CFSG.Timmesfeld (edgeD)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadPlus)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] {m : ℕ}
  {e : L ≃* matrixProjectiveDerived (coordinateQuadPlus (m + 1) K)} {ι : K →+* F}

theorem hfork_of_forall_cover (hm : 2 ≤ m) (hC : ∀ k, PlusFieldCover e ι k)
    (hK : 4 ≤ Nat.card K) (hF : 4 ≤ Nat.card F) :
    ∀ i j : Fin (m + 1), i.val + 2 = m + 1 → j.val + 1 = m + 1 →
      plusNode e i ≤ centralizer (plusNode e j : Set G) :=
  fun _ _ hi hj => plusNode_fork_le_centralizer hm (hC 0) hK hF hi hj

theorem exists_weakCT_plus_of_forall_cover {f : ℕ} (hm : 4 ≤ m) (hKf : Nat.card K = 2 ^ f)
    (hK : 4 ≤ Nat.card K) (hF : Nat.card F = 2 ^ (2 * f)) (hC : ∀ k, PlusFieldCover e ι k)
    {G₀ : Subgroup G} (hG₀ : G₀ = ⨆ j, plusNode e j) {t : G}
    (ht : t ∈ centralizer (L : Set G)) :
    ∃ Ψ : spinGroup (Spin.quadPlus (m + 1) F) →* G₀, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) .POmegaPlus (m + 1) 2 (2 * f) ∧
      (∀ j, (CurtisTits.rankOne (Spin.plusDatum (m + 1) F (by omega)).rootGroup j).map Ψ =
        (plusNode e j).subgroupOf G₀) ∧
      t ∈ normalizer (G₀ : Set G) := by
  have hf2 : 2 ≤ f := by
    by_contra h
    have hf1 : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hF16 : 16 ≤ Nat.card F := by
    rw [hF]
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hfork := hfork_of_forall_cover (by omega) hC hK (by omega)
  have hcomm : ∀ i j : Fin (m + 1), i ≠ j → ¬ edgeD (m + 1) i j → ¬ edgeD (m + 1) j i →
      plusNode e i ≤ centralizer (plusNode e j : Set G) := by
    intro i j hij h1 h2
    by_cases hf1 : i.val + 2 = m + 1 ∧ j.val + 1 = m + 1
    · exact hfork i j hf1.1 hf1.2
    by_cases hf2' : j.val + 2 = m + 1 ∧ i.val + 1 = m + 1
    · exact Subgroup.le_centralizer_iff.1 (hfork j i hf2'.1 hf2'.2)
    exact plusNode_le_centralizer hm hC hK (by omega) (disjoint_plusNodeSet hij h1 h2 hf1 hf2')
  obtain ⟨Ψ, hΨs, hΨk, hq, hmodel, hroot⟩ := exists_weakCT_spinPlus_of_pieces (n := m + 1)
    (by omega) (by omega) (by omega) hF (plusNode e) hG₀ hcomm
    (fun i j hij => exists_theta_plusNode (by omega) hC hK (by omega) hij)
  refine ⟨Ψ, hΨs, hΨk, hq, hmodel, hroot, ?_⟩
  rw [hG₀]
  exact mem_normalizer_iSup_plusNode e ht

end CFSG.SeitzReduction.OmegaPilot
