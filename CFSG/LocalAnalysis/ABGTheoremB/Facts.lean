module

public import CFSG.LocalAnalysis.ABGTheoremB.Setting

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise

universe u

namespace Setting

variable {G : Type u} [Group G] (σ : Setting G)

structure NStructure [Finite G] : Prop where
  L_eq : σ.L = σ.L₀ ⊔ (σ.D ⊓ Subgroup.centralizer (σ.T : Set G))
  N_oddCore_of_cover : ∀ K : Subgroup G, K ≤ σ.N → (σ.L₀ : Set G) ⊆ (K : Set G) * σ.ON →
    oddCoreIn K ≤ σ.ON
  N_solvRad : solvRadIn σ.N = σ.ON ⊔ centerOf (σ.S : Subgroup G)
  N_minimalNormal : ∀ K : Subgroup G, K ≤ σ.N → σ.N ≤ Subgroup.normalizer (K : Set G) →
    ¬ K ≤ solvRadIn σ.N → σ.L₀ ≤ K ⊔ solvRadIn σ.N
  N_coverTransfer : ∀ K : Subgroup G, K ≤ σ.N → σ.L₀ ≤ K ⊔ solvRadIn σ.N →
    (σ.L₀ : Set G) ⊆ (K : Set G) * σ.ON
  N_constraint_criterion : ∀ r : ℕ, r.Prime → r ∣ Nat.card σ.ON → ∀ R : Subgroup G,
    IsSylowOf r R σ.ON → (σ.S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) →
      (σ.Constrained r ↔ IsSylowOf 2 (centerOf (σ.S : Subgroup G) ⊓
        Subgroup.centralizer (R : Set G)) (σ.N ⊓ Subgroup.centralizer (R : Set G)))
  center_S_eq_center_D : centerOf (σ.S : Subgroup G) = centerOf σ.D
  center_involution_of_sylow : ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) →
    σ.x ∈ centerOf (S₁ : Subgroup G) ∧
      ∀ z ∈ centerOf (S₁ : Subgroup G), orderOf z = 2 → z = σ.x
  normal_le_center_of_inf_D : ∀ S₁ : Sylow 2 G, σ.D ≤ (S₁ : Subgroup G) → ∀ X : Subgroup G,
    X ≤ S₁ → (S₁ : Subgroup G) ≤ Subgroup.normalizer (X : Set G) → X ⊓ σ.D ≤ centerOf σ.D →
      X ≤ centerOf (S₁ : Subgroup G)

structure ChapterIIFacts [Finite G] : Prop extends σ.NStructure where
  localQD_charPower : ∀ H : Subgroup G, (∃ r : ℕ, r.Prime ∧ IsPLocal r H) → IsQDGroup H →
    ∀ r : ℕ, HasQDCharPower H r → r = 3 ∨ r = 5 ∨ (r ∣ σ.q ∧ r ≠ σ.q)
  workingI : WorkingHypothesisI G
  cover_qgroup : ∀ H : Subgroup G, σ.T ≤ H → oddCoreIn H ≠ ⊥ →
    (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON →
      HasQCharPower H σ.q ∧ oddCoreIn H ⊔ (H ⊓ σ.N) = H
  not_qd_of_cover : ∀ H : Subgroup G, σ.T ≤ H → oddCoreIn H ≠ ⊥ →
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆ (H : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) →
      ¬ IsQDGroup H
  qd_or_d_of_three : ∀ H : Subgroup G, σ.T ≤ H → (σ.D ≤ H ∨ σ.height = 1) →
    3 ∣ automizerIndex (σ.T.subgroupOf H) → IsQDGroup H ∨ IsDGroupWrt (σ.T.subgroupOf H)
  fusion_cases : ∀ H : Subgroup G, H ≠ ⊤ → σ.T ≤ H → (σ.D ≤ H ∨ σ.height = 1) →
    IsQDGroup H ∨ IsQGroup H ∨ IsDGroup H ∨ HasNormalPComplement 2 H
  fusion_disjoint : ∀ H : Subgroup G,
    (IsQDGroup H → ¬ IsQGroup H) ∧ (IsQDGroup H → ¬ IsDGroup H) ∧
      (IsQDGroup H → ¬ HasNormalPComplement 2 H) ∧ (IsQGroup H → ¬ IsDGroup H) ∧
      (IsQGroup H → ¬ HasNormalPComplement 2 H) ∧ (IsDGroup H → ¬ HasNormalPComplement 2 H)
  qgroup_constraint_criterion : ∀ H : Subgroup G, σ.D ≤ H → oddCoreIn H ≠ ⊥ →
    (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON → ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ H →
      ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ P : Subgroup G,
        IsSylowOf r P (oddCoreIn H) → S₁ ≤ Subgroup.normalizer (P : Set G) →
          (PConstrainedWithin r H (CFSG.solvableRadical H) ↔
              IsSylowOf 2 (centerOf S₁ ⊓ Subgroup.centralizer (P : Set G))
                (H ⊓ Subgroup.centralizer (P : Set G))) ∧
            (PConstrainedWithin r H (CFSG.oddCore H) ↔
              Odd (Nat.card (H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)))
  qgroup_solvRad : ∀ H : Subgroup G, σ.D ≤ H → oddCoreIn H ≠ ⊥ →
    (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON → solvRadIn H = oddCoreIn H ⊔ centerOf σ.D
  automizer_T : automizerIndex σ.T = 6
  qgroup_no_three : ∀ K : Subgroup G, IsQGroup K → ∀ T₁ : Subgroup G, T₁ ≤ K →
    IsKleinFour T₁ → ¬ 3 ∣ automizerIndex (T₁.subgroupOf K)
  normal_contains_three : ∀ H : Subgroup G, σ.D ≤ H →
    (IsQDGroup H ∨ (IsDGroupWrt (σ.T.subgroupOf H) ∧ ¬ Group.IsSolvable H)) →
      ∀ X : Subgroup G, X ≤ H → H ≤ Subgroup.normalizer (X : Set G) → σ.T ≤ X →
        ∃ T₁ : Subgroup G, T₁ ≤ X ∧ IsKleinFour T₁ ∧ 3 ∣ automizerIndex (T₁.subgroupOf X)
  solvable_dgroup_signalizer : ∀ H : Subgroup G, σ.D ≤ H → IsDGroupWrt (σ.T.subgroupOf H) →
    Group.IsSolvable H → ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ X : Subgroup G, X ≤ H → IsPGroup r X →
      σ.T ≤ Subgroup.normalizer (X : Set G) → X ≤ oddCoreIn H

end Setting

end CFSG.ABGTheoremB
