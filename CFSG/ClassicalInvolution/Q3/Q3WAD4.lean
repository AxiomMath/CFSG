module

public import CFSG.ClassicalInvolution.Q3.Q3WATwinDRow
public import CFSG.ClassicalInvolution.Q3.Generation
import all CFSG.ClassicalInvolution.RouteD.MultiD4

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

section Group

variable {G : Type} [Group G] [Finite G]

theorem psi_torusD_eq3 (hn3 : 3 ≤ 4) (h2 : (2 : GaloisField 3 1) ≠ 0)
    (ψ : spinGroup (quadPlus 4 (GaloisField 3 1)) →* G) (hker : ψ.ker ≤ Subgroup.center _)
    (k : Fin 4) (hk : k ≠ 1) {M : Subgroup G} {w : G}
    (hM : (rankOne (plusDatum 4 (GaloisField 3 1) hn3).rootGroup k).map ψ = M)
    (hw : IsClassicalMember3 M w) : ψ (torusD (GaloisField 3 1) hn3 k (-1)) = w := by
  have hmem : torusD (GaloisField 3 1) hn3 k (-1) ∈
      rankOne (plusDatum 4 (GaloisField 3 1) hn3).rootGroup k := by
    rw [torusD_apply]
    exact CFSG.LieType.Universal.Spin.PlusCT.rankOneD_mem_rankOne hn3 k _
  obtain ⟨φ, hφ⟩ := hw.exists_chart
  refine hφ.eq_of_central ⟨?_, ?_, ?_, ?_⟩ hw.isCentralInvolution
  · rw [← hM]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h1
    exact torusD_not_mem_center hn3 h2 k hk (hker (MonoidHom.mem_ker.mpr h1))
  · rw [← map_mul, torusD_neg_one_mul_self, map_one]
  · intro m hm
    rw [← hM] at hm
    obtain ⟨r, hr, rfl⟩ := hm
    have hr' : r ∈ (rankOneD (GaloisField 3 1) hn3 k).range := by
      rw [← CFSG.LieType.Universal.Spin.PlusCT.rankOne_plusRootGroup hn3 k]
      exact hr
    obtain ⟨M', rfl⟩ := hr'
    rw [← map_mul, ← map_mul, torusD_apply, ← map_mul, ← map_mul, diagSL2_neg_one_mul]


theorem d4Frame3_holds :
    ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), ConjInvariant Ω →
      ∀ (K a₁ a₂ β : Subgroup G) (z w₁ w₂ : G), K ∈ Ω → a₁ ∈ Ω → a₂ ∈ Ω → β ∈ Ω →
        IsClassicalMember3 K z → IsClassicalMember3 a₁ w₁ → IsClassicalMember3 a₂ w₂ →
        Commutes K a₁ → Commutes K a₂ → Commutes a₁ a₂ →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W a₁ β) →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W a₂ β) →
          ∃ a₃ ∈ Ω, Commutes a₃ K ∧ Commutes a₃ a₁ ∧ Commutes a₃ a₂ ∧
            IsClassicalMember3 a₃ (z * w₁ * w₂) := by
  intro G _ _ Ω hΩ K a₁ a₂ β z w₁ w₂ hK ha₁ ha₂ hβ hz hw₁ hw₂ hKa₁ hKa₂ ha₁a₂
    ⟨W₀, hpK⟩ ⟨W₁, hp₁⟩ ⟨W₂, hp₂⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨hp, le_rfl, le_rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  let U : Fin 4 → Subgroup G := ![K, β, a₁, a₂]
  have hcomm : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i → Commutes (U i) (U j) := by
    intro i j hij h1' h2'
    fin_cases i <;> fin_cases j <;> simp [edgeD, U] at hij h1' h2' ⊢
    all_goals first | exact hKa₁ | exact hKa₂ | exact ha₁a₂ | exact hKa₁.symm | exact hKa₂.symm |
      exact ha₁a₂.symm
  have hpair : ∀ i j : Fin 4, edgeD 4 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [edgeD, U] at hij ⊢
    all_goals first | exact ⟨W₀, hpK⟩ | exact ⟨W₁, hp₁.symm⟩ | exact ⟨W₂, hp₂.symm⟩
  obtain ⟨ψ, hker, -, hψ⟩ := exists_psi_of_chain_plus3 hadm U hcomm hpair
  have hfundM : CFSG.ClassicalInvolution.ModelFacts.IsFundTag .POmegaPlus := trivial
  have hscT : FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 hp).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass _ _ 3 _ _ hfundM hadm (by decide)
      (by decide)
  have e1 := modelUniv_POmegaPlus_eq (p := 3) (f := 1) hn3
  have hscT' : FundamentalSingleClass .POmegaPlus (plusDatum 4 (GaloisField 3 1) hn3) := by
    revert hscT
    rw [e1]
    exact id
  obtain ⟨g, hg⟩ := hscT' (rankOne (plusDatum 4 (GaloisField 3 1) hn3).rootGroup (0 : Fin 4))
    (rankOne_mem_fundamentalSubgroups_plusDatum hn3 (0 : Fin 4)) (rootθD 4 (GaloisField 3 1) hn3)
    (rootθD_mem_fundamentalSubgroups hn3 le_rfl)
  have ha3 : (rootθD 4 (GaloisField 3 1) hn3).map ψ = conjSub (ψ g) K := by
    rw [hg, ← conjSub_map, hψ 0]
    rfl
  refine ⟨conjSub (ψ g) K, hΩ _ _ hK, ?_, ?_, ?_, ?_⟩
  · have := commutes_map_of_commutes ψ (commutes_rootθD_rankOne hn3 le_rfl (k := 0) (by decide))
    rw [ha3, hψ 0] at this
    exact this
  · have := commutes_map_of_commutes ψ (commutes_rootθD_rankOne hn3 le_rfl (k := 2) (by decide))
    rw [ha3, hψ 2] at this
    exact this
  · have := commutes_map_of_commutes ψ (commutes_rootθD_rankOne hn3 le_rfl (k := 3) (by decide))
    rw [ha3, hψ 3] at this
    exact this
  · have hcl := hz.conj (ψ g)
    have hz0 := psi_torusD_eq3 hn3 h2 ψ hker 0 (by decide) (hψ 0) hz
    have hz2 := psi_torusD_eq3 hn3 h2 ψ hker 2 (by decide) (hψ 2) hw₁
    have hz3 := psi_torusD_eq3 hn3 h2 ψ hker 3 (by decide) (hψ 3) hw₂
    have hθ : ψ (zTheta (GaloisField 3 1) hn3) = z * w₁ * w₂ := by
      rw [zTheta_eq, map_mul, map_mul, hz0, hz2, hz3]
    have hcent : IsCentralInvolution (conjSub (ψ g) K) (z * w₁ * w₂) := by
      rw [← ha3, ← hθ]
      refine ⟨Subgroup.mem_map_of_mem _ (zTheta_mem hn3), ?_, ?_, ?_⟩
      · intro h1
        exact zTheta_not_mem_center hn3 h2 (hker (MonoidHom.mem_ker.mpr h1))
      · rw [← map_mul, zTheta, ← map_mul]
        simp
      · rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, ← map_mul, zTheta_central hn3 x hx]
    obtain ⟨φ, hφ⟩ := hcl.exists_chart
    have hzeq := hφ.eq_of_central hcl.isCentralInvolution hcent
    rw [hzeq] at hcl
    exact hcl

end Group

end CFSG.ClassicalInvolution.Q3.Q3W
