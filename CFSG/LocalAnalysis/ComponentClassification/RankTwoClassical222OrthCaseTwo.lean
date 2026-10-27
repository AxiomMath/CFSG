module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthTwoC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222OrthTwoRot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222TwoB

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard CFSG.LieType.Universal.Spin
open scoped Matrix

section Groups

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  [Finite K] [CharP K 2]

theorem noPairOrbit_orth_two (Q : QuadraticForm K (ι → K)) (q : (ι → K) → K) (hq : ⇑Q = q)
    (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (ι → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hK : Nat.card K = 2) (hι : 7 ≤ Fintype.card ι)
    {e : rankTwoQuot A ≃* StatedProj (StatedOmega q)} (hZ : Odd (Nat.card (center ↥A)))
    {p : G} (hp2 : orderOf p = 2) {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2) :
    NoPairOrbit A p := by
  have hev : Even (commRank M) := by
    subst hq
    exact even_commRank_of_mem_statedOmega Q hQ hpM.2.1
  have hr0 : commRank M ≠ 0 := by
    intro h
    apply sub_one_ne_zero (M := M) fun h1 => by rw [h1, orderOf_one] at hM2; omega
    refine Matrix.ext_iff_mulVec.mpr fun v => ?_
    have h1 : ((M : Matrix ι ι K) - 1) *ᵥ v ∈
        LinearMap.range ((M : Matrix ι ι K) - 1).mulVecLin := ⟨v, rfl⟩
    rw [Submodule.finrank_eq_zero.mp h] at h1
    rw [(Submodule.mem_bot K).mp h1, zero_mulVec]
  by_cases h2 : commRank M = 2
  · exact noPairOrbit_rankTwo_orth_two Q q hq hQ hT hK hι hZ hp2 hpM hM2 h2
  have h4 : 4 ≤ commRank M := by
    obtain ⟨r, hr⟩ := hev
    omega
  by_cases hsing : ∀ v, Q (((M : Matrix ι ι K) - 1) *ᵥ v) = 0
  · exact noPairOrbit_typeA_orth_two Q q hq hQ hT hK hZ hp2 hpM hM2 hsing h4
  · push Not at hsing
    exact noPairOrbit_typeC_orth_two Q q hq hQ hT hK hZ hp2 hpM hM2 hsing h4

end Groups

theorem orthCaseIITwo : OrthCaseIITwo := by
  intro G _ _ A D hD _ hZ hq t u hconf
  refine hconf.not_noPairOrbit ?_
  have ht2 : orderOf t = 2 := orderOf_eq_prime hconf.t_sq hconf.t_ne_one
  obtain ⟨ℓ, hℓ⟩ := D.exists_hasRank hZ hconf.mem_t ht2
  cases D with
  | orthPlus n m hn hm K hK e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, -⟩ := hℓ
    have hK2 : Nat.card K = 2 := by
      have h2 : 2 ^ m = 2 := hq
      rw [hK, h2]
    exact noPairOrbit_orth_two (quadPlus n K) (StatedQuadPlus n K) (coe_quadPlus n K)
      (nondegenerate_polarBilin_quadPlus n K) (exists_totallySingular_quadPlus (by omega) K) hK2
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ ht2 hM hM2
  | orthMinus n m hn hm K hK b c hbc e =>
    have := charP_two_of_card hK
    obtain ⟨-, M, hM, hM2, -⟩ := hℓ
    have hK2 : Nat.card K = 2 := by
      have h2 : 2 ^ m = 2 := hq
      rw [hK, h2]
    exact noPairOrbit_orth_two (quadMinus n K b c) (StatedQuadMinus n K b c)
      (coe_quadMinus n K b c) (nondegenerate_polarBilin_quadMinus_of_finite n K hbc)
      (exists_totallySingular_quadMinus hn K b c) hK2
      (by simp only [Fintype.card_sum, Fintype.card_fin]; omega) hZ ht2 hM hM2
  | linear => simp [ClassicalModel.family] at hD
  | unitary => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD

end CFSG.ComponentClassification.RankTwoClassical
