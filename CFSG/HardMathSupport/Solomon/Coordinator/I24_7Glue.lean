module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
open scoped commutatorElement

theorem i247_card_iff {A : Type*} [Group A] [Finite A] {S : Subgroup A} (hS : IsPGroup 3 S) :
    Nat.card S = 3 ^ (Nat.card A).factorization 3 ↔ ¬ 3 ∣ S.index := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hS
  have hidx : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcard : Nat.card A = 3 ^ a * S.index := by
    rw [← ha]
    exact (Subgroup.card_mul_index S).symm
  have hfac : (Nat.card A).factorization 3 = a + S.index.factorization 3 := by
    rw [hcard, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hidx, Finsupp.add_apply,
      Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
  constructor
  · intro h
    rw [ha] at h
    have h1 : a = (Nat.card A).factorization 3 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
    have h2 : S.index.factorization 3 = 0 := by omega
    intro hd
    have := (hp.dvd_iff_one_le_factorization hidx).1 hd
    omega
  · intro h
    have h2 : S.index.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h
    rw [ha, hfac, h2, add_zero]

theorem i247_perfect_of_layer {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (h : GLAPLayer 5 K = K) : commutator ↥K = ⊤ := by
  have h1 : K ≤ ⁅K, K⁆ := by
    conv_lhs => rw [← h]
    refine sSup_le fun J hJ => ?_
    have := glaPComponent_perfect hJ
    calc J = ⁅J, J⁆ := this.symm
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hJ.1 hJ.1
  rw [commutator_def, eq_top_iff]
  intro x _
  have hx : (x : G) ∈ ⁅K, K⁆ := h1 x.2
  have h2 : ⁅K, K⁆ = (⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ : Subgroup ↥K).map K.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  rw [h2] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := Subtype.ext hyx
  rwa [this] at hy

end CFSG.HardMathSupport.Solomon.Coordinator
