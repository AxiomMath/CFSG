module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.InvConj

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup
open scoped Pointwise

theorem factorization_five : (877800 : ℕ).factorization 5 = 2 := by
  have h : (877800 : ℕ) = 5 ^ 2 * 35112 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have hn : ¬ 5 ∣ 35112 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hn, h5.factorization_pow]
  simp

theorem exists_conj_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {C P Q : Subgroup G} (hPC : P ≤ C) (hP : Nat.card P = p ^ (Nat.card C).factorization p)
    (hQC : Q ≤ C) (hQ : IsPGroup p Q) : ∃ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ P := by
  have hP' : Nat.card (P.subgroupOf C) = p ^ (Nat.card C).factorization p := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  let P₁ : Sylow p C := Sylow.ofCard (P.subgroupOf C) hP'
  have hQ' : IsPGroup p (Q.subgroupOf C) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQC).symm
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C S P₁
  refine ⟨c, c.2, fun q hq => ?_⟩
  have hqS : (⟨q, hQC hq⟩ : C) ∈ (S : Subgroup C) := hS (Subgroup.mem_subgroupOf.2 hq)
  have h1 : (MulAut.conj c : MulAut C) • (⟨q, hQC hq⟩ : C) ∈
      (MulAut.conj c : MulAut C) • (S : Subgroup C) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hqS
  have h2 : (MulAut.conj c : MulAut C) • (S : Subgroup C) = (P₁ : Subgroup C) := by
    rw [← Sylow.coe_subgroup_smul, hc]
  rw [h2] at h1
  have h3 : (MulAut.conj c : MulAut C) • (⟨q, hQC hq⟩ : C) ∈ P.subgroupOf C := h1
  exact Subgroup.mem_subgroupOf.1 h3

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
