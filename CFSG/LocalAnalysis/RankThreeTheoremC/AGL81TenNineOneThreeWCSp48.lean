module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieSp4F1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

namespace Sp48

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.LevelLieSp4F CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  (spLinearAutGroup spSemilinearAutGroup fieldAut)
open Subgroup

theorem sp48_inner_of_fix (β : MulAut TF) (hβ3 : β ^ 3 = 1) (T : Subgroup TF)
    (hT : Nat.card T = 81) (hfix : ∀ t ∈ T, β t = t) : β ∈ innTF := by
  by_contra hβin
  obtain ⟨-, -, -, -, -, -, -, hIdx, hRel, hfield⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent
      (ℓ := 2) (f := 3) (r := 2) Nat.prime_two (by norm_num) (by norm_num) card_F8_pow
  have hDinn : spLinearAutGroup 2 F8 ≤ innTF := by
    apply Subgroup.relIndex_eq_one.1
    have h1 : Nat.gcd 2 (2 ^ 3 - 1) = 1 := by norm_num
    rw [h1] at hRel
    exact Nat.dvd_one.1 hRel
  have hEn : (spSemilinearAutGroup 2 F8).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hIdx with h1 | h1
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h1
  have hβE : β ∈ spSemilinearAutGroup 2 F8 := by
    have h3 : orderOf (QuotientGroup.mk' (spSemilinearAutGroup 2 F8) β) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hβ3, map_one])
    have h2 : orderOf (QuotientGroup.mk' (spSemilinearAutGroup 2 F8) β) ∣ 2 :=
      (_root_.orderOf_dvd_natCard _).trans hIdx
    have h1 : orderOf (QuotientGroup.mk' (spSemilinearAutGroup 2 F8) β) = 1 :=
      Nat.dvd_one.1 (by simpa using Nat.dvd_gcd h3 h2)
    exact (QuotientGroup.eq_one_iff β).1 (orderOf_eq_one_iff.1 h1)
  have hβD : β ∉ spLinearAutGroup 2 F8 := fun h => hβin (hDinn h)
  have hβ1 : β ≠ 1 := fun h => hβin (h ▸ (innTF).one_mem)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
  obtain ⟨-, σ, hσ, -, h, hhD, hβeq⟩ := hfield 3 Nat.prime_three β hβE hβD hord
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 (hDinn hhD)
  have hβform : β = MulAut.conj x * fieldAut 2 F8 σ * MulAut.conj x⁻¹ := by
    rw [hβeq, ← hx, map_inv]
  obtain ⟨-, -, -, -, -, hmem, -, -, hS6, -, -, -, -, -⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.symplectic_prime_subfield_fixed_group_and_full_centralizer_odd
      (K := F8) (ℓ := 2) (p := 3) (f := 3) (r := 2) Nat.prime_two Nat.prime_three (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) card_F8_pow σ hσ
  obtain ⟨-, -, h720⟩ := hS6 ⟨rfl, by norm_num⟩
  have hfixeq : fixSubgroup β = GLBConj x⁻¹
      (CFSG.RankThree.CASymplecticSubfield.subfieldFixedGroup F8 2 σ) := by
    rw [hβform]
    exact fix_conj_form x _ _ hmem
  have hcard : Nat.card (fixSubgroup β) = 720 := by
    rw [hfixeq, ← h720]
    refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj x).toEquiv fun y => ?_).symm
    rw [mem_gLBConj]
    simp [MulAut.conj_apply, mul_assoc]
  have hle : T ≤ fixSubgroup β := fun t ht => (mem_fixSubgroup).2 (hfix t ht)
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hT, hcard] at hdvd
  norm_num at hdvd

theorem factorization_sp48 : (3 ^ 4 * 13045760 : ℕ).factorization 3 = 4 := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

end Sp48

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
