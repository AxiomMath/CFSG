module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1InnerRow
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1Field
public import CFSG.RankThree.PartOne.KF4.F4Pointwise
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofBurgE1ToralData

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem one_le_of_card_eq_pow {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hK : Nat.card K = p ^ f) : 1 ≤ f := by
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at hK
    exact absurd hK (Finite.one_lt_card).ne'
  · exact h0

theorem burgOddCoreRow_F4
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : BurgOddCoreRow (adjointGroup .F4 K) := by
  intro α hα
  have hf := one_le_of_card_eq_pow hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  have hidx : ∀ k : Fin (Tag.rank .F4),
      (k = RankThree.PartOne.KF4.f4Index 0 ∨ k = RankThree.PartOne.KF4.f4Index 1) ∨
        (k = RankThree.PartOne.KF4.f4Index 2 ∨ k = RankThree.PartOne.KF4.f4Index 3) := by
    decide
  rcases odd_F4_E8_G2_involution_inner_or_quadratic (Or.inl rfl) hKodd hα2 with
    ⟨g, a, hαg⟩ | ⟨q, e, hq, he, hKe, δ, hδ, g, a, hαg⟩
  · refine burgOddCoreFor_innerDiagonal (Or.inr (Or.inl rfl)) hK2 (fun _ => True)
      (fun b hb => (exists_mem_rootCharKernel_of_isRoot_add (i := 0) (j := 1) hb
        (mem_rootFinset.1 (by decide +kernel))).imp fun γ hγ => ⟨hγ, fun _ _ _ => trivial⟩)
      (fun b hb hb1 => pPrimeCore_toralCentralizer_F4 hK2 hb hb1)
      (fun k _ h hU Z hZ η hη _ => RankThree.PartOne.KF4.F4_descended_root_SL2_pointwise_inner K
        hp hp2 hf hK (AlgebraicClosure K) k (hidx k) 1 h hU Z hZ η hη) hαg hα
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    exact burgOddCoreFor_quadratic_field .F4 (by decide) hq hp2 he hKe δ hδ
      (fun k _ _ hk => (odd_F4_and_nonexceptional_G2_automorphism_normal_form hq hp2
        hk.choose_spec.1 k hk.choose_spec.2 .F4 (Or.inl rfl)).1) hαg hα

end CFSG.ComponentClassification.CatLeafProof
