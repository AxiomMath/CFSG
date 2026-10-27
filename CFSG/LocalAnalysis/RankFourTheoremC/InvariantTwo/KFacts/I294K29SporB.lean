module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporWit
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29SporOut
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveA
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveACover

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open Subgroup
open CFSG.Monster.B CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native CFSG.Monster.B.Pinned
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.RankThree.Native

section CertificateInstances


theorem rankThreeWitness_zFive_pow (c : ℕ) : RankThreeWitness 5 (zFive ^ c) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hR := bFiveRel
  have hP : Nat.card (FiveLocal.P xFive qFive) =
      5 ^ (Nat.card CFSG.Blueprint.NativeSporadic.B).factorization 5 := by
    rw [hR.card_P, factorization_card_B_five]
  refine RankThreeWitness.pow_of_sylow_le (Sylow.ofCard _ hP) ?_ c
  rw [Sylow.coe_ofCard]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.2 (hR.mem_H0.1 (hR.P_le_H0 hg)).2

theorem rankThreeWitness_yAFive_pow (c : ℕ) (hc : ¬ 5 ∣ c) :
    RankThreeWitness 5 (yAFive ^ c) := by
  have hR := bFiveRel
  have hy : yAFive ^ c ∈ FiveLocal.Q qFive := Subgroup.pow_mem _ yAFive_mem_Q c
  refine RankThreeWitness.of_mem_of_not_mem_zpowers (fun y hy' => hR.pow_five_of_mem hy')
    hR.z_mem ?_ hR.orderOf_z ?_ (by rw [hR.card_Q]) hy ?_
  · intro y hy'
    have hzc : (⟨zFive, hR.z_mem⟩ : FiveLocal.Q qFive) ∈ Subgroup.center (FiveLocal.Q qFive) := by
      rw [hR.center_Q_eq]
      exact Subgroup.mem_zpowers zFive
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.1 hzc ⟨y, hy'⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h1
    exact h1.symm
  · intro y hy' w hw
    have := hR.bcomm_mem (Subgroup.inv_mem _ hy') (Subgroup.inv_mem _ hw)
    simpa [bcomm, mul_assoc] using this
  · intro hz
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers).2 hz
    beta_reduce at hk
    have hcop : (orderOf yAFive).Coprime c := by
      rw [orderOf_yAFive]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hc
    have hyo : orderOf (yAFive ^ c) = 5 := by
      rw [hcop.orderOf_pow, orderOf_yAFive]
    by_cases h5 : 5 ∣ k
    · obtain ⟨m, rfl⟩ := h5
      rw [pow_mul, hR.z_pow_five, one_pow] at hk
      rw [← hk, orderOf_one] at hyo
      omega
    · have h1 := rank_bMat_pow hR.orderOf_z h5
      have h2 := rank_bMat_pow orderOf_yAFive hc
      rw [hk, h2, bFiveAK_parts.2.1, bFiveAK_parts.2.2] at h1
      omega

theorem sporadicClassWitnessNative_B_five :
    ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier .B) →
      ∀ x : S, orderOf x = 5 → RankThreeWitness 5 x := by
  intro S _ _ ⟨e⟩ x hx
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨f, -⟩ : ∃ f : S ≃* CFSG.Blueprint.NativeSporadic.B, f = e := ⟨e, rfl⟩
  have hfx : orderOf (f x) = 5 := by rw [MulEquiv.orderOf_eq]; exact hx
  obtain ⟨t, ht, hty⟩ := bFiveTwoBCover_holds (f x) hfx
  have hw : RankThreeWitness 5 (f x) := by
    obtain ⟨c, hc, g, hg | hg⟩ := exists_conj_pow_zFive_or_sFiveA hfx ht hty
    · exact RankThreeWitness.conj_eq g hg (rankThreeWitness_zFive_pow c)
    · obtain ⟨c', hc', h, hh⟩ := exists_conj_sFiveA_pow_eq_yAFive
      have h₁ : g⁻¹ * f x * g⁻¹⁻¹ = sFiveA ^ c := by rw [← hg]; group
      have h₂ : h⁻¹ * yAFive * h⁻¹⁻¹ = sFiveA ^ c' := by rw [← hh]; group
      obtain ⟨d, hd, k, hk⟩ := exists_conj_pow_of_conj_pow orderOf_sFiveA hc hc' h₁ h₂
      exact RankThreeWitness.conj_eq k hk (rankThreeWitness_yAFive_pow d hd)
  exact @RankThreeWitness.of_mulEquiv S CFSG.Blueprint.NativeSporadic.B _ inferInstance _ 5 _ f x hw

end CertificateInstances

section CertificateInstancesNative


theorem sporadicClassWitnessAt_B_five : SporadicClassWitnessAt .B 5 :=
  sporadicClassWitnessAt_of_native sporadicClassWitnessNative_B_five

end CertificateInstancesNative

end CFSG.LocalAnalysis.RankFourTheoremC
