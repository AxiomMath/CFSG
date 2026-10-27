module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeakCaseTwo
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallAlphaThree
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanThreeCoverSpor
public import CFSG.LocalAnalysis.AGLEmbedding.KFactsAlphaWeak

public section

namespace CFSG.AGLEmbedding

open CFSG.Open


theorem pow_three_eq_one_of_sylow_exponent_three {K : Type} [Group K] [Finite K]
    (hZ : IsPGroup 3 (Subgroup.center K)) (T : Sylow 3 K)
    (hexp : ∀ t ∈ (T : Subgroup K), t ^ 3 = 1) (x : K ⧸ Subgroup.center K)
    (hx : ∃ n : ℕ, x ^ 3 ^ n = 1) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨n, hn⟩ := hx
  have hyZ : y ^ 3 ^ n ∈ Subgroup.center K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hn
  obtain ⟨m, hm⟩ := hZ ⟨_, hyZ⟩
  have hy : y ^ 3 ^ (n + m) = 1 := by
    have h1 : (y ^ 3 ^ n) ^ 3 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    rw [pow_add, pow_mul]
    exact h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hy)
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q T
  have hyQ : y ∈ (Q : Subgroup K) := hQ (Subgroup.mem_zpowers y)
  have hgy : g * y * g⁻¹ ∈ (T : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨y, hyQ, by simp [MulAut.smul_def]⟩
  have h3 : (g * y * g⁻¹) ^ 3 = 1 := hexp _ hgy
  have hy3 : y ^ 3 = 1 := by
    rw [conj_pow] at h3
    have := congrArg (fun t => g⁻¹ * t * g) h3
    simpa [mul_assoc] using this
  rw [← QuotientGroup.mk_pow, hy3, QuotientGroup.mk_one]

theorem kFactCaseTwoAlphaElimThree_of (hα : KFactAlphaW) (hK3 : KFactAlphaThreeWeak) :
    KFactCaseTwoAlphaElimThreeW := by
  intro K _ _ hK hcat hZ hZp hZc A L _ hL f hf T
  rcases hα K hK hcat 3 Nat.prime_three (by norm_num) hZ hZp hZc T with
    ha | ha' | hb | hc | ⟨hout, he1 | ⟨hexp, -⟩ | he3⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha')
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr hc))
  · rcases hK3 K hK hcat hZ hZp hZc hout T (Or.inl he1) with hw | hJ
    · exact Or.inr (Or.inr (Or.inr hw))
    · exact hJ.elim fun e => (KFactProofs.ThreeCover.false_J3 hZp hL A f hf e).elim
  · exact (KFactProofs.ThreeCover.false_of_exponent_three hL
      (pow_three_eq_one_of_sylow_exponent_three hZp T hexp) A f hf).elim
  · rcases hK3 K hK hcat hZ hZp hZc hout T (Or.inr he3) with hw | hJ
    · exact Or.inr (Or.inr (Or.inr hw))
    · exact hJ.elim fun e => (KFactProofs.ThreeCover.false_J3 hZp hL A f hf e).elim

end CFSG.AGLEmbedding
