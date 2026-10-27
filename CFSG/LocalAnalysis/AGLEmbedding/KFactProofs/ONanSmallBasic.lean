module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
public import CFSG.Foundations.SteinbergCAGeneratedCoreNodes

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open

theorem rank_le_two_of_autRank {K : Type} [Group K] [Finite K] (hs : IsSimpleGroup K)
    (hnab : ∃ a b : K, a * b ≠ b * a) {p : ℕ} (hp : p.Prime)
    (hAut : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2) : Open.pRank p (⊤ : Subgroup K) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have := pRank_le_pRank_mulAut_of_nonabelian hnab hp.one_lt (k := 3) (by omega)
  omega

theorem isSmallStrongP_of_autRank (h : KFactSmallIdent) {K : Type} [Group K] [Finite K]
    (hs : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a) (hc : IsCatalogGroup K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (T : Sylow p K) (hT : ¬ IsCyclic (T : Subgroup K))
    (hΓ : GLBCore p 1 (T : Subgroup K) ≠ ⊤)
    (hAut : Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2) :
    IsSmallStrongP p K :=
  h K hs hnab hc p hp hp2 T hT hΓ
    ((CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp ⊤).le.trans
      (rank_le_two_of_autRank hs hnab hp hAut))

section Sylow

variable {K : Type*} [Group K] [Finite K]

theorem pow_eq_one_of_card_sq {p : ℕ} (hp : p.Prime) {T : Subgroup K} (hT : Nat.card T = p ^ 2)
    (hnc : ¬ IsCyclic T) (t : K) (ht : t ∈ T) : t ^ p = 1 := by
  by_contra h
  apply hnc
  have hdvd : orderOf (⟨t, ht⟩ : T) ∣ p ^ 2 := hT ▸ orderOf_dvd_natCard _
  have hnd : ¬ orderOf (⟨t, ht⟩ : T) ∣ p := by
    intro hd
    apply h
    have h1 : (⟨t, ht⟩ : T) ^ p = 1 := orderOf_dvd_iff_pow_eq_one.1 hd
    simpa using congrArg Subtype.val h1
  have hord : orderOf (⟨t, ht⟩ : T) = p ^ 2 := by
    rcases (Nat.dvd_prime_pow hp).1 hdvd with ⟨k, hk, hk'⟩
    interval_cases k
    · exact absurd (by rw [hk']; simp) hnd
    · exact absurd (by rw [hk']; simp) hnd
    · exact hk'
  exact isCyclic_of_orderOf_eq_card _ (by rw [hord, hT])

theorem pow_eq_one_of_sylow_exp {p : ℕ} [Fact p.Prime] (T : Sylow p K)
    (hT : ∀ t ∈ (T : Subgroup K), t ^ p = 1) (t : K) (ht : ∃ n : ℕ, t ^ p ^ n = 1) :
    t ^ p = 1 := by
  obtain ⟨n, hn⟩ := ht
  have hpg : IsPGroup p (Subgroup.zpowers t) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).1 (orderOf_dvd_of_pow_eq_one hn)
    exact ⟨k, hk⟩
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T P
  have htP : t ∈ (P : Subgroup K) := hP (Subgroup.mem_zpowers t)
  have h2 : ((g • T : Sylow p K) : Subgroup K) = (T : Subgroup K).map (MulAut.conj g).toMonoidHom :=
    by rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]; rfl
  rw [← hg, h2, Subgroup.mem_map] at htP
  obtain ⟨s, hs, rfl⟩ := htP
  have := hT s hs
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [conj_pow, this, mul_one, mul_inv_cancel]

end Sylow

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
