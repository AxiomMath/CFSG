module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocal
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open

theorem odd_orderOf_mul_of_isTwoPrimeTwo {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y}
    (hK : IsTwoPrimeTwo K) {a b : Y} (ha : a ∈ K) (hb : b ∈ K) (hao : Odd (orderOf a))
    (hbo : Odd (orderOf b)) : Odd (orderOf (a * b)) := by
  obtain ⟨O, hOK, hOn, hodd, hq⟩ := hK
  have key : ∀ c : Y, c ∈ K → Odd (orderOf c) → c ∈ O := by
    intro c hc hco
    obtain ⟨k, hk⟩ := hq c hc
    have hcop : Nat.Coprime (2 ^ k) (orderOf c) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hco)
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hr]
    exact O.pow_mem hk r
  have haO := key a ha hao
  have hbO := key b hb hbo
  have habO : a * b ∈ O := O.mul_mem haO hbO
  have hdvd : orderOf (⟨a * b, habO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk] at hdvd
  exact Odd.of_dvd_nat hodd hdvd

theorem exists_normal_twoPrimeTwo_of_subnormal {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : K.IsSubnormal) (hK22 : IsTwoPrimeTwo K) :
    ∃ M : Subgroup G, K ≤ M ∧ M.Normal ∧ IsTwoPrimeTwo M := by
  obtain ⟨O, hOK, hOn, hodd, hq⟩ := hK22
  set N : Subgroup G := pPrimeCore 2 G with hN
  have hNn : N.Normal := pPrimeCore_normal
  have hNodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOsub : O.IsSubnormal := Subgroup.IsSubnormal.step O K hOK hK hOn
  have hON : O ≤ N :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 2 hOsub (Nat.coprime_two_left.mpr hodd)
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hKp : IsPGroup 2 (K.map π) := by
    rintro ⟨_, k, hk, rfl⟩
    obtain ⟨j, hj⟩ := hq k hk
    refine ⟨j, Subtype.ext ?_⟩
    change π k ^ 2 ^ j = 1
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hON hj
  have hKsub : CFSG.Open.IsSubnormal (K.map π) ⊤ := by
    have h1 := (CFSG.Open.IsSubnormal.of_mathlib hK).map π
    rwa [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective π hπ] at h1
  have hKle : K.map π ≤ pCore 2 (G ⧸ N) := by
    have h1 := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hKsub hKp
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_top_eq_pCore] at h1
  refine ⟨(pCore 2 (G ⧸ N)).comap π, fun k hk => hKle (Subgroup.mem_map_of_mem π hk),
    (pCore_normal (p := 2) (G := G ⧸ N)).comap π, N, ?_, ?_, hNodd, ?_⟩
  · intro n hn
    rw [Subgroup.mem_comap]
    have : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [this]
    exact Subgroup.one_mem _
  · rw [Subgroup.normal_subgroupOf_iff (fun n hn => by
      rw [Subgroup.mem_comap]
      have : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [this]
      exact Subgroup.one_mem _)]
    intro n m hn _
    exact hNn.conj_mem n hn m
  · intro g hg
    rw [Subgroup.mem_comap] at hg
    obtain ⟨j, hj⟩ := (pCore_isPGroup (p := 2) (G := G ⧸ N)) ⟨π g, hg⟩
    refine ⟨j, ?_⟩
    have hj' : π g ^ 2 ^ j = 1 := congrArg Subtype.val hj
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj'
    exact hj'

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
