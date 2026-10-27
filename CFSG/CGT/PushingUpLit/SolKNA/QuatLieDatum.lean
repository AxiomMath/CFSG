module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatSetup
public import CFSG.CGT.PushingUpLit.SolKNA.FrattiniCenter
public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5InvolutionRankOne
import CFSG.RankThree.GF2n.Tim78Normal
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (STSetting sylowImg)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.ClassicalInvolution.Q3 (TightDatum)
open CFSG.Assembly (pCoreOf)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.GF2n.Tim78 (eq_one_of_odd_of_isPGroup exists_odd_orderOf_pow)
open CFSG.ComponentClassification.AschbacherTheorem5.SectionSix
  (cyclic_or_quaternion_of_pRank_le_one)

variable {G : Type} [Group G]

theorem not_isCyclic_of_isQuaternionTwoGroup {P : Subgroup G} (hq : IsQuaternionTwoGroup P) :
    ¬ IsCyclic ↥P := by
  obtain ⟨n, hn, ⟨e⟩⟩ := hq
  intro hc
  have hc' : IsCyclic (QuaternionGroup (2 ^ (n - 2))) := e.isCyclic.mp hc
  have h2 : 2 ≤ 2 ^ (n - 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp hc'
  have hcard : Nat.card (QuaternionGroup (2 ^ (n - 2))) = 4 * 2 ^ (n - 2) := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  rw [hcard] at hg
  cases g with
  | a i =>
    have : orderOf (QuaternionGroup.a i : QuaternionGroup (2 ^ (n - 2))) ≤ 2 * 2 ^ (n - 2) := by
      rw [QuaternionGroup.orderOf_a]
      exact Nat.div_le_self _ _
    omega
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hg
    omega

private theorem le_sylow_of_le_normalizer_aux {P K A : Subgroup G} (hP : IsSylowOf 2 P K)
    (hAK : A ≤ K) (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hA : IsPGroup 2 A) : A ≤ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have : (Subgroup.comap K.subtype A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAK).mpr hKA
  have hle : A.subgroupOf K ≤ (Q : Subgroup K) := (hA.comap_subtype (K := K)).le_sylow_of_normal Q
  rw [hQ] at hle
  intro x hx
  exact hle (show (⟨x, hAK hx⟩ : K) ∈ A.subgroupOf K from hx)

variable [Finite G] {K : Subgroup G}

theorem eq_one_of_odd_of_cyclic {P K : Subgroup G} (hP2 : IsPGroup 2 P) (hcyc : IsCyclic ↥P)
    (hKP : K ≤ Subgroup.normalizer (P : Set G))
    (hC : K ⊓ Subgroup.centralizer (P : Set G) ≤ P) {a : G} (ha : a ∈ K)
    (hao : Odd (orderOf a)) : a = 1 := by
  have haN : a ∈ Subgroup.normalizer (P : Set G) := hKP ha
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hs : ∃ s : ℕ, Nat.card (MulAut ↥P) = 2 ^ s := by
    rw [IsCyclic.card_mulAut, hk]
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · exact ⟨0, by simp⟩
    · exact ⟨k - 1, by rw [Nat.totient_prime_pow Nat.prime_two hkpos]; simp⟩
  obtain ⟨s, hs⟩ := hs
  have h1 : orderOf (P.normalizerMonoidHom ⟨a, haN⟩) ∣ orderOf a := by
    have := orderOf_map_dvd P.normalizerMonoidHom (⟨a, haN⟩ : Subgroup.normalizer (P : Set G))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf (P.normalizerMonoidHom ⟨a, haN⟩) ∣ 2 ^ s := by
    rw [← hs]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (orderOf a) (2 ^ s) :=
    Nat.Coprime.pow_right s (Nat.coprime_two_right.mpr hao)
  have hone : orderOf (P.normalizerMonoidHom ⟨a, haN⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hker : (⟨a, haN⟩ : Subgroup.normalizer (P : Set G)) ∈ P.normalizerMonoidHom.ker :=
    orderOf_eq_one_iff.mp hone
  rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact eq_one_of_odd_of_isPGroup hP2 (hC ⟨ha, hker⟩) hao

theorem exists_tightDatum_of_quaternion (S : STSetting G K) (R : Sylow 2 K)
    (hq : IsQuaternionTwoGroup (sylowImg R)) :
    ∃ (t : G) (P : Subgroup G) (SP : Sylow 2 P), TightDatum P SP t ∧ P ≤ K ∧
      (∀ u ∈ K, orderOf u = 2 → u = t) ∧
      Subgroup.centralizer ({t} : Set G) = Subgroup.normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht2, htR, hKt, hU⟩ := exists_central_involution_of_quaternion S R hq
  have htK : t ∈ K := (Subgroup.map_subtype_le _) htR
  have hCN := centralizer_eq_normalizer_of_quaternion S R hq htK ht2
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hPK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hKP : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hsyl : IsSylowOf 2 (sylowImg R) K := ⟨R, rfl⟩
  have hPR : pCoreOf 2 K ≤ sylowImg R := le_sylow_of_le_normalizer_aux hsyl hPK hKP hP2
  have hPnc : ¬ IsCyclic ↥(pCoreOf 2 K) := by
    intro hcyc
    have hodd : ∀ a ∈ K, Odd (orderOf a) → a = 1 := fun a ha hao =>
      eq_one_of_odd_of_cyclic hP2 hcyc hKP S.inf_centralizer_pCoreOf_le ha hao
    have hK2 : IsPGroup 2 K := by
      intro c
      obtain ⟨n, hn, hn'⟩ := exists_odd_orderOf_pow (c : G)
      have hcn : (c : G) ^ 2 ^ n ∈ K := K.pow_mem c.2 _
      have := hodd _ hcn hn
      obtain ⟨k, hk⟩ := hn' this
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hKR : K = sylowImg R := hsyl.eq_of_le (Subgroup.map_subtype_le _) le_rfl hK2
    have hKP' : K ≤ pCoreOf 2 K := by
      refine CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl ?_ hK2
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    have hPS : pCoreOf 2 K = sylowImg R := le_antisymm hPR (le_trans (le_of_eq hKR.symm) hKP')
    exact not_isCyclic_of_isQuaternionTwoGroup (P := pCoreOf 2 K) (by rw [hPS]; exact hq) hcyc
  have hPq : IsQuaternionTwoGroup (pCoreOf 2 K) := by
    have hr : CFSG.Open.pRank 2 (pCoreOf 2 K) ≤ 1 :=
      (CFSG.SectionRank.pRank_mono Nat.one_lt_two hPR).trans
        (CFSG.ComponentClassification.AschbacherTheorem5.Involution.pRank_le_one_of_quaternion hq)
    rcases cyclic_or_quaternion_of_pRank_le_one hP2 hr with hc | hq'
    · exact absurd hc hPnc
    · exact hq'
  obtain ⟨n, hn, ⟨e⟩⟩ := hPq
  obtain ⟨u, hu2, -, -⟩ :=
    CFSG.ClassicalInvolution.exists_unique_involution_of_mulEquiv_quaternionGroup e
  have hu2' : orderOf (u : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have htP : t ∈ pCoreOf 2 K := by
    have h1 : (u : G) = t := hU _ (hPK u.2) hu2'
    rw [← h1]
    exact u.2
  obtain ⟨SP, hSP⟩ : ∃ SP : Sylow 2 ↥(pCoreOf 2 K), (SP : Subgroup ↥(pCoreOf 2 K)) = ⊤ := by
    have hTop : IsPGroup 2 (⊤ : Subgroup ↥(pCoreOf 2 K)) :=
      hP2.of_equiv Subgroup.topEquiv.symm
    obtain ⟨S', hS'⟩ := hTop.exists_le_sylow
    exact ⟨S', top_le_iff.mp hS'⟩
  have hPC : pCoreOf 2 K ≤ Subgroup.centralizer ({t} : Set G) := hPK.trans hKt
  refine ⟨t, pCoreOf 2 K, SP, ⟨⟨n, hn, ⟨(MulEquiv.subgroupCongr hSP).trans
    (Subgroup.topEquiv.trans e)⟩⟩, ?_, ht2, hPC, ?_, ?_⟩, hPK, hU, hCN⟩
  · rw [hSP, Subgroup.map_top, Subgroup.range_subtype]
    exact htP
  · refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mpr ?_
    rw [hCN]
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
  · exact hP2.to_quotient _

theorem pieceTightDatum :
    ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), STSetting G K →
      ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
        ∃ (t : G) (P : Subgroup G) (SP : Sylow 2 P),
          TightDatum P SP t ∧ P ≤ K ∧ (∀ u ∈ K, orderOf u = 2 → u = t) ∧
          Subgroup.centralizer ({t} : Set G) = Subgroup.normalizer (K : Set G) :=
  fun _ _ _ _ S R hq => exists_tightDatum_of_quaternion S R hq

end CFSG.CGT.PushingUpLit.SolKNA
