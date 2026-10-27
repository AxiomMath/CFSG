module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.Dihedral.BrauerSuzuki
import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneCorefreeCyclic
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG.Open CFSG.ABGLocalTools
open scoped MatrixGroups

namespace StrongTI

variable {Y : Type} [Group Y]

theorem eq_bot_of_isPGroup_of_odd {A : Subgroup Y} [Finite Y] (hA : IsPGroup 2 A)
    {B : Subgroup Y} (hAB : A ≤ B) (hB : Odd (Nat.card B)) : A = ⊥ := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hA
  have hdvd : Nat.card A ∣ Nat.card B := Subgroup.card_dvd_of_le hAB
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card B := (hk ▸ dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.2 hB) (even_iff_two_dvd.2 h2)
  rw [hk0, pow_zero] at hk
  exact (Subgroup.eq_bot_iff_card A).2 hk

theorem exists_sylow_eq [Finite Y] {A : Subgroup Y} (hA : IsSylowOf 2 A ⊤) :
    ∃ S : Sylow 2 Y, (S : Subgroup Y) = A := by
  rw [isSylowOf_iff, Subgroup.relIndex_top_right] at hA
  exact ⟨hA.2.1.toSylow hA.2.2, rfl⟩

theorem inf_eq_bot_of_stronglyEmbedded_normalizer [Finite Y] {A B : Subgroup Y}
    (hA : IsSylowOf 2 A ⊤) (hB : IsSylowOf 2 B ⊤) (hAB : A ≠ B)
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (A : Set Y))) : A ⊓ B = ⊥ := by
  obtain ⟨SA, rfl⟩ := exists_sylow_eq hA
  obtain ⟨SB, rfl⟩ := exists_sylow_eq hB
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq Y SA SB
  have hSB : (SB : Subgroup Y) = (SA : Subgroup Y).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]
    rfl
  have hcN : c⁻¹ ∉ Subgroup.normalizer ((SA : Subgroup Y) : Set Y) := by
    intro h
    have h1 : c ∈ Subgroup.normalizer ((SA : Subgroup Y) : Set Y) := by
      simpa using Subgroup.inv_mem _ h
    have h2 : c • SA = SA := Sylow.smul_eq_iff_mem_normalizer.2 h1
    exact hAB (by rw [← hc, h2])
  have hodd := hSE.2.2 c⁻¹ hcN
  rw [inv_inv] at hodd
  refine eq_bot_of_isPGroup_of_odd (SA.isPGroup'.to_inf_left) (B := _) ?_ hodd
  refine le_inf (inf_le_left.trans Subgroup.le_normalizer) ?_
  refine inf_le_right.trans ?_
  rw [hSB]
  exact Subgroup.map_mono Subgroup.le_normalizer

theorem fusionIsBenderGroup_of_mulEquiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : fusionIsBenderGroup K) : fusionIsBenderGroup L := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem bender_sylow_inf_eq_bot [Finite Y] (hY : fusionIsBenderGroup Y) {A B : Subgroup Y}
    (hA : IsSylowOf 2 A ⊤) (hB : IsSylowOf 2 B ⊤) (hAB : A ≠ B) : A ⊓ B = ⊥ := by
  rcases hY with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨SA, rfl⟩ := exists_sylow_eq hA
    obtain ⟨SB, rfl⟩ := exists_sylow_eq hB
    have hL2 := CFSG.CGT.Timmesfeld75.IsL2Pair.of_psl_sylow (by omega : f ≠ 0) ⟨e⟩ SA
    obtain ⟨g, hg⟩ := hL2.exists_conj_eq_sylow SB
    have hgN : g ∉ Subgroup.normalizer ((SA : Subgroup Y) : Set Y) := by
      intro h
      have h1 : (SA : Subgroup Y).map (MulAut.conj g).toMonoidHom = SA :=
        Subgroup.mem_normalizer_iff_map_conj_eq.1 h
      exact hAB (by rw [← hg]; exact h1.symm)
    rw [← hg]
    exact hL2.inf_conj_eq_bot hgN
  · have : Finite (PSU3 2 f) := Finite.of_surjective e e.surjective
    have hbor := (bender_psu3_borel_full f hf).map_mulEquiv e.symm
    obtain ⟨SA, rfl⟩ := exists_sylow_eq hA
    exact inf_eq_bot_of_stronglyEmbedded_normalizer hA hB hAB (hbor SA).1
  · have : Finite (Sz a) := Finite.of_surjective e e.surjective
    have hbor := (bender_suzuki_borel_full a ha).map_mulEquiv e.symm
    obtain ⟨SA, rfl⟩ := exists_sylow_eq hA
    exact inf_eq_bot_of_stronglyEmbedded_normalizer hA hB hAB (hbor SA).1

theorem le_of_isPGroup_of_odd_index [Finite Y] {N : Subgroup Y} [N.Normal] (hN : Odd N.index)
    {P : Subgroup Y} (hP : IsPGroup 2 P) : P ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hP ⟨x, hx⟩
  have h1 : orderOf x = 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_coe (⟨x, hx⟩ : P)
  have h2 : orderOf (QuotientGroup.mk x : Y ⧸ N) ∣ 2 ^ k :=
    h1 ▸ orderOf_map_dvd (QuotientGroup.mk' N) x
  have h3 : orderOf (QuotientGroup.mk x : Y ⧸ N) ∣ N.index := orderOf_dvd_natCard _
  have hc : Nat.Coprime (2 ^ k) N.index := Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hN)
  have h4 : orderOf (QuotientGroup.mk x : Y ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes hc h2 h3
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 h4)

theorem false_of_central_involution
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) {t : Y} (ht : orderOf t = 2)
    (hc : t ∈ Subgroup.center Y) : False := by
  have hnorm : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le).2 hc)
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht, pow_one]
  have hbot := hO2 _ hnorm hp
  rw [Subgroup.zpowers_eq_bot] at hbot
  rw [hbot, orderOf_one] at ht
  omega

private theorem oddCore_eq_bot (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) :
    CFSG.oddCore Y = ⊥ :=
  le_bot_iff.1 (sSup_le fun N hN => (hO N hN.1 hN.2).le)

private theorem oddCore_eq_bot' (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥) :
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore Y = ⊥ :=
  le_bot_iff.1 (sSup_le fun N hN => (hO N hN.1 hN.2).le)

theorem sylow_inf_eq_bot_of_stronglyEmbedded [Finite Y]
    {K : Subgroup Y} (hK : fusionStronglyEmbedded K)
    (hO : ∀ N : Subgroup Y, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥)
    {P Q : Subgroup Y} (hP : IsSylowOf 2 P ⊤) (hQ : IsSylowOf 2 Q ⊤) (hPQ : P ≠ Q) :
    P ⊓ Q = ⊥ := by
  rcases CFSG.Open.bender_strongly_embedded_normal_series Y K hK with
    hcq | ⟨M, N, hMn, hNn, hMNn, hMN, hModd, hNodd, hBend⟩
  · exfalso
    have hev : Even (Nat.card Y) :=
      even_iff_two_dvd.2 ((even_iff_two_dvd.1 hK.2.1).trans (Subgroup.card_subgroup_dvd_card K))
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hev)
    have hp2 : IsPGroup 2 (Subgroup.zpowers t) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, ht, pow_one]
    obtain ⟨S, hS⟩ := hp2.exists_le_sylow
    have htS : t ∈ (S : Subgroup Y) := hS (Subgroup.mem_zpowers t)
    refine false_of_central_involution hO2 ht ?_
    rcases hcq S with hcyc | ⟨r, hr, hquat⟩
    · exact CFSG.DisconnectedInvolutionGraph.Helpers.corefree_cyclic_two_sylow_involution_central
        (oddCore_eq_bot' hO) S hcyc ⟨t, ht⟩
    · have hcen := CFSG.BrauerSuzuki.brauer_suzuki r hr S hquat t htS ht
      refine Subgroup.mem_center_iff.2 fun y => ?_
      have h1 := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk y)
      have h2 : (QuotientGroup.mk (y * t) : Y ⧸ CFSG.oddCore Y) = QuotientGroup.mk (t * y) := by
        simpa [QuotientGroup.mk_mul] using h1
      have h3 := QuotientGroup.eq.1 h2
      rw [oddCore_eq_bot hO, Subgroup.mem_bot] at h3
      exact inv_mul_eq_one.1 h3
  · have hM0 : M = ⊥ := hO M hMn hModd
    subst hM0
    have hBN : fusionIsBenderGroup ↥N := by
      refine fusionIsBenderGroup_of_mulEquiv ?_ hBend
      exact (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf N)).trans
        QuotientGroup.quotientBot
    have hPN : P ≤ N := le_of_isPGroup_of_odd_index hNodd hP.isPGroup
    have hQN : Q ≤ N := le_of_isPGroup_of_odd_index hNodd hQ.isPGroup
    have hsyl : ∀ {R : Subgroup Y}, IsSylowOf 2 R ⊤ → R ≤ N → IsSylowOf 2 (R.subgroupOf N) ⊤ := by
      intro R hR hRN
      rw [isSylowOf_iff]
      obtain ⟨-, hRp, hRi⟩ := isSylowOf_iff.1 hR
      rw [Subgroup.relIndex_top_right] at hRi
      refine ⟨le_top, hRp.comap_subtype, ?_⟩
      rw [Subgroup.relIndex_top_right]
      intro h
      exact hRi (h.trans (Subgroup.relIndex_dvd_index_of_le hRN))
    have hne : P.subgroupOf N ≠ Q.subgroupOf N := by
      intro h
      apply hPQ
      rw [← Subgroup.map_subgroupOf_eq_of_le hPN, ← Subgroup.map_subgroupOf_eq_of_le hQN, h]
    have hTI := bender_sylow_inf_eq_bot hBN (hsyl hP hPN) (hsyl hQ hQN) hne
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hxN : x ∈ N := hPN hx.1
    have hmem : (⟨x, hxN⟩ : N) ∈ P.subgroupOf N ⊓ Q.subgroupOf N := ⟨hx.1, hx.2⟩
    rw [hTI, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem

end StrongTI

end CFSG.CGT.PushingUpLit.C2L
