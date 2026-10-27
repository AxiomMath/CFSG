module

public import CFSG.GH74.GLS.C3.Layer1.BkA7Facts
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem z_mem_of_isFourSub {P U : Subgroup G} (hP : RankTwoShape P) {z : G} (hzP : z ∈ P) (hz1 : z ≠ 1)
    (hzz : z * z = 1) (hzc : ∀ p ∈ P, p * z = z * p) (hU : IsFourSub P U) : z ∈ U := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hzU
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hcd : CommDisj U (zpowers z) := by
    refine ⟨fun u hu s hs => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      exact (Commute.zpow_right (show Commute u z from hzc u (hU.1 hu)) m).eq
    · refine eq_bot_iff.2 fun w hw => ?_
      rcases mem_zpowers_two hzo hw.2 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hw.1) hzU
  have hrk := hcd.pRank_sup hU.2.1 (Th2.isElementaryAbelian_zpowers_of_orderOf_two hzo) le_rfl le_rfl
  rw [pRank_of_isFourSub hU, Th2.pRank_zpowers_of_orderOf_two hzo] at hrk
  have hle : U ⊔ zpowers z ≤ P := sup_le hU.1 (zpowers_le.2 hzP)
  have h1 := C3.Layer1.Back.pRank_mono' hle
  have h2 := pRank_eq_two_of_rankTwoShape hP
  omega


omit [Finite G] in
theorem normal_of_isFourSub_of_card_eight {P U : Subgroup G} (hP8 : Nat.card ↥P = 8)
    (hU : IsFourSub P U) : ∀ u ∈ U, ∀ p ∈ P, p * u * p⁻¹ ∈ U := by
  classical
  have h2 : Nat.card ↥(U.subgroupOf P) = 4 := by
    rw [← hU.2.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU.1).toEquiv
  have h1 : (U.subgroupOf P).index = 2 := by
    have h := Subgroup.index_mul_card (U.subgroupOf P)
    rw [h2, hP8] at h
    omega
  have hn : (U.subgroupOf P).Normal := Subgroup.normal_of_index_eq_two h1
  intro u hu p hp
  have := hn.conj_mem ⟨u, hU.1 hu⟩ (Subgroup.mem_subgroupOf.2 hu) ⟨p, hp⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem exists_dec617 (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) :
    ∃ (U E : Subgroup G) (z : G), IsFourSub (T ⊓ K) U ∧ IsS (T ⊓ CxK x K) E ∧
      2 ≤ pRank 2 ↥E ∧ B = U ⊔ E ∧ z ∈ U ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ p ∈ T ⊓ K, p * z = z * p) ∧
      (∀ w ∈ T ⊓ K, (∀ p ∈ T ⊓ K, p * w = w * p) → w = 1 ∨ w = z) ∧ Nat.card ↥(T ⊓ K) = 8 := by
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hP : RankTwoShape (T ⊓ K) := rankTwoShape_sylow_A7 hs.sylow_P ⟨eK⟩
  obtain ⟨U, hU, E, hE, hE2, hBdef⟩ := (isS_sup_iff hcd hP B).1 hB
  have hD8 := C3.Layer1.Bk.isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P eK
  obtain ⟨z, hzP, hz1, hzz, hzc, hzu⟩ := hD8.exists_z
  exact ⟨U, E, z, hU, hE, hE2, hBdef, z_mem_of_isFourSub hP hzP hz1 hzz hzc hU, hz1, hzz, hzc, hzu,
    hD8.card_eq⟩

end CFSG.GH74.GLS.Th2.Obs
