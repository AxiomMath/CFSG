module

public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.RankFourTheoremC.PPointInvTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankFourTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l28l45_exists_invariant_two_lift {J U : Subgroup G} (hU : IsPGroup 3 U)
    (O : Subgroup ↥J) [O.Normal] (hO : Nat.Coprime 3 (Nat.card O)) (V : Subgroup (↥J ⧸ O))
    (hV2 : IsPGroup 2 V)
    (hUĈ : U ≤ normalizer (((V.comap (QuotientGroup.mk' O)).map J.subtype : Subgroup G) :
      Set G)) :
    ∃ W : Subgroup G, IsPGroup 2 W ∧ U ≤ normalizer (W : Set G) ∧
      ∀ v ∈ V, ∃ (s : G) (hs : s ∈ J), s ∈ W ∧ QuotientGroup.mk' O ⟨s, hs⟩ = v := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : ↥J →* ↥J ⧸ O := QuotientGroup.mk' O with hρ
  set Ĉ : Subgroup ↥J := V.comap ρ with hĈ
  set Ĉg : Subgroup G := Ĉ.map J.subtype with hĈg
  have hĈJ : Ĉg ≤ J := Subgroup.map_subtype_le _
  have hcop : Nat.Coprime 3 (Nat.card Ĉg) := by
    by_contra hnc
    have hdvd : 3 ∣ Nat.card Ĉg := by
      by_contra hnd
      exact hnc (hp.coprime_iff_not_dvd.mpr hnd)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Ĉg) 3 hdvd
    obtain ⟨c, hc, hcg⟩ := g.2
    have hgp : (g : G) ^ 3 = 1 := by
      have := pow_orderOf_eq_one g
      rw [hg] at this
      simpa using congrArg Subtype.val this
    have hcp : c ^ 3 = 1 := by
      apply J.subtype_injective
      rw [map_pow, hcg, map_one]
      exact hgp
    have hρc : ρ c = 1 := by
      obtain ⟨k, hk⟩ := hV2 ⟨ρ c, hc⟩
      have h1 : orderOf (ρ c) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hcp, map_one])
      have h2 : orderOf (ρ c) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hcop' : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' h1 h2)
    have hcO : c ∈ O := (QuotientGroup.eq_one_iff c).mp hρc
    have hordc : orderOf c = 3 := by
      rw [← Subgroup.orderOf_coe c]
      have hcg' : (c : G) = (g : G) := hcg
      rw [hcg', Subgroup.orderOf_coe, hg]
    have hdvdO : 3 ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨c, hcO⟩ : O)
      rwa [Subgroup.orderOf_mk, hordc] at this
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hO hdvdO)
  have hUbot : U ≤ normalizer (((⊥ : Subgroup G)) : Set G) := fun w _ => by
    rw [mem_normalizer_iff]
    intro h
    simp
  obtain ⟨W, -, hW⟩ := exists_invariantTwoMaximalWithin_containing U Ĉg ⊥ bot_le
    (IsPGroup.of_card (n := 0) (by simp)) hUbot
  have hWs : CFSG.ABGLocalTools.IsSylowOf 2 W Ĉg :=
    isSylowOf_two_of_invariantTwoMaximalWithin hp hU hUĈ hcop hW
  have hWJ : W ≤ J := hW.1.trans hĈJ
  set W' : Subgroup ↥J := W.subgroupOf J with hW'
  have hW'W : W'.map J.subtype = W := by
    rw [hW', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWJ]
  have hW'Ĉ : CFSG.ABGLocalTools.IsSylowOf 2 W' Ĉ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff J, hW'W]
    exact hWs
  obtain ⟨Q, hQ⟩ := hW'Ĉ
  set φ : Ĉ →* V := (ρ.comp Ĉ.subtype).codRestrict V (fun c => c.2) with hφdef
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective O (v : ↥J ⧸ O)
    exact ⟨⟨c, show ρ c ∈ V from by rw [hρ, hc]; exact v.2⟩, Subtype.ext hc⟩
  have hVtop : IsPGroup 2 ↥(⊤ : Subgroup V) := hV2.of_equiv Subgroup.topEquiv.symm
  have hQtop : (⊤ : Subgroup V) = (Q.mapSurjective hφ : Subgroup V) :=
    (Q.mapSurjective hφ).3 hVtop le_top
  have hVW : ∀ v ∈ V, ∃ c ∈ W', ρ c = v := by
    intro v hv
    have hv' : (⟨v, hv⟩ : V) ∈ (Q.mapSurjective hφ : Subgroup V) := by
      rw [← hQtop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hv'
    obtain ⟨q, hq, hqv⟩ := hv'
    refine ⟨(q : ↥J), ?_, congrArg Subtype.val hqv⟩
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  refine ⟨W, hW.2.1, hW.2.2.1, fun v hv => ?_⟩
  obtain ⟨c, hcW, hcv⟩ := hVW v hv
  refine ⟨c, c.2, ?_, hcv⟩
  rw [← hW'W]
  exact ⟨c, hcW, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
