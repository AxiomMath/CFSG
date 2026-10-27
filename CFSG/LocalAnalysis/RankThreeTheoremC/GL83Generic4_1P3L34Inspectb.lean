module

public import Mathlib.GroupTheory.PGroup
import CFSG.GH74.Constrained
import CFSG.LocalAnalysis.RankFourTheoremC.PPointInvTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankFourTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem l34insp_exists_fixed {S B : Subgroup G} {u : G} (hSB : S ≤ B) (hB : IsPGroup 2 B)
    (hBS : B ≤ normalizer (S : Set G)) (hu : u ∈ normalizer (S : Set G)) (hu3 : orderOf u = 3)
    (hcomm : ∀ b ∈ B, b⁻¹ * u⁻¹ * b * u ∈ S) {b : G} (hb : b ∈ B) :
    ∃ c ∈ B, c * u = u * c ∧ c⁻¹ * b ∈ S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := normalizer (S : Set G) with hN
  set S' : Subgroup N := S.subgroupOf N with hS'
  have hS'n : S'.Normal := Subgroup.normal_in_normalizer
  have hcop : Nat.Coprime 3 (Nat.card S') := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((hB.to_le hSB).comap_subtype (K := N))
    rw [show Nat.card S' = 2 ^ k from hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have ht : ∃ k : ℕ, orderOf (⟨u, hu⟩ : N) = 3 ^ k := ⟨1, by rw [Subgroup.orderOf_mk, hu3, pow_one]⟩
  have hcent := CFSG.GH74.centralizer_singleton_quotient_eq_map 3 S' hcop ht
  have hb' : QuotientGroup.mk' S' (⟨b, hBS hb⟩ : N) ∈
      centralizer ({QuotientGroup.mk' S' (⟨u, hu⟩ : N)} : Set (N ⧸ S')) := by
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := S.inv_mem (hcomm b hb)
    have h1 : ((((⟨b, hBS hb⟩ : N) * ⟨u, hu⟩)⁻¹ * (⟨u, hu⟩ * ⟨b, hBS hb⟩) : N) : G) =
        (b⁻¹ * u⁻¹ * b * u)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h1]
    exact h
  rw [hcent] at hb'
  obtain ⟨c, hc, hcb⟩ := hb'
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hcb
  have hcb' : (c : G)⁻¹ * b ∈ S := by simpa using hcb
  have hcu : (c : G) * u = u * (c : G) := by
    have h := mem_centralizer_singleton_iff.mp hc
    simpa using congrArg Subtype.val h
  have hcB : (c : G) ∈ B := by
    have h : (c : G) = b * ((c : G)⁻¹ * b)⁻¹ := by group
    rw [h]
    exact B.mul_mem hb (B.inv_mem (hSB hcb'))
  exact ⟨c, hcB, hcu, hcb'⟩

theorem l34insp_lift {J U S : Subgroup G} {x u : G} {Q : Type*} [Group Q] (f : ↥J →* Q)
    (hU : IsPGroup 3 U) (huJ : u ∈ J) (hUxu : U ≤ zpowers x ⊔ zpowers u)
    (hxJ : ∀ j ∈ J, x * j = j * x) (hker : Nat.Coprime 3 (Nat.card f.ker))
    {V : Subgroup Q} (hV2 : IsPGroup 2 V) (hVf : V ≤ f.range)
    (hu : f ⟨u, huJ⟩ ∈ normalizer (V : Set Q)) (hSJ : S ≤ J) (hS2 : IsPGroup 2 S)
    (hUS : U ≤ normalizer (S : Set G)) (hSV : ∀ (s : G) (hs : s ∈ S), f ⟨s, hSJ hs⟩ ∈ V) :
    ∃ W : Subgroup G, S ≤ W ∧ W ≤ J ∧ IsPGroup 2 W ∧ U ≤ normalizer (W : Set G) ∧
      ∀ v ∈ V, ∃ (s : G) (hs : s ∈ J), s ∈ W ∧ f ⟨s, hs⟩ = v := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ĉ : Subgroup ↥J := V.comap f with hĈ
  set Ĉg : Subgroup G := Ĉ.map J.subtype with hĈg
  have hĈJ : Ĉg ≤ J := Subgroup.map_subtype_le _
  have hu' : (⟨u, huJ⟩ : ↥J) ∈ normalizer (Ĉ : Set ↥J) := by
    rw [mem_normalizer_iff]
    intro c
    have h := mem_normalizer_iff.mp hu (f c)
    simp only [hĈ, Subgroup.mem_comap, map_mul, map_inv]
    exact h
  have huĈ : u ∈ normalizer (Ĉg : Set G) := Subgroup.le_normalizer_map J.subtype ⟨_, hu', rfl⟩
  have hxĈ : x ∈ normalizer (Ĉg : Set G) :=
    Subgroup.centralizer_le_normalizer (Ĉg : Set G)
      (mem_centralizer_iff.mpr fun h hh => (hxJ h (hĈJ hh)).symm)
  have hUĈ : U ≤ normalizer (Ĉg : Set G) :=
    hUxu.trans (sup_le (zpowers_le.mpr hxĈ) (zpowers_le.mpr huĈ))
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
    have hfc : f c = 1 := by
      obtain ⟨k, hk⟩ := hV2 ⟨f c, hc⟩
      have h1 : orderOf (f c) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hcp, map_one])
      have h2 : orderOf (f c) ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hcop' : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop' h1 h2)
    have hordc : orderOf c = 3 := by
      rw [← Subgroup.orderOf_coe c]
      have hcg' : (c : G) = (g : G) := hcg
      rw [hcg', Subgroup.orderOf_coe, hg]
    have hdvdO : 3 ∣ Nat.card f.ker := by
      have hck : c ∈ f.ker := hfc
      have := orderOf_dvd_natCard (⟨c, hck⟩ : f.ker)
      rwa [Subgroup.orderOf_mk, hordc] at this
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hker hdvdO)
  have hSĈ : S ≤ Ĉg := fun s hs => ⟨⟨s, hSJ hs⟩, hSV s hs, rfl⟩
  obtain ⟨W, hSW, hW⟩ := exists_invariantTwoMaximalWithin_containing U Ĉg S hSĈ hS2 hUS
  have hWs : CFSG.ABGLocalTools.IsSylowOf 2 W Ĉg :=
    isSylowOf_two_of_invariantTwoMaximalWithin hp hU hUĈ hcop hW
  have hWJ : W ≤ J := hW.1.trans hĈJ
  set W' : Subgroup ↥J := W.subgroupOf J with hW'
  have hW'W : W'.map J.subtype = W := by
    rw [hW', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWJ]
  have hW'Ĉ : CFSG.ABGLocalTools.IsSylowOf 2 W' Ĉ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff J, hW'W]
    exact hWs
  obtain ⟨Q', hQ'⟩ := hW'Ĉ
  set φ : Ĉ →* V := (f.comp Ĉ.subtype).codRestrict V (fun c => c.2) with hφdef
  have hφ : Function.Surjective φ := by
    intro v
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (hVf v.2)
    exact ⟨⟨c, show f c ∈ V from by rw [hc]; exact v.2⟩, Subtype.ext hc⟩
  have hVtop : IsPGroup 2 ↥(⊤ : Subgroup V) := hV2.of_equiv Subgroup.topEquiv.symm
  have hQtop : (⊤ : Subgroup V) = (Q'.mapSurjective hφ : Subgroup V) :=
    (Q'.mapSurjective hφ).3 hVtop le_top
  have hVW : ∀ v ∈ V, ∃ c ∈ W', f c = v := by
    intro v hv
    have hv' : (⟨v, hv⟩ : V) ∈ (Q'.mapSurjective hφ : Subgroup V) := by
      rw [← hQtop]
      exact Subgroup.mem_top _
    rw [Sylow.coe_mapSurjective] at hv'
    obtain ⟨q, hq, hqv⟩ := hv'
    refine ⟨(q : ↥J), ?_, congrArg Subtype.val hqv⟩
    rw [← hQ']
    exact ⟨q, hq, rfl⟩
  refine ⟨W, hSW, hWJ, hW.2.1, hW.2.2.1, fun v hv => ?_⟩
  obtain ⟨c, hcW, hcv⟩ := hVW v hv
  refine ⟨c, c.2, ?_, hcv⟩
  rw [← hW'W]
  exact ⟨c, hcW, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
