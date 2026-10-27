module

public import CFSG.GH74.GLS.Stage2.Local.P34Bar
public import CFSG.GH74.GLS.Stage2.Final.Thm6.I414Core

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

section Frattini

variable {Y : Type*} [Group Y] [Finite Y]

theorem centralizer_sup_eq_top {r : ℕ} [Fact r.Prime] (N : Subgroup Y) [N.Normal]
    (hsimple : IsSimpleGroup (Y ⧸ N)) {V : Subgroup Y} (hV : IsSylowOf r V N) {z : Y}
    (hzV : ∀ v ∈ V, z * v = v * z) (hzN : z ∉ N) :
    Subgroup.centralizer (V : Set Y) ⊔ N = ⊤ := by
  obtain ⟨Q, hQ⟩ := hV
  have hfr : normalizer (V : Set Y) ⊔ N = ⊤ := by
    have := Sylow.normalizer_sup_eq_top Q
    rwa [hQ] at this
  have hnorm : (N ⊔ Subgroup.centralizer (V : Set Y)).Normal :=
    I414.normal_sup_centralizer N V hfr
  set M : Subgroup Y := N ⊔ Subgroup.centralizer (V : Set Y) with hM
  have hMn : (M.map (QuotientGroup.mk' N)).Normal := hnorm.map _ (QuotientGroup.mk'_surjective N)
  have hzM : z ∈ M := (le_sup_right : Subgroup.centralizer (V : Set Y) ≤ M)
    (Subgroup.mem_centralizer_iff.mpr fun v hv => (hzV v hv).symm)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' N)) with h | h
  · exfalso
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hzN (h hzM)
  · have hsup : M ⊔ N = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' N) M
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    rw [sup_eq_left.mpr (le_sup_left : N ≤ M)] at hsup
    rw [sup_comm]
    exact hsup

end Frattini

section Cover

variable {X : Type} [Group X] [Finite X]

theorem cover_of_simple_quotient {r : ℕ} [Fact r.Prime] (K : Subgroup X)
    (hsimple : IsSimpleGroup (↥K ⧸ pPrimeCore 2 ↥K)) {V : Subgroup X}
    (hV : IsSylowOf r V (pPrimeCoreOf 2 K)) {z : X} (hzK : z ∈ K) (hz2 : orderOf z = 2)
    (hzV : ∀ v ∈ V, z * v = v * z) :
    K ≤ (K ⊓ Subgroup.centralizer (V : Set X)) ⊔ pPrimeCoreOf 2 K := by
  have hVle : V ≤ pPrimeCoreOf 2 K := hV.le
  have hVK : V ≤ K := hVle.trans (Subgroup.map_subtype_le _)
  have hVY : IsSylowOf r (V.subgroupOf K) (pPrimeCore 2 ↥K) := by
    refine (isSylowOf_map_subtype_iff K).mp ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hVK]
    exact hV
  have hzN : (⟨z, hzK⟩ : ↥K) ∉ pPrimeCore 2 ↥K := by
    intro h
    have := P34.odd_orderOf_of_mem_pPrimeCore (X := ↥K) h
    rw [Subgroup.orderOf_mk, hz2] at this
    exact absurd this (by decide)
  have hzV' : ∀ v ∈ V.subgroupOf K, (⟨z, hzK⟩ : ↥K) * v = v * ⟨z, hzK⟩ := fun v hv =>
    Subtype.ext (hzV v hv)
  have hn : (pPrimeCore 2 ↥K).Normal := pPrimeCore_normal (p := 2) (G := ↥K)
  have htop := centralizer_sup_eq_top (pPrimeCore 2 ↥K) hsimple hVY hzV' hzN
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥K) ∈ Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊔
      pPrimeCore 2 ↥K := by rw [htop]; trivial
  have hmap : (Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊔
      pPrimeCore 2 ↥K).map K.subtype ≤ (K ⊓ Subgroup.centralizer (V : Set X)) ⊔ pPrimeCoreOf 2 K := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ le_rfl
    rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ Subgroup.centralizer ((V.subgroupOf K : Subgroup ↥K) : Set ↥K) := hc
    refine ⟨c.2, ?_⟩
    show (c : X) ∈ Subgroup.centralizer (V : Set X)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hc' ⟨v, hVK hv⟩ hv)
  exact hmap ⟨⟨x, hx⟩, hx', rfl⟩

end Cover

section Transport

variable {G : Type*} [Group G]

theorem pPrimeCoreOf_subgroupOf_map {H J : Subgroup G} (hJH : J ≤ H) :
    (pPrimeCoreOf 2 (J.subgroupOf H)).map H.subtype = pPrimeCoreOf 2 J := by
  let e : ↥(J.subgroupOf H) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJH
  have h1 := CFSG.pPrimeCore_map_iso 2 e
  unfold pPrimeCoreOf
  rw [Subgroup.map_map, ← h1, Subgroup.map_map]
  congr 1

theorem commutator_pPrimeCoreOf_subgroupOf_map {H J : Subgroup G} (hJH : J ≤ H) :
    (⁅pPrimeCoreOf 2 (J.subgroupOf H), J.subgroupOf H⁆ : Subgroup ↥H).map H.subtype =
      ⁅pPrimeCoreOf 2 J, J⁆ := by
  rw [Subgroup.map_commutator, pPrimeCoreOf_subgroupOf_map hJH, Subgroup.map_subgroupOf_eq_of_le hJH]

theorem card_commutator_pPrimeCoreOf_subgroupOf {H J : Subgroup G} (hJH : J ≤ H) :
    Nat.card ↥(⁅pPrimeCoreOf 2 (J.subgroupOf H), J.subgroupOf H⁆ : Subgroup ↥H) =
      Nat.card ↥(⁅pPrimeCoreOf 2 J, J⁆ : Subgroup G) := by
  rw [← commutator_pPrimeCoreOf_subgroupOf_map hJH]
  exact (Subgroup.card_map_of_injective H.subtype_injective).symm

end Transport

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011
