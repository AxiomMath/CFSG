module

public import CFSG.GH74.GLS.C3.Layer1.BkL114SEAsm

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

theorem sylow_le_normalClosure_mul {M : Type} [Group M] [Finite M] {n : ℕ} (hn : n = 5 ∨ n = 7)
    (H : Subgroup (M ⧸ pPrimeCore 2 M)) (e : ↥H ≃* alternatingGroup (Fin (n + 4)))
    (hH : H.IsSubnormal) {S : Subgroup M} (hS : IsSylowOf 2 S ⊤)
    (hScard : Nat.card S ≤ 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2)
    {x : M} (hxS : x ∈ S) (hx : orderOf x = 2) :
    ∀ s ∈ S, ∃ d ∈ Subgroup.normalClosure ({x} : Set M), ∃ o ∈ pPrimeCore 2 M, s = d * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSH, -⟩ := map_le_of_sylow H e hH hS hScard
  have h5 : 5 ≤ Nat.card (Fin (n + 4)) := by simp; omega
  have : IsSimpleGroup (alternatingGroup (Fin (n + 4))) := alternatingGroup.isSimpleGroup h5
  have : IsSimpleGroup ↥H := e.isSimpleGroup
  have hx1 : piO M x ≠ 1 := by
    intro h1
    have := orderOf_piO_of_orderOf_two hx
    rw [h1, orderOf_one] at this
    omega
  let J : Subgroup ↥H := ((Subgroup.normalClosure ({x} : Set M)).map (piO M)).subgroupOf H
  have hJn : J.Normal := by
    refine ⟨fun j hj h => ?_⟩
    obtain ⟨d, hd, hdj⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hj)
    obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 M) (h : M ⧸ pPrimeCore 2 M)
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_map.2 ⟨m * d * m⁻¹, Subgroup.Normal.conj_mem inferInstance d hd m, ?_⟩
    change piO M (m * d * m⁻¹) = (h : M ⧸ pPrimeCore 2 M) * (j : M ⧸ pPrimeCore 2 M) *
      (h : M ⧸ pPrimeCore 2 M)⁻¹
    rw [map_mul, map_mul, map_inv, hdj]
    rw [hm]
  have hxJ : (⟨piO M x, hSH ⟨x, hxS, rfl⟩⟩ : ↥H) ∈ J :=
    Subgroup.mem_subgroupOf.2 ⟨x, Subgroup.subset_normalClosure rfl, rfl⟩
  have hJtop : J = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal J with hbot | htop
    · exfalso
      rw [hbot, Subgroup.mem_bot] at hxJ
      exact hx1 (congrArg Subtype.val hxJ)
    · exact htop
  intro s hs
  have hsJ : (⟨piO M s, hSH ⟨s, hs, rfl⟩⟩ : ↥H) ∈ J := by
    rw [hJtop]
    exact Subgroup.mem_top _
  obtain ⟨d, hd, hds⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hsJ)
  refine ⟨d, hd, d⁻¹ * s, ?_, by group⟩
  rw [← QuotientGroup.eq_one_iff]
  change piO M (d⁻¹ * s) = 1
  rw [map_mul, map_inv, hds]
  exact inv_mul_cancel _

theorem W_centralizes_S {G : Type} [Group G] [Finite G] {n : ℕ} (hn : n = 5 ∨ n = 7)
    {x : G} {K T Q S : Subgroup G} {a : G} (h : IsAConfigW n x K T Q S a) (hS : S = T ⊔ zpowers a)
    (haN : a ∈ NW x) {H : Subgroup (NWbar x)} {e : ↥H ≃* alternatingGroup (Fin (n + 4))}
    (hHsub : H.IsSubnormal) :
    ∀ s ∈ S, ∀ w ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)), s * w = w * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCN : centralizer ({x} : Set G) ≤ NW x := centralizer_le_NW x
  have hxN : x ∈ NW x := hCN (mem_centralizer_singleton_iff.2 rfl)
  have hSN : S ≤ NW x := by
    rw [hS]
    exact sup_le (h.T_le_C.trans hCN) (zpowers_le.2 haN)
  have hTS : T ≤ S := h.T_lt_S.le
  have hSyl : IsSylowOf 2 (S.subgroupOf (NW x)) ⊤ := by
    have h1 : IsSylowOf 2 S (NW x) := h.sylowS.of_le hSN le_top
    have h2 : IsSylowOf 2 ((S.subgroupOf (NW x)).map (NW x).subtype)
        ((⊤ : Subgroup ↥(NW x)).map (NW x).subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hSN, Subgroup.map_top, Subgroup.range_subtype]
      exact h1
    exact (isSylowOf_map_subtype_iff (NW x)).1 h2
  have hScard : Nat.card ↥(S.subgroupOf (NW x)) ≤
      2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]
    exact card_S_le hn h hS
  have hxS : (⟨x, hxN⟩ : ↥(NW x)) ∈ S.subgroupOf (NW x) := hTS h.x_mem_T
  have hx' : orderOf (⟨x, hxN⟩ : ↥(NW x)) = 2 := (Subgroup.orderOf_mk x hxN).trans h.x_order
  have hcover := sylow_le_normalClosure_mul hn H e hHsub hSyl hScard hxS hx'
  set W : Subgroup G := pPrimeCoreOf 2 (centralizer ({x} : Set G)) with hWdef
  let W' : Subgroup ↥(NW x) := W.subgroupOf (NW x)
  have hWn : ∀ m : ↥(NW x), ∀ w ∈ W', m * w * m⁻¹ ∈ W' := by
    intro m w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    have hm : (m : G) ∈ normalizer (W : Set G) := m.2
    exact (mem_normalizer_iff.1 hm (w : G)).1 hw
  let 𝒞 : Subgroup ↥(NW x) := centralizer (W' : Set ↥(NW x))
  have h𝒞n : 𝒞.Normal := by
    refine ⟨fun c hc m => ?_⟩
    rw [mem_centralizer_iff]
    intro w hw
    have hw' : m⁻¹ * w * m ∈ W' := by
      have := hWn m⁻¹ w hw
      simpa using this
    have := mem_centralizer_iff.1 hc _ hw'
    calc w * (m * c * m⁻¹) = m * ((m⁻¹ * w * m) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * w * m)) * m⁻¹ := by rw [this]
      _ = m * c * m⁻¹ * w := by group
  have hx𝒞 : (⟨x, hxN⟩ : ↥(NW x)) ∈ 𝒞 := by
    rw [mem_centralizer_iff]
    intro w hw
    have hwC : (w : G) ∈ centralizer ({x} : Set G) := by
      obtain ⟨u, -, hu⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hw)
      rw [← hu]
      exact u.2
    have := mem_centralizer_singleton_iff.1 hwC
    exact Subtype.ext this
  have hncl : Subgroup.normalClosure ({(⟨x, hxN⟩ : ↥(NW x))} : Set ↥(NW x)) ≤ 𝒞 :=
    Subgroup.normalClosure_le_normal (by simpa using hx𝒞)
  intro s hs w hw
  have hsN : s ∈ NW x := hSN hs
  have hsS : (⟨s, hsN⟩ : ↥(NW x)) ∈ S.subgroupOf (NW x) := hs
  obtain ⟨d, hd, o, ho, hdo⟩ := hcover ⟨s, hsN⟩ hsS
  have hd𝒞 : d ∈ 𝒞 := hncl hd
  have hs𝒞 : (⟨s, hsN⟩ : ↥(NW x)) ∈ 𝒞 := by
    rw [← QuotientGroup.eq_one_iff]
    have h2 : IsPGroup 2 ↥(S.subgroupOf (NW x)) := hSyl.isPGroup
    obtain ⟨k, hk⟩ := h2 ⟨⟨s, hsN⟩, hsS⟩
    have hk' : (⟨s, hsN⟩ : ↥(NW x)) ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    set y : ↥(NW x) ⧸ 𝒞 := ((⟨s, hsN⟩ : ↥(NW x)) : ↥(NW x) ⧸ 𝒞) with hy
    have hy1 : y ^ (2 ^ k) = 1 := by
      rw [hy, ← QuotientGroup.mk_pow, hk']
      rfl
    have hyo : y = (o : ↥(NW x) ⧸ 𝒞) := by
      rw [hy, hdo, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff d).2 hd𝒞, one_mul]
    have hy2 : y ^ Nat.card (pPrimeCore 2 ↥(NW x)) = 1 := by
      rw [hyo, ← QuotientGroup.mk_pow]
      have : o ^ Nat.card (pPrimeCore 2 ↥(NW x)) = 1 := by
        have := pow_card_eq_one' (G := pPrimeCore 2 ↥(NW x)) (x := ⟨o, ho⟩)
        exact congrArg Subtype.val this
      rw [this]
      rfl
    have hcop : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥(NW x))) :=
      Nat.Coprime.pow_left k pPrimeCore_coprime_card
    have : orderOf y = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hy1) (orderOf_dvd_of_pow_eq_one hy2)
    exact orderOf_eq_one_iff.1 this
  have hwN : w ∈ NW x := W_le_NW x hw
  have hw' : (⟨w, hwN⟩ : ↥(NW x)) ∈ W' := hw
  have := mem_centralizer_iff.1 hs𝒞 _ hw'
  exact (congrArg Subtype.val this).symm

end CFSG.GH74.GLS.C3.Layer1.Bk
