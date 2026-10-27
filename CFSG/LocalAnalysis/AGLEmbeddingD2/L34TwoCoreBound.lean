module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaPU
public import CFSG.LocalAnalysis.AGLEmbeddingD2.E9TwoGroup

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}

omit [Finite G] in
theorem le_normalizer_twoCore (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := by
  have hn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 H H le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  exact Subgroup.le_normalizer_of_normal_subgroupOf
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 H)

theorem D2Escape.exists_mem_normalizer_conj_eq_of_l34
    {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M A H R : Subgroup G}
    (h : D2Escape 3 P M A H R) {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hL : CFSG.AGLEmbedding.IsLinThreeFour K)
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K)
    {x y : G} (hx : x ∈ A) (hx1 : x ≠ 1) (hy : y ∈ A) (hy1 : y ≠ 1) :
    ∃ g ∈ H ⊓ Subgroup.normalizer (A : Set G), g * x * g⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W : Subgroup H := primeComplementCore (G := H) 3 with hWdef
  have hWcop : Nat.Coprime 3 (Nat.card W) := primeComplementCore_coprime 3
  set π := QuotientGroup.mk' W with hπ
  set Ab : Subgroup (H ⧸ W) := (A.subgroupOf H).map π with hAbdef
  have hAH : A ≤ H := h.A_le.trans h.le_H
  have hAcard : Nat.card (A.subgroupOf H) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, h.card_A]
    norm_num
  have hAp : IsPGroup 3 (A.subgroupOf H) :=
    IsPGroup.of_card (n := 2) (by rw [hAcard]; norm_num)
  have hAb : Nat.card Ab = 9 := by
    rw [hAbdef, card_map_mk_of_isPGroup Nat.prime_three W hWcop hAp, hAcard]
  have hbot : A.subgroupOf H ⊓ W = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard (by
      rw [hAcard, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact hWcop.pow_left 2)).eq_bot
  have hinj : ∀ u ∈ A.subgroupOf H, ∀ v ∈ A.subgroupOf H, π u = π v → u = v := by
    intro u hu v hv huv
    have hw : u⁻¹ * v ∈ W := QuotientGroup.eq.mp huv
    have h1 : u⁻¹ * v ∈ A.subgroupOf H ⊓ W :=
      ⟨(A.subgroupOf H).mul_mem ((A.subgroupOf H).inv_mem hu) hv, hw⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  have hcardK : Nat.card K = 20160 := (kFactSmallThreeOrders K).2.1 hL
  have hAc : Nat.card (Ab.subgroupOf K) = 3 ^ (Nat.card K).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAb, hcardK,
      factorization_20160_three]
    norm_num
  let T : Sylow 3 K := Sylow.ofCard (Ab.subgroupOf K) hAc
  have hT : (T : Subgroup K) = Ab.subgroupOf K := rfl
  have hloc := KFactProofs.UPrimeExcL34.localData_of_isLinThreeFour hL T
  have himg : ∀ x (hx : x ∈ A), ∃ xb : K, (xb : H ⧸ W) = π ⟨x, hAH hx⟩ ∧ xb ∈ (T : Subgroup K) ∧
      (x ≠ 1 → xb ≠ 1) := by
    intro x hx
    have hxA : (⟨x, hAH hx⟩ : H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    refine ⟨⟨π ⟨x, hAH hx⟩, hAK (Subgroup.mem_map_of_mem π hxA)⟩, rfl, ?_, ?_⟩
    · rw [hT, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_map_of_mem π hxA
    · intro hx1 hxb
      apply hx1
      have h1 : π ⟨x, hAH hx⟩ = π 1 := by
        rw [map_one]
        exact congrArg Subtype.val hxb
      have := hinj _ hxA _ (Subgroup.one_mem _) h1
      exact congrArg Subtype.val this
  have hconj : ∀ g : H, g ∈ Subgroup.normalizer ((A.subgroupOf H : Subgroup H) : Set H) →
      (g : G) ∈ Subgroup.normalizer (A : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      have h1 := (Subgroup.mem_normalizer_iff.mp hg ⟨a, hAH ha⟩).mp (Subgroup.mem_subgroupOf.mpr ha)
      simpa using Subgroup.mem_subgroupOf.mp h1
    · intro ha
      have haH : a ∈ H := by
        have h1 : (g : G) * a * (g : G)⁻¹ ∈ H := hAH ha
        have h2 := H.mul_mem (H.mul_mem (H.inv_mem g.2) h1) g.2
        simpa [mul_assoc] using h2
      have h2 := (Subgroup.mem_normalizer_iff.mp (inv_mem hg)
        ⟨(g : G) * a * (g : G)⁻¹, hAH ha⟩).mp (Subgroup.mem_subgroupOf.mpr ha)
      simpa [mul_assoc] using Subgroup.mem_subgroupOf.mp h2
  have hxA : (⟨x, hAH hx⟩ : H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  have hyA : (⟨y, hAH hy⟩ : H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
  obtain ⟨xb, hxb, hxbT, hxb1⟩ := himg x hx
  obtain ⟨yb, hyb, hybT, hyb1⟩ := himg y hy
  obtain ⟨n, hn, hnxy⟩ := hloc.trans xb hxbT (hxb1 hx1) yb hybT (hyb1 hy1)
  have hnX : (n : H ⧸ W) ∈ Subgroup.normalizer (Ab : Set (H ⧸ W)) := by
    rw [hT, ← Subgroup.subgroupOf_normalizer_eq hAK] at hn
    exact Subgroup.mem_subgroupOf.mp hn
  obtain ⟨h₀, hh₀⟩ := QuotientGroup.mk'_surjective W (n : H ⧸ W)
  have hh₀N : h₀ ∈ W ⊔ Subgroup.normalizer ((A.subgroupOf H : Subgroup H) : Set H) :=
    comap_normalizer_map_le_sup Nat.prime_three W hWcop hAp
      (Subgroup.mem_comap.mpr (by rw [hh₀]; exact hnX))
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hh₀N
  obtain ⟨w, hw, m, hm, rfl⟩ := hh₀N
  have hw1 : (QuotientGroup.mk' W) w = 1 := (QuotientGroup.eq_one_iff w).mpr hw
  have hπm : π m = (n : H ⧸ W) := by
    rw [← hh₀, map_mul, hw1, one_mul]
  have hmx : m * ⟨x, hAH hx⟩ * m⁻¹ ∈ A.subgroupOf H :=
    (Subgroup.mem_normalizer_iff.mp hm _).mp hxA
  have heq : π (m * ⟨x, hAH hx⟩ * m⁻¹) = π ⟨y, hAH hy⟩ := by
    rw [map_mul, map_mul, map_inv, hπm, ← hxb, ← hyb, ← hnxy]
    rfl
  have := hinj _ hmx _ hyA heq
  exact ⟨(m : G), Subgroup.mem_inf.mpr ⟨m.2, hconj m hm⟩, congrArg Subtype.val this⟩

theorem D2Escape.exists_conj_eq_of_l34 (h : D2Escape 3 P M A H R)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K) :
    ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 → ∃ g ∈ H, g * x * g⁻¹ = y := by
  intro x hx hx1 y hy hy1
  obtain ⟨g, hg, hgxy⟩ :=
    h.exists_mem_normalizer_conj_eq_of_l34 (isLinThreeFour_of_l34Index hd he) hAK hx hx1 hy hy1
  exact ⟨g, hg.1, hgxy⟩

theorem D2Escape.two_pow_eight_le_card_twoCore_of_l34 (h : D2Escape 3 P M A H R)
    (hglob : AGLGlobal G) {d : TauCeti.ValidLieTypeIndex} (hd : IsL34Index d)
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hAK : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 3)) ≤ K) :
    2 ^ 8 ≤ Nat.card (pCoreOf 2 H) := by
  have hAH : A ≤ H := h.A_le.trans h.le_H
  have htrans : ∀ x ∈ A, x ≠ 1 → ∀ y ∈ A, y ≠ 1 →
      ∃ g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G), g * x * g⁻¹ = y := by
    intro x hx hx1 y hy hy1
    obtain ⟨g, hgH, hg⟩ := h.exists_conj_eq_of_l34 hd he hAK x hx hx1 y hy hy1
    exact ⟨g, le_normalizer_twoCore H hgH, hg⟩
  have hS2 : IsPGroup 2 (pCoreOf 2 H) := pCoreOf_isPGroup 2 H
  have hne : ¬ pCoreOf 2 H ≤ Subgroup.centralizer (A : Set G) := by
    intro hle
    have hAC : A ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      Subgroup.le_centralizer_iff.mp hle
    have hchar := hglob.charTwo H h.maxTwoLocal_H.1
    have hAS : A ≤ pCoreOf 2 H := fun a ha => hchar ⟨hAH ha, hAC ha⟩
    obtain ⟨k, hk⟩ := (hS2.to_le hAS).exists_card_eq
    rw [h.card_A] at hk
    have h3 : 3 ∣ 2 ^ k := by rw [← hk]; exact dvd_pow_self 3 two_ne_zero
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have h8 := E9TwoGroup.two_pow_eight_mul_card_le (pCoreOf 2 H) A hS2
    (hAH.trans (le_normalizer_twoCore H)) (by rw [h.card_A]; norm_num) htrans hne
  have hpos : 0 < Nat.card
      (pCoreOf 2 H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  calc 2 ^ 8 = 2 ^ 8 * 1 := by norm_num
    _ ≤ 2 ^ 8 * Nat.card (pCoreOf 2 H ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) :=
        Nat.mul_le_mul_left _ hpos
    _ ≤ _ := h8

end CFSG.AGLEmbeddingD2
