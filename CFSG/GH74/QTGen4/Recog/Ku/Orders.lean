module

public import CFSG.GH74.QTGen4.Recog.Ku.Hyp

public section

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

theorem card_perm_fin5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_perm_fin3 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem card_mulZMod2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_eq_fintype_card]
  rfl

variable {G : Type} [Group G]

theorem KuHyp.card_M {T M H P : Subgroup G} {z : G} [Finite G] (h : KuHyp G T M H P z) :
    Nat.card M = 1920 := by
  obtain ⟨φ, hφs, hker⟩ := h.mQuot
  have hVM : pCoreOf 2 M ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hq : Nat.card (↥M ⧸ φ.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      card_perm_fin5]
  have hk : Nat.card φ.ker = 16 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVM).toEquiv, h.vCard]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hq, hk]

theorem KuHyp.card_H {T M H P : Subgroup G} {z : G} [Finite G] (h : KuHyp G T M H P z) :
    Nat.card H = 384 := by
  obtain ⟨φ, hφs, hker⟩ := h.hQuot
  have hq : Nat.card (↥H ⧸ φ.ker) = 12 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv,
      Nat.card_prod, card_perm_fin3, card_mulZMod2]
  have hP := h.pExtra.2.1
  have hk : Nat.card φ.ker = 32 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.pH).toEquiv]
    norm_num [hP]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hq, hk]

theorem KuHyp.pCore_le_T {T M H P : Subgroup G} {z : G} [Finite G] (h : KuHyp G T M H P z) :
    pCoreOf 2 M ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hTn : T ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    have := h.tM
    rw [h.mNorm] at this
    exact this
  have hsup : IsPGroup 2 (pCoreOf 2 M ⊔ T : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_sup_of_normal_left' h.sylow.1 hTn
  have hEq : (pCoreOf 2 M ⊔ T : Subgroup G) = (S : Subgroup G) :=
    S.is_maximal' hsup le_sup_right
  have hS : (S : Subgroup G) = T := rfl
  rw [hS] at hEq
  exact le_sup_left.trans hEq.le

theorem KuHyp.card_T {T M H P : Subgroup G} {z : G} [Finite G] (h : KuHyp G T M H P z) :
    Nat.card T = 128 := by
  have hTG : Nat.card T * T.index = Nat.card G := Subgroup.card_mul_index T
  have hodd : Nat.Coprime (2 ^ 7) T.index :=
    Nat.Coprime.pow_left 7 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h.sylow.2)
  have hMG : Nat.card M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  rw [KuHyp.card_M h] at hMG
  have h128G : 2 ^ 7 ∣ Nat.card T * T.index := by
    rw [hTG]
    exact dvd_trans (by norm_num) hMG
  have h128T : 2 ^ 7 ∣ Nat.card T := Nat.Coprime.dvd_of_dvd_mul_right hodd h128G
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.sylow.1
  have hdvd : Nat.card T ∣ 1920 := by
    have := Subgroup.card_dvd_of_le h.tM
    rwa [KuHyp.card_M h] at this
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.sylow.1
  rw [hn] at hdvd h128T ⊢
  have h7 : 7 ≤ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h128T
  have h8 : n ≤ 7 := by
    by_contra hc
    have h8' : 2 ^ 8 ∣ 2 ^ n := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mpr (by omega)
    have := dvd_trans h8' hdvd
    norm_num at this
  obtain rfl : n = 7 := by omega
  norm_num

theorem inf_center_ne_bot_aux [Finite G] {X N : Subgroup G} (hX : IsPGroup 2 ↥X) (hNX : N ≤ X)
    (hNn : X ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) :
    N ⊓ (X ⊓ Subgroup.centralizer (X : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent X := hX.isNilpotent
  have hnormal : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNn
  have hne : N.subgroupOf X ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNX, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ N ⊓ (X ⊓ Subgroup.centralizer (X : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem KuHyp.card_zpowers {T M H P : Subgroup G} {z : G} (h : KuHyp G T M H P z) :
    Nat.card (Subgroup.zpowers z) = 2 := by
  have hmap : (Subgroup.center ↥P).map P.subtype = P ⊓ Subgroup.centralizer (P : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)
    · rintro ⟨hxP, hxC⟩
      refine ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxC g.1 g.2
  have hinj : Function.Injective P.subtype := Subtype.val_injective
  rw [← h.pCentP, ← hmap, Subgroup.card_map_of_injective hinj]
  exact h.pExtra.1.center_order_p

theorem KuHyp.z_mem_pCoreOf {T M H P : Subgroup G} {z : G} [Finite G]
    (h : KuHyp G T M H P z) : z ∈ pCoreOf 2 M := by
  have hVT : pCoreOf 2 M ≤ T := h.pCore_le_T
  have hTn : T ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) := by
    have := h.tM
    rw [h.mNorm] at this
    exact this
  have hVne : pCoreOf 2 M ≠ ⊥ := by
    intro h0
    have hc := h.vCard
    rw [h0, Subgroup.card_bot] at hc
    norm_num at hc
  have hmeet := inf_center_ne_bot_aux h.sylow.1 hVT hTn hVne
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hxz : x ∈ Subgroup.zpowers z :=
    h.center_T_le_zpowers x hx.2.1 fun y hy => Subgroup.mem_centralizer_iff.mp hx.2.2 y hy
  have hord : orderOf z = 2 := by rw [← Nat.card_zpowers, h.card_zpowers]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
  have hzk : z ^ k = z ^ (k % 2) := by
    have h2 := zpow_mod_orderOf z k
    rw [hord] at h2
    simpa using h2.symm
  have hxV : x ∈ pCoreOf 2 M := hx.1
  rw [← hk] at hxV hx1'
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with hk2 | hk2
  · rw [hzk, hk2, zpow_zero] at hx1'
    exact absurd rfl hx1'
  · rw [hzk, hk2, zpow_one] at hxV
    exact hxV

end CFSG.GH74.QTGen4.Ku
