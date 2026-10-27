module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617D

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_of_commute_rank_four (hG4 : pRank 2 G ≤ 4) {B : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : 4 ≤ pRank 2 ↥B) {w : G} (hw2 : w * w = 1)
    (hwc : ∀ β ∈ B, β * w = w * β) : w ∈ B := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hwB
  have hw1 : w ≠ 1 := fun h => hwB (h ▸ B.one_mem)
  have hwo : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hw2) hw1
  have hcd : Th2.CommDisj B (zpowers w) := by
    refine ⟨fun b hb t ht => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
      exact (Commute.zpow_right (show Commute b w from hwc b hb) m).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hwo hz.2 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.1) hwB
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers w) := Th2.isElementaryAbelian_zpowers_of_orderOf_two hwo
  have hrk := hcd.pRank_sup hBel hxel le_rfl le_rfl
  rw [Th2.pRank_zpowers_of_orderOf_two hwo] at hrk
  have h4 := pRank_le_top' (B ⊔ zpowers w)
  omega

theorem inf_center_ne_bot_of_normal {X N : Subgroup G} (hX : IsPGroup 2 ↥X) (hNX : N ≤ X)
    (hNn : X ≤ normalizer (N : Set G)) (hN : N ≠ ⊥) :
    N ⊓ (X ⊓ centralizer (X : Set G)) ≠ ⊥ := by
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

theorem card_rootFour_sup_swap {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F)
    {t : Perm (Fin 7)} (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i) :
    Nat.card ↥(F ⊔ Subgroup.zpowers t) = 8 := by
  classical
  have ht2 : orderOf t = 2 := ht.orderOf
  have hsign : Equiv.Perm.sign t = -1 := by
    obtain ⟨a, b, hab, rfl⟩ := ht
    exact Equiv.Perm.sign_swap hab
  have hcd : Th2.CommDisj F (zpowers t) := by
    refine ⟨fun f hf s hs => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hs
      have hdisj : f.Disjoint t := fun i => by
        by_cases hfi : f i = i
        · exact Or.inl hfi
        · exact Or.inr (hdis i ⟨f, hf, hfi⟩)
      exact (Commute.zpow_right hdisj.commute m).eq
    · refine eq_bot_iff.2 fun g hg => ?_
      rcases mem_zpowers_two ht2 hg.2 with h0 | h0
      · simp [h0]
      · exfalso
        have hA : t ∈ alternatingGroup (Fin 7) := hF.1 (h0 ▸ hg.1)
        rw [Equiv.Perm.mem_alternatingGroup, hsign] at hA
        exact absurd hA (by decide)
  rw [hcd.card_sup le_rfl le_rfl, hF.2.1, Nat.card_zpowers, ht2]

omit [Finite G] in
theorem card_B_eq_sixteen [Finite G] (hG4 : pRank 2 G ≤ 4) {B : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : 4 ≤ pRank 2 ↥B) : Nat.card ↥B = 16 := by
  have hr : pRank 2 ↥B = 4 := le_antisymm ((pRank_le_top' B).trans hG4) hB4
  rw [C3.Layer1.Back.card_eq_two_pow_pRank hBel, hr]
  norm_num

theorem Obstr52.B_inf_ker {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : 4 ≤ pRank 2 ↥B)
    {β : G} (hβ : β ∈ B) (hker : β ∈ centralizerSection J (pPrimeCoreOf 2 J)) :
    β = 1 ∨ β = b := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h.nonempty_A7_of_rank_four hG4 hBel
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hBC : B ≤ centralizer ({b} : Set G) := h.B_le_centralizer hBel
  have hBN : B ≤ normalizer (J : Set G) := hBC.trans (h.centralizer_le_normalizer hG4 hBel)
  obtain ⟨F, t, hF, ht, hdis, hrange⟩ := h.exists_image_B hG4 hBel e (le_refl B) hBN
  set φ := actOn e hBN with hφ
  have hcardr : Nat.card ↥φ.range = 8 := by
    rw [show φ.range = F ⊔ zpowers t from hrange]
    exact card_rootFour_sup_swap hF ht hdis
  have hcardB := card_B_eq_sixteen hG4 hBel hB4
  have hk := Subgroup.card_ker_mul_card_range φ
  rw [hcardr, hcardB] at hk
  have hk2 : Nat.card φ.ker = 2 := by omega
  have hb2 : orderOf b = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq b h.mem) h.ne_one
  set c : ↥B := ⟨b, h.mem⟩ with hc
  have hco : orderOf c = 2 := by
    rw [← Subgroup.orderOf_coe c]
    exact hb2
  have hbk : c ∈ φ.ker := (actOn_eq_one_iff e hBN h.mem).2 (mem_CxK_self' h.comp.1).2
  have hzk : zpowers c ≤ φ.ker := (zpowers_le).2 hbk
  have hzeq : zpowers c = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hzk (by rw [hk2, Nat.card_zpowers, hco])
  have hβk : (⟨β, hβ⟩ : ↥B) ∈ φ.ker := (actOn_eq_one_iff e hBN hβ).2 hker
  rw [← hzeq] at hβk
  rcases mem_zpowers_two hco hβk with h0 | h0
  · left
    exact congrArg Subtype.val h0
  · right
    exact congrArg Subtype.val h0

theorem Obstr52.b_mem_of_normal_ker {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J)
    (hG4 : pRank 2 G ≤ 4) (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : 4 ≤ pRank 2 ↥B)
    {X : Subgroup G} (hX2 : IsPGroup 2 ↥X) (hBX : B ≤ X)
    {N : Subgroup G} (hNX : N ≤ X) (hNn : X ≤ normalizer (N : Set G)) (hNker : N ≤ CxK b J)
    (hN1 : N ≠ ⊥) : b ∈ N := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  set Z₂ : Subgroup G := N ⊓ (X ⊓ centralizer (X : Set G)) with hZ₂
  have hZ₂ne : Z₂ ≠ ⊥ := inf_center_ne_bot_of_normal hX2 hNX hNn hN1
  have hZ₂2 : IsPGroup 2 ↥Z₂ := hX2.to_le (inf_le_left.trans hNX)
  have hdvd : 2 ∣ Nat.card ↥Z₂ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ₂2
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hn
      exact hZ₂ne ((Subgroup.card_eq_one).1 hn)
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z₂) 2 hdvd
  have hwo : orderOf (w : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hw
  have hwsq : (w : G) * (w : G) = 1 := by
    have := pow_orderOf_eq_one (w : G)
    rwa [hwo, sq] at this
  have hwN : (w : G) ∈ N := w.2.1
  have hwX : (w : G) ∈ X := w.2.2.1
  have hwC : (w : G) ∈ centralizer (X : Set G) := w.2.2.2
  have hwB : (w : G) ∈ B := by
    refine mem_of_commute_rank_four hG4 hBel hB4 hwsq (fun β hβ => ?_)
    exact Subgroup.mem_centralizer_iff.1 hwC β (hBX hβ)
  have hwker : (w : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) := (hNker hwN).2
  rcases h.B_inf_ker hG4 hBel hB4 hwB hwker with h1 | h1
  · rw [h1, orderOf_one] at hwo
    exact absurd hwo (by decide)
  · rw [← h1]
    exact hwN

end CFSG.GH74.GLS.Th2.Obs

