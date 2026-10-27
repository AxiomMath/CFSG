module

public import CFSG.GH74.GLS.Stage2.Local.Defs
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local

theorem card_center_q8 : Nat.card (center (QuaternionGroup 2)) = 2 := by
  have h : ∀ g : QuaternionGroup 2, (∀ h, g * h = h * g) ↔ (g = 1 ∨ g = QuaternionGroup.a 2) := by decide
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, one_mem _⟩, ⟨QuaternionGroup.a 2, ?_⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact ((h (QuaternionGroup.a 2)).2 (Or.inr rfl) g).symm
  · intro hh
    have h2 : (1 : QuaternionGroup 2) ≠ QuaternionGroup.a 2 := by decide
    exact h2 (congrArg Subtype.val hh)
  · ext ⟨g, hg⟩
    rw [Subgroup.mem_center_iff] at hg
    have := (h g).1 (fun k => (hg k).symm)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases this with rfl | rfl
    · left; rfl
    · right; rfl

theorem inf_eq_center_of_q8 {P : Type} [Group P] [Finite P] {A B : Subgroup P}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hcard : Nat.card ↥(A ⊓ B) = 2)
    (eA : ↥A ≃* QuaternionGroup 2) :
    ∀ a ∈ A, (∀ a' ∈ A, a * a' = a' * a) → a ∈ A ⊓ B := by
  classical
  have hZcard : Nat.card ↥(center ↥A) = 2 := by
    rw [Nat.card_congr (Subgroup.centerCongr eA).toEquiv]
    exact card_center_q8
  have hle : (A ⊓ B).subgroupOf A ≤ center ↥A := by
    intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2 a ha.2)
  have hcard' : Nat.card ↥((A ⊓ B).subgroupOf A) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ B ≤ A)).toEquiv]
    exact hcard
  have heq : (A ⊓ B).subgroupOf A = center ↥A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hZcard, hcard'])
  intro a ha hc
  have : (⟨a, ha⟩ : ↥A) ∈ center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2).symm
  rw [← heq, Subgroup.mem_subgroupOf] at this
  exact this


structure BarShape (P : Type) [Group P] [Finite P] (zc : P) : Prop where
  ne_one : zc ≠ 1
  sq : zc * zc = 1
  central : ∀ g : P, g * zc = zc * g
  noOdd : pPrimeCore 2 P = ⊥
  data : ∃ (W A B A₃ : Subgroup P) (_ : W.Normal), zc ∈ W ∧ IsCentralProd A B W ∧
    Nonempty (↥A ≃* QuaternionGroup 2) ∧ Nonempty (↥B ≃* QuaternionGroup 2) ∧ A.Normal ∧
    Nonempty (↥A₃ ≃* Multiplicative (ZMod 3)) ∧ generalizedFitting P = W ∧
    ⁅W, A₃⁆ = W ∧ (∀ w ∈ W, (∀ a ∈ A₃, a * w = w * a) → w ∈ zpowers zc) ∧
    Nonempty ((P ⧸ W) ≃* Equiv.Perm (Fin 3))

theorem center_W_key {P : Type} [Group P] [Finite P] {W A B : Subgroup P}
    (hcp : IsCentralProd A B W) (hAn : A.Normal)
    (eA : ↥A ≃* QuaternionGroup 2) (eB : ↥B ≃* QuaternionGroup 2) :
    ∀ w ∈ W, (∀ w' ∈ W, w * w' = w' * w) → w ∈ A ⊓ B := by
  classical
  obtain ⟨hAB, hcomm, hcard⟩ := hcp
  have hcomm' : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcomm a ha b hb).symm
  have hcard' : Nat.card ↥(B ⊓ A) = 2 := by rw [inf_comm]; exact hcard
  intro w hw hwc
  rw [← hAB] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hw
  have hAW : ∀ a' ∈ A, a' ∈ W := fun a' ha' => hAB ▸ Subgroup.mem_sup_left ha'
  have hBW : ∀ b' ∈ B, b' ∈ W := fun b' hb' => hAB ▸ Subgroup.mem_sup_right hb'
  have h1 : ∀ a' ∈ A, a * a' = a' * a := by
    intro a' ha'
    have := hwc a' (hAW a' ha')
    have h2 : a * b * a' = a * a' * b := by rw [mul_assoc, hcomm' b hb a' ha', ← mul_assoc]
    have h3 : a' * (a * b) = a' * a * b := by rw [mul_assoc]
    rw [h2, h3] at this
    exact mul_right_cancel this
  have h4 : ∀ b' ∈ B, b * b' = b' * b := by
    intro b' hb'
    have := hwc b' (hBW b' hb')
    have h2 : a * b * b' = a * (b * b') := by rw [mul_assoc]
    have h3 : b' * (a * b) = a * (b' * b) := by
      rw [← mul_assoc, hcomm' b' hb' a ha, mul_assoc]
    rw [h2, h3] at this
    exact mul_left_cancel this
  have haAB : a ∈ A ⊓ B := inf_eq_center_of_q8 hcomm hcard eA a ha h1
  have hbBA : b ∈ B ⊓ A := inf_eq_center_of_q8 hcomm' hcard' eB b hb h4
  exact (A ⊓ B).mul_mem haAB (by rw [inf_comm] at hbBA; exact hbBA)

theorem zpowers_zc_eq_inf {P : Type} [Group P] [Finite P] {zc : P} {W A B : Subgroup P}
    (hzc1 : zc ≠ 1) (hzc2 : zc * zc = 1) (hzcc : ∀ g : P, g * zc = zc * g) (hzcW : zc ∈ W)
    (hcp : IsCentralProd A B W) (hAn : A.Normal)
    (eA : ↥A ≃* QuaternionGroup 2) (eB : ↥B ≃* QuaternionGroup 2) :
    zpowers zc = A ⊓ B := by
  classical
  have hcard := hcp.2.2
  have hzAB : zc ∈ A ⊓ B := center_W_key hcp hAn eA eB zc hzcW (fun w' _ => (hzcc w').symm)
  have hz2 : orderOf zc = 2 := orderOf_eq_prime (by rw [sq]; exact hzc2) hzc1
  have hzp : Nat.card ↥(zpowers zc) = 2 := by rw [Nat.card_zpowers]; exact hz2
  exact Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzAB) (by rw [hcard, hzp])

theorem center_W {P : Type} [Group P] [Finite P] {zc : P} {W A B : Subgroup P} (hzc1 : zc ≠ 1)
    (hzc2 : zc * zc = 1) (hzcc : ∀ g : P, g * zc = zc * g) (hzcW : zc ∈ W)
    (hcp : IsCentralProd A B W) (hAn : A.Normal)
    (eA : ↥A ≃* QuaternionGroup 2) (eB : ↥B ≃* QuaternionGroup 2) :
    ∀ w ∈ W, (∀ w' ∈ W, w * w' = w' * w) → w ∈ zpowers zc := by
  intro w hw hwc
  rw [zpowers_zc_eq_inf hzc1 hzc2 hzcc hzcW hcp hAn eA eB]
  exact center_W_key hcp hAn eA eB w hw hwc

theorem isPGroup_W {P : Type} [Group P] [Finite P] {W A B : Subgroup P}
    (hcp : IsCentralProd A B W) (hAn : A.Normal)
    (eA : ↥A ≃* QuaternionGroup 2) (eB : ↥B ≃* QuaternionGroup 2) : IsPGroup 2 ↥W := by
  classical
  obtain ⟨hAB, hcomm, -⟩ := hcp
  have hq8 : ∀ g : QuaternionGroup 2, g ^ 8 = 1 := by decide
  have hA8 : ∀ a ∈ A, a ^ 8 = 1 := by
    intro a ha
    have := hq8 (eA ⟨a, ha⟩)
    rw [← map_pow] at this
    exact congrArg Subtype.val (eA.injective (this.trans (map_one eA).symm))
  have hB8 : ∀ b ∈ B, b ^ 8 = 1 := by
    intro b hb
    have := hq8 (eB ⟨b, hb⟩)
    rw [← map_pow] at this
    exact congrArg Subtype.val (eB.injective (this.trans (map_one eB).symm))
  intro g
  have hg : (g : P) ∈ A ⊔ B := hAB ▸ g.2
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  refine ⟨3, ?_⟩
  apply Subtype.ext
  show (g : P) ^ (2 ^ 3) = 1
  rw [← hab]
  have hc : Commute a b := hcomm a ha b hb
  rw [hc.mul_pow, show (2 : ℕ) ^ 3 = 8 from rfl, hA8 a ha, hB8 b hb, one_mul]

theorem BarShape.zc_mem_of_normal {P : Type} [Group P] [Finite P] {zc : P} (hP : BarShape P zc)
    {N : Subgroup P} [hN : N.Normal] (hNne : N ≠ ⊥) : zc ∈ N := by
  classical
  obtain ⟨W, A, B, A₃, hWn, hzcW, hcp, ⟨eA⟩, ⟨eB⟩, hAn, ⟨eA₃⟩, hF, hWA, hfix, ⟨eq⟩⟩ := hP.data
  have hZ := center_W hP.ne_one hP.sq hP.central hzcW hcp hAn eA eB
  have hz2 : orderOf zc = 2 := orderOf_eq_prime (by rw [pow_two]; exact hP.sq) hP.ne_one
  have h1 : N ⊓ W ≠ ⊥ := by
    intro hbot
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hcent : n ∈ centralizer (generalizedFitting P : Set P) := by
      rw [hF]
      intro w hw
      have h2 : n * w * n⁻¹ * w⁻¹ ∈ N ⊓ W := by
        refine ⟨?_, ?_⟩
        · have : w * n⁻¹ * w⁻¹ ∈ N := hN.conj_mem _ (N.inv_mem hn) w
          have h3 : n * w * n⁻¹ * w⁻¹ = n * (w * n⁻¹ * w⁻¹) := by group
          rw [h3]; exact N.mul_mem hn this
        · have : n * w * n⁻¹ ∈ W := hWn.conj_mem _ hw n
          exact W.mul_mem this (W.inv_mem hw)
      rw [hbot, Subgroup.mem_bot] at h2
      have h5 : n * w * n⁻¹ = w := mul_inv_eq_one.1 h2
      calc w * n = n * w * n⁻¹ * n := by rw [h5]
        _ = n * w := by group
    have := CFSG.centralizer_generalizedFitting_le P hcent
    rw [hF] at this
    have h4 : n ∈ N ⊓ W := ⟨hn, this⟩
    rw [hbot] at h4
    exact h4
  have hWp : IsPGroup 2 ↥W := isPGroup_W hcp hAn eA eB
  have hnil : Group.IsNilpotent ↥W := hWp.isNilpotent
  have hM : (N ⊓ W).subgroupOf W ≠ ⊥ := by
    intro h
    apply h1
    rw [eq_bot_iff]
    intro x hx
    have hxW : x ∈ W := hx.2
    have hx' : (⟨x, hxW⟩ : ↥W) ∈ (N ⊓ W).subgroupOf W := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (congrArg Subtype.val hx')
  have hMn : ((N ⊓ W).subgroupOf W).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (inferInstance : (N ⊓ W).Normal).conj_mem _ hx y
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal hM
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h2
  have huM : (u : ↥W) ∈ (N ⊓ W).subgroupOf W := hu.1
  have huZ : (u : ↥W) ∈ center ↥W := hu.2
  have huN : (u : P) ∈ N := (Subgroup.mem_subgroupOf.1 huM).1
  have huc : ∀ w' ∈ W, (u : P) * w' = w' * (u : P) := by
    intro w' hw'
    have := Subgroup.mem_center_iff.1 huZ ⟨w', hw'⟩
    exact (congrArg Subtype.val this).symm
  have huz : (u : P) ∈ zpowers zc := hZ _ u.2 huc
  have hu1' : (u : P) ≠ 1 := fun h => hu1 (Subtype.ext (Subtype.ext h))
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 huz
  have hk2 : zc ^ k = zc ^ (k % 2) := by
    have h := zpow_mod_orderOf zc k
    rw [hz2] at h
    simpa using h.symm
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · exfalso
    apply hu1'
    rw [← hk, hk2, h0]
    simp
  · rw [← hk, hk2, h0] at huN
    simpa using huN


theorem card_sup_mul_card_inf_of_normal' {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem BarShape.card_eq {P : Type} [Group P] [Finite P] {zc : P} (hP : BarShape P zc) :
    Nat.card P = 192 := by
  classical
  obtain ⟨W, A, B, A₃, hWn, hzcW, hcp, ⟨eA⟩, ⟨eB⟩, hAn, ⟨eA₃⟩, hF, hWA, hfix, ⟨eq⟩⟩ := hP.data
  obtain ⟨hAB, hcomm, hcard⟩ := hcp
  have hA8 : Nat.card ↥A = 8 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB8 : Nat.card ↥B = 8 := by
    rw [Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h1 := card_sup_mul_card_inf_of_normal' B A
  rw [sup_comm, hAB, inf_comm, hcard, hA8, hB8] at h1
  have hW : Nat.card ↥W = 32 := by omega
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup W
  rw [Nat.card_congr eq.toEquiv, hW] at h2
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  rw [h6] at h2
  omega


end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
